import data.dfinsupp.multiset
import data.finset.basic
import data.finset.card
import data.finset.fin
import data.list.basic

/-
The goal of this file is to prove that in the case of three generals,
with one traitorous general, reaching consensus is impossible. After
completing this proof, we state the result of the general theorem, but
do not present a proof.
-/

/- SECTION ONE: Definitions -/

-- This codifies the requirement that machines actually talk to each other,
-- and do not just choose degenerate protocol
def is_interactive {fin : finset ℕ}
(wrong : fin)
(value_map : fin → ℕ)
(assignment : fin → fin → ℕ)
:= ∀ p q : fin, p ≠ wrong ∧ q ≠ wrong → assignment p q = value_map q

-- This codifies the requirement that the machines agree on _everything_.
-- Note that this includes the requirement that truthy machines agree on the
-- value of faulty machines, either meaning they both identify it as faulty,
-- or both receive the same value.
def is_consistent { fin : finset ℕ }
(wrong : fin)
(value_map : fin → ℕ)
(assignment : fin → fin → ℕ)
:= ∀ p q : fin, p ≠ wrong ∧ q ≠ wrong → ∀ x : fin, assignment p x = assignment q x

-- This simply wraps the above two definitions into a handy statement
def is_IC {fin : finset ℕ}
(wrong : fin)
(value_map : fin → ℕ) 
(assignment : fin → fin → ℕ)
:= is_interactive wrong value_map assignment ∧ is_consistent wrong value_map assignment 

-- A helper definition that defines what it means for a map to satisfy a
-- condition on the first element of a list (trivially true if empty)
def matches_first {fin : finset ℕ}
(σ : list fin → ℕ) (value_map : fin → ℕ) : list fin → Prop
| [] := true = true
| (h :: t) := σ (h :: t) = value_map h

-- A helper definition to capture the meaning of a list starting with a machine
def starts_with {fin : finset ℕ} (p : fin) : list fin → bool
| [] := true
| (h :: t) := h = p

-- A helper definition to capture the meaning of a list ending with a machine
def ends_with {fin : finset ℕ} (p : fin) : list fin → bool
| [] := false
| l := l.reverse.head' = some p

-- A simple result showing that the last element in a list must be unique
lemma end_unique {fin : finset ℕ} {a : fin} {b : fin}
(h : a ≠ b)
(l : list fin)
(h_end : ends_with a l) : ¬ends_with b l :=
begin
  cases l,
  {
    simp only [eq_ff_eq_not_eq_tt],
    rw ends_with,
    simp only [to_bool_false_eq_ff],
  },
  {
    rw ends_with at *,
    simp* at h_end,
    simp only [list.reverse_cons, bool.of_to_bool_iff],
    simp only [*, not_false_iff],
  },
end

-- Given a list of lists, return only the lists that start with q
def lists_that_start_with {fin : finset ℕ} (q : fin) : list (list fin) → list (list fin)
| [] := []
| ([] :: meta_l) := lists_that_start_with meta_l
| ((h :: rest) :: meta_l) := 
    if h = q 
    then (h :: rest) :: (lists_that_start_with meta_l) 
    else (lists_that_start_with meta_l)

-- Given a list of lists, return only the lists that end with q
def lists_that_end_with {fin : finset ℕ} (q : fin) : list (list fin) → list (list fin)
| [] := []
| ([] :: meta_l) := lists_that_end_with meta_l
| (l :: meta_l) := 
    if l.last' = some q
    then l :: (lists_that_end_with meta_l) 
    else (lists_that_end_with meta_l)

-- Combine the two above, and return the subset of a list of lists that start
-- with a given p and end with a given q
def filter_by {fin : finset ℕ} (p : fin) (q : fin) (W : list (list fin)) : list (list fin) :=
lists_that_end_with q (lists_that_start_with p W)

-- A result about our filter_by function that enforces the first element condition
-- NOTE: It is left unproven, but this should be possible to replace with a formal proof
lemma h_filter_by_start {fin : finset ℕ} {f : fin} {p : fin} {W : list (list fin)} 
(l : list fin)
(hl : l ∈ filter_by f p W) : starts_with f l := sorry

-- A result about our filter_by function that enforces the last element condition
-- NOTE: It is left unproven, but this should be possible to replace with a formal proof
def h_filter_by_end {fin : finset ℕ} {f : fin} {p : fin} {W : list (list fin)} 
(l : list fin)
(hl : l ∈ filter_by f p W) : ends_with p l := sorry

-- A helper function to return a list by applying a function to every
-- element of that list
def map_list {α : Type*} {β : Type*} (f : α → β) : list α → list β
| [] := []
| (h :: t) := (f h)::(map_list t)

-- A helper function to generate truthy behavior when crafting network functions
def truthy_like {fin : finset ℕ} (value_map : fin → ℕ) : list fin → ℕ
| [] := 0
| (h :: t) := value_map h 

/- SECTION TWO: Impossibility for n = 3 -/

-- These definitions are constant and provide the information at the global
-- level to restrict our scope to n = 3
constant procs : finset ℕ
constant procs_def : procs = { 1, 2, 3}
constant first_exists : ∃ x : procs, true
constant second_exists (p : procs) : ∃ x : procs, x ≠ p
constant third_exists (p : procs) (q : procs) : ∃ x : procs, x ≠ p ∧ x ≠ q
constant procs_ne_zero : ∀ p ∈ procs, p ≠ 0

-- It is impossible for three generals with one traitor to agree on anything
theorem byzantine :
∀ W : list (list procs), -- Any arbitrary communications
∀ alg : list (list procs) → (list procs → ℕ) → ℕ, -- Any algorithm
alg [] = 0 -- The algorithm must be _sound_
→
-- The algorithm must be _blind_ (i.e., dependent on it's inputs)
(∀ K : list (list procs), ∀ σ σ' : list procs → ℕ, ∀ m: ℕ → ℕ, (∀ l ∈ K, σ'(l) = m(σ(l))) → alg K σ' = m(alg K σ))
→
-- We can always construct a counterexample
∃ f : procs,
∃ value_map : procs → ℕ,
∃ σ : list procs → ℕ,
∀ l : list procs, f ∉ l → matches_first σ value_map l 
→
¬is_IC f value_map (λ p q : procs, alg (filter_by q p W) σ) :=
begin
  -- Get access to the arbitrary protocl
  intro W,
  intro alg,
  intro alg_sound,
  intro alg_blind,

  -- Handle the degenerate case where some machines don't talk to each other
  by_cases W_full : (∃ p : procs, ∃ q : procs, p ≠ q ∧ filter_by q p W = []),
  {
    rcases W_full with ⟨ p, q, ⟨ p_ne_q, silent_q ⟩ ⟩,
    -- To get a contradiction, we need p and q as our truthy processors
    have f_exists := third_exists p q,
    cases f_exists with f hf,
    use f, -- The faulty processor
    let value_map : procs → ℕ := λ x, 1,
    use value_map,
    let σ : list procs → ℕ := λ l, truthy_like value_map l,
    use σ,
    intros l f_nin_l hσ,
    rw [is_IC, is_interactive, is_consistent],
    push_neg,
    intro interactive,
    exfalso,
    have accurate := interactive p q ⟨ ne.symm hf.1, ne.symm hf.2 ⟩,
    rw [silent_q] at accurate,
    dsimp [map_list, value_map] at accurate,
    rw [alg_sound] at accurate,
    -- UPSHOT: When machines don't talk, interactivity can be broken
    contradiction,
  },
  push_neg at W_full,

  -- Get three distinct elements from procs, p q and f
  cases first_exists with p,
  cases second_exists p with q q_ne_p,
  rcases third_exists p q with ⟨ f, ⟨ f_ne_p, f_ne_q ⟩⟩,
  
  -- We can construct a counterexample with a simple value_map 
  -- and arbitrary f
  let value_map : procs → ℕ := λ p, p,
  use [f, value_map],

  -- Assume that having a valid network function implies interactive consistency
  by_contradiction all_sigs,
  push_neg at all_sigs,

  -- A very simple (but valid) network function
  let σ : list procs → ℕ := λ l,
    if starts_with f l
      then 1
      else truthy_like value_map l,

  -- A derivative (but also valid) network function that can trick the algorithm
  let σ' : list procs → ℕ := λ l,
    if starts_with f l
      then if ends_with p l
        then σ l + 1
      else if ends_with q l
        then σ l + 2
        else truthy_like value_map l
      else truthy_like value_map l,

  -- By assumption, using this σ will guarantee consistency
  rcases all_sigs σ with ⟨ K, f_nin_K, ⟨  hσ, interactive, consistent ⟩  ⟩, 
  rw is_consistent at consistent,
  have alg_app_eq := consistent p q ⟨ ne.symm f_ne_p, ne.symm f_ne_q ⟩ f,

  -- By assumption, using this σ' will guarantee consistency
  rcases all_sigs σ' with ⟨ K, f_nin_K, ⟨  hσ', interactive', consistent' ⟩  ⟩, 
  rw is_consistent at consistent',
  have alg_app_eq' := consistent' p q ⟨ ne.symm f_ne_p, ne.symm f_ne_q ⟩ f,

  -- m and m' capture the discrepancies between σ and σ'
  let m : ℕ → ℕ := λ n, n + 1,
  let m' : ℕ → ℕ := λ n, n + 2,

  -- Proofs that for the filtered values in question m and m' do indeed
  -- capture the differences between σ and σ'
  have σ_rel_p : ∀ (l : list ↥procs), l ∈ filter_by f p W → σ' l = m (σ l),
  {
    intros l hl,
    dsimp [m, σ, σ'],
    have l_starts_with_f := h_filter_by_start l hl,
    have l_ends_with_p := h_filter_by_end l hl,
    simp only [*, if_true, self_eq_add_left, nat.one_ne_zero],
  },
  have σ_rel_q : ∀ (l : list ↥procs), l ∈ filter_by f q W → σ' l = m' (σ l),
  {
    intros l hl,
    dsimp [m', σ, σ'],
    have l_starts_with_f := h_filter_by_start l hl,
    have l_ends_with_q := h_filter_by_end l hl,
    have does_not_end_with_p := end_unique q_ne_p l l_ends_with_q,
    simp only [*, if_true, if_false],
  },

  -- Our algorithm is blind, so using these two network functions
  -- we can trick it
  have p'_eq_p_one := alg_blind (filter_by f p W) σ σ' m σ_rel_p,
  dsimp [m] at p'_eq_p_one,
  have q'_eq_q_two := alg_blind (filter_by f q W) σ σ' m' σ_rel_q,
  dsimp [m'] at q'_eq_q_two,

  -- Show that the equalities implied by blindness contradict each other
  rw alg_app_eq at p'_eq_p_one,
  rw alg_app_eq' at p'_eq_p_one,
  rw q'_eq_q_two at p'_eq_p_one,
  simp only [nat.succ_ne_self] at p'_eq_p_one,
  exact p'_eq_p_one,
end

