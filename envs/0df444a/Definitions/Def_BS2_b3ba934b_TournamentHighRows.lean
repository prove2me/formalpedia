-- Prove2me | Definitions.Def_BS2_b3ba934b_TournamentHighRows
-- name    : BS2_b3ba934b_TournamentHighRows
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T03:59:05.115987+00:00
-- url     : https://prove2.me/theorems/0271762a-5d88-4b37-aa97-1a5c3f5e5ea1
-- title:
--   Sensitivity separation: TournamentHighRows (complete source module)
-- statement:
--   Complete Lean source module `TournamentHighRows` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/TournamentHighRows.lean; original SHA-256 33af55a94cc9e5226b2ef38c43cfae605b761c3b899fa90837313bdcbcfd382f; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/-
Semantic high-row bounds for the graded q2/q3 transfer.

The finite high set is connected to actual guard failure sets: every arc to
a high head selects a guard-true child and therefore consumes a failure of
its tail. The tournament edge double count is proved here, not assumed.
-/
import Definitions.Def_BS2_b3ba934b_MinmaxLocal
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace TournamentHighRows
open scoped Classical BigOperators

variable {V X : Type}

/-- The two tournament axioms used in the counting proof. -/
structure IsTournament (R : V → V → Prop) : Prop where
  loopless : ∀ v, ¬ R v v
  orient : ∀ v w, v ≠ w → (R v w ↔ ¬ R w v)

noncomputable def outNeighbors (R : V → V → Prop) (S : Finset V) (v : V) : Finset V := by
  classical
  exact S.filter (R v)

noncomputable def arcs (R : V → V → Prop) (S : Finset V) : Finset (V × V) := by
  classical
  exact (S.product S).filter fun p => R p.1 p.2

theorem mem_arcs (R : V → V → Prop) (S : Finset V) (v w : V) :
    (v,w) ∈ arcs R S ↔ v ∈ S ∧ w ∈ S ∧ R v w := by
  classical
  constructor
  · intro h
    have hf := Finset.mem_filter.mp h
    have hp := Finset.mem_product.mp hf.1
    exact ⟨hp.1, hp.2, hf.2⟩
  · rintro ⟨hv,hw,hR⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv,hw⟩,hR⟩

theorem reverse_arcs_card (R : V → V → Prop) (S : Finset V) :
    (arcs (fun v w => R w v) S).card = (arcs R S).card := by
  classical
  refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
  · intro p hp
    rcases p with ⟨v,w⟩
    rcases (mem_arcs _ S v w).1 hp with ⟨hv,hw,hR⟩
    exact (mem_arcs R S w v).2 ⟨hw,hv,hR⟩
  · intro p hp q hq heq
    exact Prod.swap_injective heq
  · intro p hp
    rcases p with ⟨v,w⟩
    rcases (mem_arcs R S v w).1 hp with ⟨hv,hw,hR⟩
    exact ⟨(w,v), (mem_arcs _ S w v).2 ⟨hw,hv,hR⟩, rfl⟩

theorem arcs_disjoint_reverse (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) : Disjoint (arcs R S) (arcs (fun v w => R w v) S) := by
  classical
  apply Finset.disjoint_left.mpr
  rintro ⟨v,w⟩ hp hq
  have hvw := ((mem_arcs R S v w).1 hp).2.2
  have hwv := ((mem_arcs _ S v w).1 hq).2.2
  have hne : v ≠ w := by
    intro he
    subst w
    exact hR.loopless v hvw
  exact ((hR.orient v w hne).1 hvw) hwv

theorem arcs_union_reverse (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) :
    arcs R S ∪ arcs (fun v w => R w v) S = S.offDiag := by
  classical
  ext p
  rcases p with ⟨v,w⟩
  simp only [Finset.mem_union, mem_arcs, Finset.mem_offDiag]
  constructor
  · rintro (⟨hv,hw,hvw⟩ | ⟨hv,hw,hwv⟩)
    · refine ⟨hv,hw,?_⟩
      intro he
      subst w
      exact hR.loopless v hvw
    · refine ⟨hv,hw,?_⟩
      intro he
      subst w
      exact hR.loopless v hwv
  · rintro ⟨hv,hw,hne⟩
    by_cases hvw : R v w
    · exact Or.inl ⟨hv,hw,hvw⟩
    · exact Or.inr ⟨hv,hw,(hR.orient w v hne.symm).2 hvw⟩

/-- Every unordered pair contributes exactly one directed edge. -/
theorem twice_arcs_card (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) : 2 * (arcs R S).card = S.card * S.card - S.card := by
  classical
  have h := Finset.card_union_of_disjoint (arcs_disjoint_reverse R hR S)
  rw [arcs_union_reverse R hR S, reverse_arcs_card R S, Finset.offDiag_card] at h
  omega

theorem arcs_eq_union_rows (R : V → V → Prop) (S : Finset V) :
    arcs R S = S.biUnion (fun v => ({v} : Finset V).product (outNeighbors R S v)) := by
  classical
  ext p
  rcases p with ⟨v,w⟩
  constructor
  · intro hp
    rcases (mem_arcs R S v w).1 hp with ⟨hv,hw,hR⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨v,hv,Finset.mem_product.mpr ⟨Finset.mem_singleton_self v,?_⟩⟩
    exact Finset.mem_filter.mpr ⟨hw,hR⟩
  · intro hp
    obtain ⟨u,hu,hp⟩ := Finset.mem_biUnion.mp hp
    rcases Finset.mem_product.mp hp with ⟨hvu,hw⟩
    have heq : v = u := Finset.mem_singleton.mp hvu
    subst u
    rcases Finset.mem_filter.mp hw with ⟨hw,hR⟩
    exact (mem_arcs R S v w).2 ⟨hu,hw,hR⟩

theorem arcs_card_le_sum_out (R : V → V → Prop) (S : Finset V) :
    (arcs R S).card ≤ ∑ v ∈ S, (outNeighbors R S v).card := by
  classical
  rw [arcs_eq_union_rows R S]
  calc
    (S.biUnion (fun v => ({v} : Finset V).product (outNeighbors R S v))).card
        ≤ ∑ v ∈ S, (({v} : Finset V).product (outNeighbors R S v)).card :=
      Finset.card_biUnion_le
    _ = ∑ v ∈ S, (outNeighbors R S v).card := by simp

/-- Necessary budget inequality for every finite tournament and every budget vector. -/
theorem budget_sum_bound (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) (budget : V → ℕ)
    (hbudget : ∀ v ∈ S, (outNeighbors R S v).card ≤ budget v) :
    S.card * (S.card - 1) ≤ 2 * ∑ v ∈ S, budget v := by
  have hsum : (arcs R S).card ≤ ∑ v ∈ S, budget v :=
    (arcs_card_le_sum_out R S).trans (Finset.sum_le_sum hbudget)
  have htwice := Nat.mul_le_mul_left 2 hsum
  rw [twice_arcs_card R hR S] at htwice
  simpa only [Nat.mul_sub_left_distrib, Nat.mul_one] using htwice

theorem card_le_of_outdegree_le (R : V → V → Prop) (hR : IsTournament R)
    (S : Finset V) (q : ℕ)
    (hbudget : ∀ v ∈ S, (outNeighbors R S v).card ≤ q) : S.card ≤ 2*q+1 := by
  have hb := budget_sum_bound R hR S (fun _ => q) hbudget
  simp only [Finset.sum_const, nsmul_eq_mul] at hb
  by_cases hzero : S.card = 0
  · omega
  · have hpos : 0 < S.card := Nat.pos_of_ne_zero hzero
    have hsub : S.card - 1 + 1 = S.card := Nat.sub_add_cancel hpos
    by_contra hn
    have hlarge : 2*q+2 ≤ S.card := by omega
    have hmul := Nat.mul_le_mul_left S.card hlarge
    nlinarith

section GuardSemantics
variable [Fintype V]

/-- The actual failures of a selected-child guard at a row. -/
noncomputable def guardFailures (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter fun w => R v w ∧ P (children w (ell v w))

/-- Every edge into a high head consumes an actual failed guard. -/
theorem out_high_subset_failures (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X) (H : Finset V)
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c)) (v : V) :
    outNeighbors R H v ⊆ guardFailures R ell P children v := by
  classical
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨hwH,hvw⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hvw, hhigh w hwH (ell v w)⟩

/-- The finite high-row tournament bound, derived from actual selected guards. -/
theorem high_rows_card_le (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (H : Finset V) (q : ℕ)
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c))
    (hbudget : ∀ v ∈ H, (guardFailures R ell P children v).card ≤ q) :
    H.card ≤ 2*q+1 := by
  apply card_le_of_outdegree_le R hR H q
  intro v hv
  exact (Finset.card_le_card (out_high_subset_failures R ell P children H hhigh v)).trans
    (hbudget v hv)

/-- This proves every subset budget inequality used by the typed-orientation
    generator's necessary sorted-prefix check. -/
theorem every_high_subset_budget_bound (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (H : Finset V) (budget : V → ℕ)
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c))
    (hbudget : ∀ v ∈ H, (guardFailures R ell P children v).card ≤ budget v)
    (S : Finset V) (hSH : S ⊆ H) :
    S.card * (S.card - 1) ≤ 2 * ∑ v ∈ S, budget v := by
  apply budget_sum_bound R hR S budget
  intro v hv
  have hs : ∀ w ∈ S, ∀ c : Bool, P (children w c) :=
    fun w hw c => hhigh w (hSH hw) c
  exact (Finset.card_le_card (out_high_subset_failures R ell P children S hs v)).trans
    (hbudget v (hSH hv))

/-- q2 high types have maximum failure budget three, so there are at most seven. -/
theorem q2_high_rows_le_seven (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (H : Finset V)
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c))
    (hbudget : ∀ v ∈ H, (guardFailures R ell P children v).card ≤ 3) :
    H.card ≤ 7 := by
  simpa using high_rows_card_le R hR ell P children H 3 hhigh hbudget

/-- q3 high types have maximum failure budget four, so there are at most nine. -/
theorem q3_high_rows_le_nine (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (H : Finset V)
    (hhigh : ∀ w ∈ H, ∀ c : Bool, P (children w c))
    (hbudget : ∀ v ∈ H, (guardFailures R ell P children v).card ≤ 4) :
    H.card ≤ 9 := by
  simpa using high_rows_card_le R hR ell P children H 4 hhigh hbudget

/-- The positive-target prefix through tier b has at most 2b+1 high rows. -/
theorem positive_prefix_card_le (R : V → V → Prop) (hR : IsTournament R)
    (ell : V → V → Bool) (P : X → Prop) (children : V → Bool → X)
    (pref : Finset V) (b : ℕ)
    (hhigh : ∀ w ∈ pref, ∀ c : Bool, P (children w c))
    (hbudget : ∀ v ∈ pref, (guardFailures R ell P children v).card ≤ b) :
    pref.card ≤ 2*b+1 :=
  high_rows_card_le R hR ell P children pref b hhigh hbudget

end GuardSemantics
end TournamentHighRows

#print axioms TournamentHighRows.twice_arcs_card
#print axioms TournamentHighRows.high_rows_card_le
#print axioms TournamentHighRows.every_high_subset_budget_bound
#print axioms TournamentHighRows.q2_high_rows_le_seven
#print axioms TournamentHighRows.q3_high_rows_le_nine
#print axioms TournamentHighRows.positive_prefix_card_le


