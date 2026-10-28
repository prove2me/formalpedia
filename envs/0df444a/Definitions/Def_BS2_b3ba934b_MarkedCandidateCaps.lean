-- Prove2me | Definitions.Def_BS2_b3ba934b_MarkedCandidateCaps
-- name    : BS2_b3ba934b_MarkedCandidateCaps
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:24:50.693955+00:00
-- url     : https://prove2.me/theorems/166fe02a-05ad-48d7-92e3-94554f04f9fd
-- title:
--   Sensitivity separation: MarkedCandidateCaps (complete source module)
-- statement:
--   Complete Lean source module `MarkedCandidateCaps` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/MarkedCandidateCaps.lean; original SHA-256 70f36cf46863ef614a9073ec6c026de5ae5410330d52f60a12e96f629777f587; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/-
Unrestricted marked prefix caps and the outside-first marker choice used in
the exact q2 recurrence. These theorems refer to actual selected-child guards.
-/
import Definitions.Def_BS2_b3ba934b_ResidualCaps

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace MarkedCandidateCaps
open scoped Classical BigOperators
open Finset TournamentHighRows CandidateCoherence GuardAugmentation ResidualCaps
noncomputable section

variable {V X : Type} [Fintype V] [DecidableEq V]

theorem markedGood_of_actual_guards (R : V → V → Prop) (ell : V → V → Bool)
    (guard : X → Prop) (children : V → Bool → X) (A M : Finset V)
    (hdis : Disjoint A M) (q : ℕ) (color : V → Bool)
    (hpartner : ∀ w ∈ A, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ M, ∀ c : Bool, guard (children w c))
    (hA : ∀ v ∈ A, (guardFailures R ell guard children v).card ≤ q)
    (hM : ∀ v ∈ M, (guardFailures R ell guard children v).card ≤ q+1) :
    ResidualCaps.MarkedGood R ell A M q (M.card*(q+1)) color := by
  have hcharge (v : V) :=
    charges_card_le_actual_failures R ell guard children A M hdis color hpartner hhigh v
  refine ⟨?_,?_,?_⟩
  · intro v hv
    exact (hcharge v).trans (hA v hv)
  · intro v hv
    rw [Nat.add_comm]
    exact (hcharge v).trans (hM v hv)
  · calc
      (∑ v ∈ M, (mismatch R ell A color v).card) ≤ ∑ v ∈ M, (q+1) := by
        apply Finset.sum_le_sum
        intro v hv
        exact (Finset.card_le_card
          (mismatch_subset_failures R ell guard children A color hpartner v)).trans (hM v hv)
      _ = M.card*(q+1) := by simp

/-- Markers that already belong to the target prefix are removed before the
    marked exclusion is applied, and counted back exactly once. -/
theorem actual_marked_prefix_cap (R : V → V → Prop) (ell : V → V → Bool)
    (guard : X → Prop) (children : V → Bool → X) (T M : Finset V)
    (q m a : ℕ) (hMcard : M.card = m)
    (hcap : MarkedCardBound R ell q m (m*(q+1)) a) (color : V → Bool)
    (hpartner : ∀ w ∈ T, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ M, ∀ c : Bool, guard (children w c))
    (hT : ∀ v ∈ T, (guardFailures R ell guard children v).card ≤ q)
    (hM : ∀ v ∈ M, (guardFailures R ell guard children v).card ≤ q+1) :
    T.card ≤ a-1 + (T ∩ M).card := by
  let A := T \ M
  have hAT : A ⊆ T := Finset.sdiff_subset
  have hdis : Disjoint A M := Finset.sdiff_disjoint
  have hg := markedGood_of_actual_guards R ell guard children A M hdis q color
    (fun w hw => hpartner w (hAT hw)) hhigh (fun v hv => hT v (hAT hv)) hM
  rw [hMcard] at hg
  have hc := hcap A M color hdis hMcard hg
  have hsum := Finset.card_sdiff_add_card_inter T M
  change A.card + (T ∩ M).card = T.card at hsum
  omega

/-- Select eligible markers outside T first. This proves the exact correction
    max(0,m-outside) used by the numerical prefix-cap formula. -/
theorem exists_markers_outside_first (T E : Finset V) (m : ℕ) (hm : m ≤ E.card) :
    ∃ M : Finset V, M ⊆ E ∧ M.card = m ∧ (T ∩ M).card ≤ m - (E \ T).card := by
  by_cases hout : m ≤ (E \ T).card
  · obtain ⟨M,hMO,hMc⟩ := Finset.exists_subset_card_eq hout
    refine ⟨M,hMO.trans Finset.sdiff_subset,hMc,?_⟩
    have hdis : Disjoint T M := by
      apply Finset.disjoint_left.mpr
      intro v hvT hvM
      exact (Finset.mem_sdiff.mp (hMO hvM)).2 hvT
    have hempty : T ∩ M = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdis
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  · have houtle : (E \ T).card ≤ m := by omega
    have hsplit := Finset.card_sdiff_add_card_inter E T
    have hneed : m - (E \ T).card ≤ (E ∩ T).card := by omega
    obtain ⟨J,hJI,hJc⟩ := Finset.exists_subset_card_eq hneed
    let O := E \ T
    let M := O ∪ J
    have hME : M ⊆ E := by
      apply Finset.union_subset
      · exact Finset.sdiff_subset
      · exact hJI.trans Finset.inter_subset_left
    have hdis : Disjoint O J := by
      apply Finset.disjoint_left.mpr
      intro v hvO hvJ
      exact (Finset.mem_sdiff.mp hvO).2 (Finset.mem_inter.mp (hJI hvJ)).2
    have hMc : M.card = m := by
      have hc : M.card = O.card + J.card := Finset.card_union_of_disjoint hdis
      dsimp [O] at hc
      omega
    have hsub : T ∩ M ⊆ J := by
      intro v hv
      obtain ⟨hvT,hvM⟩ := Finset.mem_inter.mp hv
      rcases Finset.mem_union.mp hvM with hvO | hvJ
      · exact False.elim ((Finset.mem_sdiff.mp hvO).2 hvT)
      · exact hvJ
    refine ⟨M,hME,hMc,?_⟩
    exact (Finset.card_le_card hsub).trans (le_of_eq hJc)

/-- The configured one-marker and two-marker correction is justified for every graded
    target prefix, including positive high rows at higher tiers. -/
theorem actual_marked_outside_first_cap (R : V → V → Prop) (ell : V → V → Bool)
    (guard : X → Prop) (children : V → Bool → X) (T E : Finset V)
    (q m a : ℕ) (hm : m ≤ E.card)
    (hcap : MarkedCardBound R ell q m (m*(q+1)) a) (color : V → Bool)
    (hpartner : ∀ w ∈ T, ∀ c : Bool, c ≠ color w → guard (children w c))
    (hhigh : ∀ w ∈ E, ∀ c : Bool, guard (children w c))
    (hT : ∀ v ∈ T, (guardFailures R ell guard children v).card ≤ q)
    (hE : ∀ v ∈ E, (guardFailures R ell guard children v).card ≤ q+1) :
    T.card ≤ a-1 + (m - (E \ T).card) := by
  obtain ⟨M,hME,hMc,hint⟩ := exists_markers_outside_first T E m hm
  have h := actual_marked_prefix_cap R ell guard children T M q m a hMc hcap color
    hpartner (fun w hw => hhigh w (hME hw)) hT (fun v hv => hE v (hME hv))
  exact h.trans (Nat.add_le_add_left hint (a-1))

end
end MarkedCandidateCaps

#print axioms MarkedCandidateCaps.markedGood_of_actual_guards
#print axioms MarkedCandidateCaps.actual_marked_prefix_cap
#print axioms MarkedCandidateCaps.exists_markers_outside_first
#print axioms MarkedCandidateCaps.actual_marked_outside_first_cap


