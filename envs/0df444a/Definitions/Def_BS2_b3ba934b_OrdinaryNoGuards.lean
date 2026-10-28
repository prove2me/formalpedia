-- Prove2me | Definitions.Def_BS2_b3ba934b_OrdinaryNoGuards
-- name    : BS2_b3ba934b_OrdinaryNoGuards
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T04:07:53.82033+00:00
-- url     : https://prove2.me/theorems/5fcd03c9-acc8-471f-affd-ffd302c8a23f
-- title:
--   Sensitivity separation: OrdinaryNoGuards (complete source module)
-- statement:
--   Complete Lean source module `OrdinaryNoGuards` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/OrdinaryNoGuards.lean; original SHA-256 4b5fb81838caa2eadb22fbd94a31bb0cbfe787e170cde84b9124e4bff30013ec; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- A direct specialization of the accepted ordinary proof when the actual
strong guard candidates are empty. This permits a graded weak threshold at 1. -/
import Definitions.Def_BS2_b3ba934b_ArchivedOrdinaryStrict
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ThreeBoundOrdinaryArchive
open OAI.Paper320 Sensitivity2075 SensitivityQ
open scoped Classical BigOperators
noncomputable section
namespace ZT
variable {n k : ℕ} {I : Type} [Fintype I]

theorem zero_tolerance_of_no_guards (T : Tournament k) (label : Fin k → Fin k → Fin 2)
    (F : Fin n → (I → Bool) → Bool) (hF : NestedFamily F)
    (ta tb ga gb : Fin n) (ht : ta ≤ tb) (hg : gb ≤ ga) (hga : ga ≤ ta)
    (a b : ℕ)
    (ha : PBound F gb ta tb a) (hb : ABound F gb tb b)
    (hordinary : DefectBound T label 0 23)
    (hsource : SensitivitySourceZero.SourceBound T label 21)
    (x : ((Fin k × Fin 2) × I) → Bool)
    (hx : tolerantFamily T label F ta ga 0 x = false)
    (hG0 : tolerantGuards T label F tb gb 0 x=∅) :
    (flipsTo (tolerantFamily T label F tb gb 0) true x).card ≤ max (22*b) (a+19*b) := by
  let TC := tolerantTargets T label F tb gb 0 x
  let P := positiveTargets T label F tb gb 0 x (by decide)
  let G := tolerantGuards T label F tb gb 0 x
  let δ := (crossedTargetHeads T label F tb gb 0 x).card
  have hgt : gb ≤ tb := hg.trans (hga.trans ht)
  have hG : G=∅ := hG0
  have hgcard : G.card=0 := by rw [hG]; rfl
  have hu : P.card ≤ 1 := by simpa using positiveTargets_card T label F hF tb gb hgt 0 x (by decide)
  have htcard : TC.card ≤ 22 := by
    have hh := targets_card_of_exclusion T label F hF tb gb hgt 0 23 hordinary x
    change TC.card < 23 at hh
    omega
  have hδbudget := crossedTargetHeads_budget T label F hF tb gb hgt 0 x
  change δ+((P.card*G.card+P.card.choose 2)-0*P.card) ≤ G.card*(0+1)-G.card.choose 2 at hδbudget
  have hδ : δ=0 := by rw [hgcard] at hδbudget; norm_num at hδbudget; omega
  have hsrc : P.card=1 → TC.card-1 ≤ 19 := by
    intro hpc
    have hne : (P ∪ G).Nonempty := by
      rw [hG,Finset.union_empty]
      exact Finset.card_pos.mp (by omega)
    have hh := remaining_card_source_zero T label F hF tb gb hgt 21 hsource x hne
    have hpart := remaining_targets_card T label F tb gb 0 x
    change (remainingOrdinaryTargets T label F tb gb 0 x).card+δ+P.card=TC.card at hpart
    omega
  have hoff : tolerantFamily T label F tb gb 0 x=false := by
    cases hh : tolerantFamily T label F tb gb 0 x with
    | false => rfl
    | true =>
        have hh' := family_nested T label F hF ht hg (le_refl 0) x hh
        rw [hx] at hh'
        contradiction
  have hrepairs : guardRepairs T label F tb gb 0 x=∅ := by
    simp only [guardRepairs,hG0,Finset.biUnion_empty]
  have hcover := up_subset_repairs T label F tb gb 0 x hoff
  rw [hrepairs,Finset.union_empty] at hcover
  have hraw := (Finset.card_le_card hcover).trans
    (targetRepairs_card T label F hF ta tb ga gb ht hg 0 0 le_rfl a b ha hb x hx)
  exact zero_strict_candidate_cases _ TC.card P.card a b hu htcard hsrc hraw

end ZT
end
end ThreeBoundOrdinaryArchive
#print axioms ThreeBoundOrdinaryArchive.ZT.zero_tolerance_of_no_guards


