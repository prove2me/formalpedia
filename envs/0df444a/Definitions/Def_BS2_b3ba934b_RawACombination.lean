-- Prove2me | Definitions.Def_BS2_b3ba934b_RawACombination
-- name    : BS2_b3ba934b_RawACombination
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T05:57:11.483988+00:00
-- url     : https://prove2.me/theorems/d2a3124f-8ee4-40e8-8a87-c25c26f435f4
-- title:
--   Sensitivity separation: RawACombination (complete source module)
-- statement:
--   Complete Lean source module `RawACombination` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/RawACombination.lean; original SHA-256 d0ddb6ab1c4d4bdfffa23768bb8b2f65c7ca5b24fd83e493fd0e852b83b3b6e7; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The small-tolerance q2 maximum can be intersected with every valid ordinary
component bound, completing the exact numeric raw-A minimum. -/
import Definitions.Def_BS2_b3ba934b_OrdinaryZeroGraded
import Definitions.Def_BS2_b3ba934b_ActualQ2Bound

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

namespace ThreeBoundConditionalNumeric
open OAI.Paper320 ThreeBoundWitness ThreeBoundProfiles ThreeBoundPositive
open ThreeBoundConditional ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundGradedCandidates ThreeBoundHeadExpressions ThreeBoundActualQ2Bound
open scoped Classical
noncomputable section
variable {n : ℕ} {I : Type} [Fintype I]

theorem le_foldl_min (z first : ℕ) (xs : List ℕ) (hf : z ≤ first)
    (hxs : ∀ x ∈ xs, z ≤ x) : z ≤ xs.foldl Nat.min first := by
  induction xs generalizing first with
  | nil => exact hf
  | cons x xs ih =>
      apply ih (min first x) (le_min hf (hxs x (by simp)))
      intro y hy
      exact hxs y (by simp [hy])

theorem rawAExpr_small_bound (S : Stage (Fin n) I (Fin 10007))
    (hAdj : S.Adj=ThreeBoundOrdinarySelected.Adj)
    (hLabel : S.label=Sensitivity10007BoolCaps.label)
    (F : Fin n → (I → Bool) → Bool) (hF : Nested F) (recipe : Fin n → Entry)
    (i j : Fin n) (P : PairData S F i j)
    (hm : EntryMatch S F i j P (recipe i) (recipe j))
    (records : List (List ℕ)) (hpos : 0<(recipe j).tolerance) (hq2 : (recipe j).tolerance ≤ 2)
    (v : Profile n) (hv : Upper F v)
    (hfirst : ABound (parent S F) i j
      ((gradedAExpr n ordinaryCaps10007 records (recipe i) (recipe j)).eval v)) :
    ABound (parent S F) i j ((rawAExpr n ordinaryCaps10007 records (recipe i) (recipe j)).eval v) := by
  intro x hx
  simp only [rawAExpr,if_neg (by omega : (recipe j).tolerance≠0),
    if_neg (by omega : ¬3 ≤ (recipe j).tolerance)]
  by_cases hc : (recipe j).ordinary=true
  · rw [if_pos hc,Expr.eval_minimum]
    apply le_foldl_min _ _ _ (hfirst x hx)
    intro value hvalue
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hvalue
    obtain ⟨level,hlevel,hbody⟩ := List.mem_filterMap.mp he
    have hrange := mem_interval.mp hlevel
    split_ifs at hbody with ht
    · have heq := Option.some.inj hbody
      subst e
      exact ordinaryComponentAExpr_bound S hAdj hLabel F hF recipe i j P hm level
        (by omega) hrange.1 (by omega) ht hc v hv x hx
  · rw [if_neg hc]
    exact hfirst x hx

end
end ThreeBoundConditionalNumeric

#print axioms ThreeBoundConditionalNumeric.rawAExpr_small_bound


