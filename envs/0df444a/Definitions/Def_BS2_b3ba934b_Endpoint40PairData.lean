-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40PairData
-- name    : BS2_b3ba934b_Endpoint40PairData
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T06:33:12.826175+00:00
-- url     : https://prove2.me/theorems/9408922c-7d28-4a8a-a386-29be19ff25cf
-- title:
--   Sensitivity separation: Endpoint40PairData (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40PairData` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40PairData.lean; original SHA-256 2459776ded115834d5a758409baf55d95e02169cdcb1da8408a7160ceb920ffc; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- The exact first-endpoint recipes instantiate the semantic pair interface.
   Every threshold in the numeric certificate is the value of the actual
   finite level used by the Boolean construction. -/
import Definitions.Def_BS2_b3ba934b_HeadCostExpressions
import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 12000000
set_option linter.unusedSectionVars false

namespace ThreeBoundEndpoint40Pairs
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundNesting
open ThreeBoundGradedCandidates ThreeBoundHeadExpressions

theorem entry_guard_le_first : ∀ (p : Fin 4) (l : Fin 40),
    (Sensitivity10007Endpoint40.entry p l).guard ≤
      (Sensitivity10007Endpoint40.entry p l).t0 := by decide +kernel

theorem entry_guard_le_threshold (p : Fin 4) (l : Fin 40) (b : ℕ) :
    (Sensitivity10007Endpoint40.entry p l).guard ≤
      (Sensitivity10007Endpoint40.entry p l).threshold b := by
  have hm := (Sensitivity10007Endpoint40.recipe_ordered p).lower_mono l
  have hz := hm (Nat.zero_le b)
  change (Sensitivity10007Endpoint40.entry p l).threshold 0 ≤
    (Sensitivity10007Endpoint40.entry p l).threshold b at hz
  have he : (Sensitivity10007Endpoint40.entry p l).threshold 0 =
      (Sensitivity10007Endpoint40.entry p l).t0 := by
    simp [Sensitivity10007Endpoint40.Entry.threshold]
  rw [he] at hz
  exact (entry_guard_le_first p l).trans hz

variable {I : Type} [Fintype I]

noncomputable def pairData (p : Fin 4) (F : Fin 40 → (I → Bool) → Bool)
    (i j : Fin 40) (hij : i ≤ j) :
    PairData ((Sensitivity10007Endpoint40.recipe p).stage F) F i j where
  weak := (Sensitivity10007Endpoint40.entry p i).threshold
  strong := (Sensitivity10007Endpoint40.entry p j).threshold
  weakMono := (Sensitivity10007Endpoint40.recipe_ordered p).lower_mono i
  strongMono := (Sensitivity10007Endpoint40.recipe_ordered p).lower_mono j
  guards := (Sensitivity10007Endpoint40.recipe_ordered p).guard hij
  tolerances := (Sensitivity10007Endpoint40.recipe_ordered p).tolerance hij
  targets b hb := (Sensitivity10007Endpoint40.recipe_ordered p).lower_order i j hij b hb
  weakDef d u z := minmax_equal_targets F
    (fun l b => (Sensitivity10007Endpoint40.entry p l).threshold b) i d u z
  strongDef d u z := minmax_equal_targets F
    (fun l b => (Sensitivity10007Endpoint40.entry p l).threshold b) j d u z
  guardTarget b _ := entry_guard_le_threshold p j b
  weakGuardTarget b _ := entry_guard_le_threshold p i b

theorem numeric_threshold (p : Fin 4) (l : Fin 40) (b : ℕ) :
    ((Sensitivity10007Endpoint40.entry p l).threshold b).val =
      (ThreeBoundNumeric.Endpoint40.recipe p l).threshold b := by
  simp only [Sensitivity10007Endpoint40.Entry.threshold,
    ThreeBoundNumeric.Endpoint40.recipe, ThreeBoundNumeric.Entry.threshold]
  split_ifs <;> simp_all

theorem entryMatch (p : Fin 4) (F : Fin 40 → (I → Bool) → Bool)
    (i j : Fin 40) (hij : i ≤ j) :
    EntryMatch ((Sensitivity10007Endpoint40.recipe p).stage F) F i j
      (pairData p F i j hij)
      (ThreeBoundNumeric.Endpoint40.recipe p i)
      (ThreeBoundNumeric.Endpoint40.recipe p j) where
  weakGuard := rfl
  strongGuard := rfl
  weakTolerance := rfl
  strongTolerance := rfl
  weakThreshold := numeric_threshold p i
  strongThreshold := numeric_threshold p j

theorem pairData_strong (p : Fin 4) (F : Fin 40 → (I → Bool) → Bool)
    (i j : Fin 40) (hij : i ≤ j) (b : ℕ) :
    (pairData p F i j hij).strong b =
      (Sensitivity10007Endpoint40.entry p j).threshold b := rfl

theorem pairData_weak (p : Fin 4) (F : Fin 40 → (I → Bool) → Bool)
    (i j : Fin 40) (hij : i ≤ j) (b : ℕ) :
    (pairData p F i j hij).weak b =
      (Sensitivity10007Endpoint40.entry p i).threshold b := rfl

end ThreeBoundEndpoint40Pairs

#print axioms ThreeBoundEndpoint40Pairs.entry_guard_le_first
#print axioms ThreeBoundEndpoint40Pairs.pairData
#print axioms ThreeBoundEndpoint40Pairs.entryMatch


