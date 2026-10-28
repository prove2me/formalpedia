-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint16PairData
-- name    : BS2_b3ba934b_Endpoint16PairData
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T20:41:50.454227+00:00
-- url     : https://prove2.me/theorems/0682a34e-84b4-41ee-aded-feff790a599c
-- title:
--   Sensitivity separation: Endpoint16PairData (complete source module)
-- statement:
--   Complete Lean source module `Endpoint16PairData` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16PairData.lean; original SHA-256 ebecd06a4f007e6da70dde1cc2e2330e22d6ef82afc1da67cf140e268846d2cb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Concrete second-endpoint min/max recipes and their numeric matching. -/
import Definitions.Def_BS2_b3ba934b_MinmaxEntryMatch
import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
set_option linter.unusedSectionVars false

namespace ThreeBoundEndpoint16Pairs
open ThreeBoundWitness ThreeBoundProfiles ThreeBoundNesting
open ThreeBoundMinmaxTransfer ThreeBoundMinmaxNumeric

theorem entry_guard_le_threshold (p : Fin 4) (l : Fin 16) (d : ℕ) :
    (Sensitivity10007Endpoint16.entry p l).guard ≤ (Sensitivity10007Endpoint16.entry p l).threshold d := by
  have hh := (Sensitivity10007Endpoint16.recipe_ordered p).lower_mono l (Nat.zero_le d)
  have hz : (Sensitivity10007Endpoint16.entry p l).threshold 0=(Sensitivity10007Endpoint16.entry p l).t0 := by
    simp [Sensitivity10007Endpoint16.Entry.threshold]
  change (Sensitivity10007Endpoint16.entry p l).threshold 0 ≤
    (Sensitivity10007Endpoint16.entry p l).threshold d at hh
  rw [hz] at hh
  exact (Sensitivity10007Endpoint16.entry_guard_order p l).1.trans hh

theorem entry_lower_upper (p : Fin 4) (l : Fin 16) (d : ℕ)
    (hd : d ≤ (Sensitivity10007Endpoint16.entry p l).tolerance) :
    (Sensitivity10007Endpoint16.entry p l).threshold d ≤ (Sensitivity10007Endpoint16.entry p l).upper d := by
  have hd9 : d<9 := by have hh := (Sensitivity10007Endpoint16.entry_internal_order p l).2.2.2.2; omega
  exact (Sensitivity10007Endpoint16.entry_guard_order p l).2 ⟨d,hd9⟩ hd

variable {I : Type} [Fintype I]

noncomputable def pairData (p : Fin 4) (F : Fin 16 → (I → Bool) → Bool)
    (i j : Fin 16) (hij : i ≤ j) :
    PairData ((Sensitivity10007Endpoint16.recipe p).stage F) F i j where
  weakLower := (Sensitivity10007Endpoint16.entry p i).threshold
  weakUpper := (Sensitivity10007Endpoint16.entry p i).upper
  strongLower := (Sensitivity10007Endpoint16.entry p j).threshold
  strongUpper := (Sensitivity10007Endpoint16.entry p j).upper
  weakLowerMono := (Sensitivity10007Endpoint16.recipe_ordered p).lower_mono i
  weakUpperMono := (Sensitivity10007Endpoint16.recipe_ordered p).upper_mono i
  strongLowerMono := (Sensitivity10007Endpoint16.recipe_ordered p).lower_mono j
  strongUpperMono := (Sensitivity10007Endpoint16.recipe_ordered p).upper_mono j
  weakLowerUpper := entry_lower_upper p i
  strongLowerUpper := entry_lower_upper p j
  guards := (Sensitivity10007Endpoint16.recipe_ordered p).guard hij
  tolerances := (Sensitivity10007Endpoint16.recipe_ordered p).tolerance hij
  lowerOrder := (Sensitivity10007Endpoint16.recipe_ordered p).lower_order i j hij
  upperOrder := (Sensitivity10007Endpoint16.recipe_ordered p).upper_order i j hij
  weakDef _ _ _ := rfl
  strongDef _ _ _ := rfl
  weakGuardTarget d _ := entry_guard_le_threshold p i d
  guardTarget d _ := entry_guard_le_threshold p j d

theorem numeric_lower (p : Fin 4) (l : Fin 16) (d : ℕ)
    (hd : d ≤ (Sensitivity10007Endpoint16.entry p l).tolerance) :
    ((Sensitivity10007Endpoint16.entry p l).threshold d).val=
      (ThreeBoundMinmaxNumeric.Endpoint16.recipe p l).lowerAt d := by
  have hd9 : d<9 := by have hh := (Sensitivity10007Endpoint16.entry_internal_order p l).2.2.2.2; omega
  simp [ThreeBoundMinmaxNumeric.Endpoint16.recipe,ThreeBoundMinmaxNumeric.Entry.lowerAt,Array.getD,hd9]

theorem numeric_upper (p : Fin 4) (l : Fin 16) (d : ℕ)
    (hd : d ≤ (Sensitivity10007Endpoint16.entry p l).tolerance) :
    ((Sensitivity10007Endpoint16.entry p l).upper d).val=
      (ThreeBoundMinmaxNumeric.Endpoint16.recipe p l).upperAt d := by
  have hd9 : d<9 := by have hh := (Sensitivity10007Endpoint16.entry_internal_order p l).2.2.2.2; omega
  simp [ThreeBoundMinmaxNumeric.Endpoint16.recipe,ThreeBoundMinmaxNumeric.Entry.upperAt,Array.getD,hd9]

theorem entryMatch (p : Fin 4) (F : Fin 16 → (I → Bool) → Bool)
    (i j : Fin 16) (hij : i ≤ j) :
    EntryMatch ((Sensitivity10007Endpoint16.recipe p).stage F) F i j
      (pairData p F i j hij) (ThreeBoundMinmaxNumeric.Endpoint16.recipe p i)
      (ThreeBoundMinmaxNumeric.Endpoint16.recipe p j) where
  weakTolerance := rfl
  strongTolerance := rfl
  weakGuard := rfl
  strongGuard := rfl
  weakLower := numeric_lower p i
  weakUpper := numeric_upper p i
  strongLower := numeric_lower p j
  strongUpper := numeric_upper p j

end ThreeBoundEndpoint16Pairs

#print axioms ThreeBoundEndpoint16Pairs.pairData
#print axioms ThreeBoundEndpoint16Pairs.entryMatch


