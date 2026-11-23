-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_NegGram
-- name    : Development_AbelianVarietyTheory_Definitions_GlobalTwisting_NegGram
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:32.129178+00:00
-- url     : https://prove2.me/theorems/96d408b7-2538-4e58-a71c-6e0c5e0e32a4
-- title:
--   Neg Gram
-- statement:
--   Definitions and structural lemmas for Neg Gram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/GlobalTwisting/NegGram.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions NumberField
namespace GlobalTheory.NegSpace
variable {E : Type} [Field E] [NumberField E] [StarRing E]
def neg (W : HSpace E) : HSpace E :=
  { W with
    hT := -W.hT
    herm := ⟨fun x y => by simpa using W.herm.eq x y⟩
    nondeg := ⟨fun x h => W.nondeg.1 x fun y => by simpa using h y,
      fun x h => W.nondeg.2 x fun y => by simpa using h y⟩
    sig := fun τ => ((W.sig τ).2, (W.sig τ).1)
    baseLattice_isUnimodular := by
      have h := W.baseLattice_isUnimodular
      have e : Formalism.HermitianLatticesTheory.dual (-W.hT) W.L0 = Formalism.HermitianLatticesTheory.dual W.hT W.L0 := by
        ext y
        simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]
      unfold Formalism.HermitianLatticesTheory.IsUnimodular at h ⊢
      rw [e]; exact h }
end GlobalTheory.NegSpace


