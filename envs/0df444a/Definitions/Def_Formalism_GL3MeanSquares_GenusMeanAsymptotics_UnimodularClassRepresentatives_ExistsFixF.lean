-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFixF
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFixF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:40:51.488841+00:00
-- url     : https://prove2.me/theorems/4333a8e8-f594-4e5a-b20e-718dc809c3a7
-- title:
--   Exists Fix F
-- statement:
--   Definitions and structural lemmas for Exists Fix F, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsFixF.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3
def starFixed (K : Type) [Field K] [CharZero K] [StarRing K] : IntermediateField ℚ K where
  carrier := {a : K | star a = a}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [star_mul', ha, hb]
  one_mem' := star_one K
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [star_add, ha, hb]
  zero_mem' := star_zero K
  algebraMap_mem' := by
    intro q
    exact map_ratCast (starRingEnd K) q
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [star_inv₀, ha]
end Formalism.HermitianLattices.Ext.L3


