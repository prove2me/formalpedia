-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ContinuousBlockDiagEmbedRingHom
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ContinuousBlockDiagEmbedRingHom
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:53:07.951209+00:00
-- url     : https://prove2.me/theorems/97b60139-443f-4a76-b65d-9b3327e6f97c
-- title:
--   Continuous Block Diag Embed Ring Hom
-- statement:
--   Definitions and structural lemmas for Continuous Block Diag Embed Ring Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/ContinuousBlockDiagEmbedRingHom.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block3_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_block_three_zero_size_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
namespace PI.UnitaryGroupMassFormula.UsCost
section words
variable {k j ρ : ℕ}
def blockDiagEmbedRingHom (k j ρ : ℕ) : B.Mat k ρ × Matrix (Fin j) (Fin j) ℂ →+* B.Mat k (j + ρ) where
  toFun x := blk3 x.2 0 0 0 x.1 0 0 0 x.2
  map_one' := Formalism.FourierDecayAlt.P.Ux4.block3_one.symm
  map_mul' x y := by
    rw [Formalism.FourierDecayAlt.P.Ux4.block3_mul]
    simp
  map_zero' := Formalism.FourierDecayAlt.P.Ux4.block_three_zero_size_eq
  map_add' x y := by
    rw [Formalism.FourierDecayAlt.P.Ux4.block3_add]
    simp
end words
section comp
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ} {ξ : Xi k p s ρ σ} {Z : G.Mat s}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
end comp
end PI.UnitaryGroupMassFormula.UsCost


