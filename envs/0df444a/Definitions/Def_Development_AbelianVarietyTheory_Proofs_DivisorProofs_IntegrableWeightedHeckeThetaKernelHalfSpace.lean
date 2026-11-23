-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpace
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegrableWeightedHeckeThetaKernelHalfSpace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:02:16.708909+00:00
-- url     : https://prove2.me/theorems/6a0c978b-8ec9-4988-a215-dd22e9c092f0
-- title:
--   Integrable Weighted Hecke Theta Kernel Half Space
-- statement:
--   Definitions and structural lemmas for Integrable Weighted Hecke Theta Kernel Half Space, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegrableWeightedHeckeThetaKernelHalfSpace.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
namespace GlobalTheory.HeckeTheta.Decay
open GlobalTheory.HeckeTheta
variable {I : Type} [Fintype I]
def gC (n : I → ℤ) : ℝ := ∏ i, (1 + ((n i).natAbs.factorial : ℝ))
end GlobalTheory.HeckeTheta.Decay
namespace GlobalTheory.HeckeTheta.Decay
open GlobalTheory.HeckeTheta
end GlobalTheory.HeckeTheta.Decay


