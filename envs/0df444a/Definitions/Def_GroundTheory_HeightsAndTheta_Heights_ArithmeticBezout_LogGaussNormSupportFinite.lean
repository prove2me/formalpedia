-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:23.931311+00:00
-- url     : https://prove2.me/theorems/3f80a7db-c7ad-4db6-b178-6a0029595d97
-- title:
--   Log Gauss Norm Support Finite
-- statement:
--   Definitions and structural lemmas for Log Gauss Norm Support Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
section General
variable {R : Type*} [CommRing R] {ι : Type*} (w : AbsoluteValue R ℝ)
def gaussNormOf (f : MvPolynomial ι R) : ℝ :=
  let s : NNReal := f.support.sup fun m => ⟨w (f.coeff m), w.nonneg _⟩
  (s : ℝ)
variable {w}
end General
section NumberField
variable {K : Type*} [Field K] [NumberField K]
end NumberField
end
end GroundTheory.Heights₂.Heights


