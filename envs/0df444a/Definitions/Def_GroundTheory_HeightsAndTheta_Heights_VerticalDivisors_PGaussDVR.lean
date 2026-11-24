-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGaussDVR
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGaussDVR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:33:22.21745+00:00
-- url     : https://prove2.me/theorems/c743dac0-d7f9-406a-8b35-325f673551d9
-- title:
--   PGauss DVR
-- statement:
--   Definitions and structural lemmas for PGauss DVR, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PGaussDVR.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain WithZero
noncomputable section
section Dedekind
variable {A : Type*} [CommRing A] [IsDedekindDomain A] (v : HeightOneSpectrum A)
end Dedekind
section NumberField
variable {K : Type*} [Field K] [NumberField K]
end NumberField
end
end GroundTheory.Heights₂.Heights.Vertical


