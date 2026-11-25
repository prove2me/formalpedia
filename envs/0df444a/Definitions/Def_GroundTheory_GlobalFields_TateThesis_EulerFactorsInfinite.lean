-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsInfinite
-- name    : GroundTheory_GlobalFields_TateThesis_EulerFactorsInfinite
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T08:26:33.739681+00:00
-- url     : https://prove2.me/theorems/19f16b85-f4e7-505f-92e9-4bb4917a893f
-- title:
--   Euler Factors Infinite
-- statement:
--   Definitions and structural lemmas for Euler Factors Infinite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsInfinite.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsArch
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
  NumberField.mixedEmbedding Function
open scoped Real SchwartzMap Classical RealInnerProductSpace
namespace GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace HeckeCharacter
variable (χ : HeckeCharacter K)
def infinitePoly (x : mixedSpace K) : ℂ :=
  (∏ w : {w // IsReal w}, ((x.1 w : ℝ) : ℂ) ^ (χ.infiniteWeight w).natAbs) *
    ∏ w : {w // IsComplex w},
      (if 0 < χ.infiniteWeight w then conj (x.2 w) else x.2 w) ^ (χ.infiniteWeight w).natAbs
def infiniteSchwartz : 𝓢(mixedSpace K, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ χ.infinitePoly
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean K)
      (gaussianSchwartz (euclidean.mixedSpace K)))
end HeckeCharacter
end
end GroundTheory.Global


