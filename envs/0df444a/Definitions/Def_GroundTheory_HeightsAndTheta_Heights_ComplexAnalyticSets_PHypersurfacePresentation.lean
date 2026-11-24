-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHypersurfacePresentation
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHypersurfacePresentation
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:35.882879+00:00
-- url     : https://prove2.me/theorems/cf9f25ef-57b2-4f1e-8d32-6d17a5f0c8c6
-- title:
--   PHypersurface Presentation
-- statement:
--   Definitions and structural lemmas for PHypersurface Presentation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHypersurfacePresentation.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
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
open MvPolynomial
noncomputable section
namespace HypersurfacePresentation
section Core
variable {R A E L : Type} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]
  [Field E] [Algebra R E] [IsFractionRing R E] [CharZero E]
  [Field L] [Algebra A L] [IsFractionRing A L] [Algebra R L] [IsScalarTower R A L]
  [Algebra E L] [IsScalarTower R E L]
end Core
section Generic
end Generic
section Main
variable {σ ι : Type} [Finite σ] [Finite ι] (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ))) [K.IsPrime]
local notation "𝔸" => MvPolynomial ι (MvPolynomial σ ℂ) ⧸ K
end Main
end HypersurfacePresentation
end
end GroundTheory.Heights₂.Heights


