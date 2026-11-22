-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:21:38.332833+00:00
-- url     : https://prove2.me/theorems/45e0ac4d-ab80-4257-ae46-24df4ebc45d2
-- title:
--   Image Lcv
-- statement:
--   Definitions and structural lemmas for Image Lcv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ImageLcv.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.DivisionValues
section SlopeTestRemainingChoices
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
end SlopeTestRemainingChoices
section Add
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
end Add
section Main
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Main
end Formalism.DivisionValues


