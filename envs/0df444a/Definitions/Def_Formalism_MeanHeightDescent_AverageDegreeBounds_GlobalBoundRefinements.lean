-- Prove2me | Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GlobalBoundRefinements
-- name    : Formalism_MeanHeightDescent_AverageDegreeBounds_GlobalBoundRefinements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:25:07.774222+00:00
-- url     : https://prove2.me/theorems/7f07924c-da3e-4dde-8743-c54c8061caf7
-- title:
--   Global Bound Refinements
-- statement:
--   Definitions and structural lemmas for Global Bound Refinements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GlobalBoundRefinements.lean

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeEstimateAnchoredWeights
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeFullAssemblyHolds
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_CovolumeIntoDivisionHolds
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_SpanMuMin
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_TwistLower
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_MuMaxMinkowski
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.ExtensionFiltration
section Numbers
open Finset Module NumberField
end Numbers
noncomputable section Short
open Module NumberField
open Formalism.HN
section Core
open NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped ENNReal NNReal nonZeroDivisors
end Core
section Line
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
  [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
end Line
end Short
noncomputable section Primes
open Finset
end Primes
end Formalism.ExtensionFiltration


