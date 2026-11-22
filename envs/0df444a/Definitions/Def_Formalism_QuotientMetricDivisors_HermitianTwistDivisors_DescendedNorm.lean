-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
-- name    : Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:52.132873+00:00
-- url     : https://prove2.me/theorems/dd666b04-8e4a-438d-82a6-772d30da6616
-- title:
--   Descended Norm
-- statement:
--   Definitions and structural lemmas for Descended Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/DescendedNorm.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HeightBoundExactNorms
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionThirdStepMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
namespace Formalism.DivisionValues
namespace OperatorNormFrames
def pmat {K : Type} [Field K] [NumberField K] {a D : ℕ} (v : InfinitePlace K)
    (B : (Fin a → K) →ₗ[K] Module.Dual K (Fin D → K)) : Matrix (Fin D) (Fin a) ℂ :=
  Matrix.of fun k i => v.embedding (B (Pi.single i 1) (Pi.single k 1))
end OperatorNormFrames
open OperatorNormFrames
namespace OperatorNormFrames
end OperatorNormFrames
namespace OperatorNormFrames
end OperatorNormFrames
namespace OperatorNormFrames
end OperatorNormFrames
namespace OperatorNormFrames
end OperatorNormFrames
namespace OperatorNormFrames
def nrm {a b : ℕ} (A : Matrix (Fin b) (Fin a) ℂ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖
end OperatorNormFrames
namespace OperatorNormFrames
section G
variable {K : Type} [Field K] [NumberField K] {D : ℕ}
def gmap (v : InfinitePlace K) (Y : Matrix (Fin D) (Fin D) ℂ) (x : Fin D → K) :
    EuclideanSpace ℂ (Fin D) :=
  WithLp.toLp 2 (Y⁻¹.mulVec fun i => v.embedding (x i))
end G
end OperatorNormFrames
end Formalism.DivisionValues


