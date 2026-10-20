-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
-- name    : OAI_Analysis_Cotype_CubeCoordinateProjections
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:07:04.235994+00:00
-- url     : https://prove2.me/theorems/b221073f-d578-45a2-8e5d-9817bf795625
-- title:
--   Coordinate reflections and conditional expectations
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. The cube $\{0,1\}^n$ (Booleans) carries the uniform average $\mathbb E$, the signs $\varepsilon_i=\pm1$, the Walsh characters $w_A(\varepsilon)=\prod_{i\in A}\varepsilon_i$, and the norm $\|f\|_{L_2}=(\mathbb E\|f(\varepsilon)\|^2)^{1/2}$ for $X$-valued functions. Work in $\ell_2(\{0,1\}^n;X)$.
--
--   1. **Coordinate reflection.** $(R_if)(\varepsilon)=f(\varepsilon\text{ with bit }i\text{ flipped})$, an isometry.
--   2. **Coordinate expectation.**
--   $$
--   E_i=\tfrac12(1+R_i),\qquad(E_if)(\varepsilon)=\tfrac12\bigl(f(\varepsilon)+f(\varepsilon^{(i)})\bigr),
--   $$
--   the conditional expectation that averages out coordinate $i$. The $E_i$ are commuting contractive projections. Their projection semigroup is the heat semigroup on the cube, and its degree-one part is the Rademacher projection.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/CubeCoordinateProjections.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/CubeCoordinateProjections.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def coordinateReflection {n : ℕ} (i : Fin n) :
    PiLp 2 (fun _ : Cube n => X) →L[ℝ] PiLp 2 (fun _ : Cube n => X) :=
  (l2Reindex (signCubeTwist (unitIndex i))).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem coordinateReflection_apply {n : ℕ} (i : Fin n)
    (f : PiLp 2 (fun _ : Cube n => X)) (ε : Cube n) :
    coordinateReflection i f ε = f (signCubeTwist (unitIndex i) ε) := rfl

def coordinateExpectation {n : ℕ} (i : Fin n) :
    PiLp 2 (fun _ : Cube n => X) →L[ℝ] PiLp 2 (fun _ : Cube n => X) :=
  (1/2 : ℝ) • (1+coordinateReflection i)

@[simp] theorem coordinateExpectation_apply {n : ℕ} (i : Fin n)
    (f : PiLp 2 (fun _ : Cube n => X)) (ε : Cube n) :
    coordinateExpectation i f ε = (1/2 : ℝ) • (f ε+f (signCubeTwist (unitIndex i) ε)) := rfl

end Cotype

end

end OAI


