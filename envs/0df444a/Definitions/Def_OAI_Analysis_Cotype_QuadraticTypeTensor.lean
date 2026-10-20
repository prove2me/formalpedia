-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
-- name    : OAI_Analysis_Cotype_QuadraticTypeTensor
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:19:33.323229+00:00
-- url     : https://prove2.me/theorems/9d47965b-8820-413d-8161-687f80b3ef3a
-- title:
--   Quadratic type bounds and sign twists
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. The cube $\{0,1\}^n$ (Booleans) carries the uniform average $\mathbb E$, the signs $\varepsilon_i=\pm1$, the Walsh characters $w_A(\varepsilon)=\prod_{i\in A}\varepsilon_i$, and the norm $\|f\|_{L_2}=(\mathbb E\|f(\varepsilon)\|^2)^{1/2}$ for $X$-valued functions.
--
--   1. **Quadratic type bound.** $X$ has quadratic type bound $A$ in dimension $n$ if
--   $$
--   \Bigl\|\sum_i\varepsilon_ix_i\Bigr\|_{L_2}^2\le A\sum_i\|x_i\|^2
--   $$
--   for all $x_1,\dots,x_n$, i.e. type-$2$ constant $\sqrt A$ on $n$ vectors.
--   2. **Sign twist.** For $\sigma\in\{0,1\}^n$, the involution $\varepsilon\mapsto\sigma\oplus\varepsilon$ of the cube. It preserves averages and multiplies Rademacher sums by fixed signs.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/QuadraticTypeTensor.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/QuadraticTypeTensor.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def QuadraticTypeBound (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (n : ℕ) (A : ℝ) : Prop :=
  ∀ x : Fin n → X, cubeL2 X (rademacherSum X x)^2 ≤ A*∑ i, ‖x i‖^2

def signCubeTwist {n : ℕ} (σ : Cube n) : Cube n ≃ Cube n where
  toFun ε i := xor (σ i) (ε i)
  invFun ε i := xor (σ i) (ε i)
  left_inv ε := by
    funext i
    change xor (σ i) (xor (σ i) (ε i)) = ε i
    cases σ i <;> cases ε i <;> rfl
  right_inv ε := by
    funext i
    change xor (σ i) (xor (σ i) (ε i)) = ε i
    cases σ i <;> cases ε i <;> rfl

@[simp] theorem sign_mul_of_xor (a b : Bool) : sign (xor a b) = sign a*sign b := by
  cases a <;> cases b <;> norm_num

end Cotype

end

end OAI


