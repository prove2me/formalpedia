-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
-- name    : OAI_Analysis_Cotype_WalshExactPairing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:58:40.690021+00:00
-- url     : https://prove2.me/theorems/ab83887d-a496-4623-92aa-87ed5591f7c6
-- title:
--   Twisted functions on the doubled cube
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Walsh characters are $w_v(u)=(-1)^{\langle u,v\rangle}$ for $u,v\in\{0,1\}^n\cong\mathbb F_2^n$. Let $p:\{0,1\}^n\to X$ and $q:\{0,1\}^n\to Y^*$.
--
--   1. **Translations.** $u\mapsto a\oplus u$, an involution of the cube.
--   2. **Twisted primal.** On $\{0,1\}^{n+n}\ni(a,b)$, for fixed $u$:
--   $$
--   (a,b)\mapsto w_u(b)\,w_a(b)\;p(u\oplus a) .
--   $$
--   3. **Twisted dual.** For fixed $v$: $(a,b)\mapsto w_a(v)\,q(v\oplus b)$.
--
--   These twisted families realize the Walsh pairing exactly. Pairing them reproduces $w_v(u)$ times a fixed scalar, which is used to build exact pairings for Walsh norms.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/WalshExactPairing.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/WalshExactPairing.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def cubeTranslate {n : ℕ} (a : Cube n) : Cube n ≃ Cube n where
  toFun u := xorCube a u
  invFun u := xorCube a u
  left_inv u := by ext i; simp [xorCube]
  right_inv u := by ext i; simp [xorCube]

def twistedPrimal {n : ℕ} (p : Cube n → X) (u : Cube n) (z : Cube (n+n)) : X :=
  let ab := (cubeJoin n n).symm z
  (character u ab.2 * character ab.1 ab.2) • p (xorCube u ab.1)

def twistedDual {n : ℕ} (q : Cube n → (Y →L[ℝ] ℝ)) (v : Cube n)
    (z : Cube (n+n)) : Y →L[ℝ] ℝ :=
  let ab := (cubeJoin n n).symm z
  character ab.1 v • q (xorCube v ab.2)

@[simp] theorem twistedPrimal_join {n : ℕ} (p : Cube n → X) (u a b : Cube n) :
    twistedPrimal p u (cubeJoin n n (a,b)) =
      (character u b * character a b) • p (xorCube u a) := by
  simp only [twistedPrimal, Equiv.symm_apply_apply]

@[simp] theorem twistedDual_join {n : ℕ} (q : Cube n → (Y →L[ℝ] ℝ)) (v a b : Cube n) :
    twistedDual q v (cubeJoin n n (a,b)) = character a v • q (xorCube v b) := by
  simp only [twistedDual, Equiv.symm_apply_apply]

end Cotype

end

end OAI


