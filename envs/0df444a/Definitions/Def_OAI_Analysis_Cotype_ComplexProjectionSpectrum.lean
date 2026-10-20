-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
-- name    : OAI_Analysis_Cotype_ComplexProjectionSpectrum
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:55:26.050158+00:00
-- url     : https://prove2.me/theorems/339d5368-408f-41b2-9cfc-8d5af4b64b62
-- title:
--   Spectral calculus for commuting projections
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. For commuting bounded projections $P_1,\dots,P_m$ on $X$, products are taken in a fixed order, $P_S=\prod_{i\in S}P_i$, and the coordinate semigroup is $T(r)=\prod_i\bigl(P_i+r(1-P_i)\bigr)$. Let $Q_\varepsilon$ be the spectral patterns and $\widehat{\cdot}$ the complex dual lift.
--
--   1. **Spectral evaluation.** For $f:\{0,1\}^m\to\mathbb C$,
--   $$
--   f(P)=\sum_\varepsilon f(\varepsilon)\,\widehat{Q_\varepsilon} .
--   $$
--   It satisfies $1(P)=1$ and $(fg)(P)=f(P)g(P)$, a functional calculus.
--   2. **Degree.** $|\varepsilon|$, the number of ones. The complex semigroup is $\widehat T(z)=\sum_\varepsilon z^{|\varepsilon|}\widehat{Q_\varepsilon}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ComplexProjectionSpectrum.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ComplexProjectionSpectrum.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def complexSpectralEval {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (f : Cube m → ℂ) :
    ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y :=
  ∑ ε, f ε • complexDualLift (projectionPattern P ε)

@[simp] theorem complexDualLift_zero : complexDualLift (0 : Y →L[ℝ] Y) = 0 :=
  map_zero (complexDualLiftCLM (Y := Y))

theorem complexSpectralEval_one {m : ℕ} (P : Fin m → Y →L[ℝ] Y) :
    complexSpectralEval P 1 = 1 := by
  simp only [complexSpectralEval, Pi.one_apply, one_smul]
  change (∑ ε, complexDualLiftCLM (projectionPattern P ε)) = 1
  rw [← map_sum]
  simp only [complexDualLiftCLM_apply, projectionPattern_sum, complexDualLift_one]

theorem complexSpectralEval_mul {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j))
    (f g : Cube m → ℂ) :
    complexSpectralEval P f * complexSpectralEval P g = complexSpectralEval P (f*g) := by
  classical
  have hpat (ε η : Cube m) :
      complexDualLift (projectionPattern P ε) * complexDualLift (projectionPattern P η) =
        if ε = η then complexDualLift (projectionPattern P ε) else 0 := by
    rw [← complexDualLift_mul, projectionPattern_mul P hp hc]
    split_ifs <;> simp
  have hmul_smul (left right : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y)
      (scalar : ℂ) : left * (scalar • right) = scalar • (left * right) := by
    apply ContinuousLinearMap.ext
    intro vector
    exact left.map_smul scalar (right vector)
  have hsmul_mul (scalar : ℂ) (left right : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) :
      (scalar • left) * right = scalar • (left * right) := by
    apply ContinuousLinearMap.ext
    intro vector
    rfl
  have hsmul_zero (scalar : ℂ) :
      scalar • (0 : ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) = 0 := by
    ext vector dual
    exact mul_zero scalar
  simp only [complexSpectralEval, Finset.sum_mul, Finset.mul_sum,
    hsmul_mul, hmul_smul, Finset.smul_sum, hpat]
  simp [smul_ite, Pi.mul_apply, smul_smul, mul_comm, hsmul_zero]

def projectionDegree {m : ℕ} (ε : Cube m) : ℕ :=
  (Finset.univ.filter (fun i => ε i = true)).card

end Cotype

end

end OAI


