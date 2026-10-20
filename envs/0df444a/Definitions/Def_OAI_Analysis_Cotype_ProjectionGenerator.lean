-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
-- name    : OAI_Analysis_Cotype_ProjectionGenerator
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:57:25.477146+00:00
-- url     : https://prove2.me/theorems/799dd8c1-3197-4b7d-8aba-7fb0ee5ea3b8
-- title:
--   The generator of the projection semigroup
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. For commuting bounded projections $P_1,\dots,P_m$ on $X$, products are taken in a fixed order, $P_S=\prod_{i\in S}P_i$, and the coordinate semigroup is $T(r)=\prod_i\bigl(P_i+r(1-P_i)\bigr)$. The spectral patterns $Q_\varepsilon=\prod_i(1-P_i\text{ or }P_i)$ of commuting projections decompose the identity, and $\widehat{\cdot}$ denotes the complex dual lift; functions $f$ of the pattern give $f(P)=\sum_\varepsilon f(\varepsilon)\widehat{Q_\varepsilon}$.
--
--   1. **Spectral homomorphism.** $f\mapsto f(P)$ is a $\mathbb C$-algebra homomorphism from functions on $\{0,1\}^m$, with constants mapping to scalars.
--   2. **Generator.** $G=\sum_\varepsilon|\varepsilon|\,\widehat{Q_\varepsilon}$, the number operator counting how many projections are switched off.
--   3. **Complex time.** $\widehat T(e^{-t})$ for $t\in\mathbb C$, so that
--   $$
--   \widehat T(e^{-t})=e^{-tG} .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ProjectionGenerator.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionGenerator.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem complexSpectralEval_const {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (c : ℂ) :
    complexSpectralEval P (fun _ => c) = c • 1 := by
  rw [← complexSpectralEval_one P]
  ext vector dual
  simp [complexSpectralEval, Finset.mul_sum]

def complexProjectionSpectralHom {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j)) :
    (Cube m → ℂ) →ₐ[ℂ] (ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y) where
  toFun := complexSpectralEval P
  map_zero' := by
    ext vector dual
    simp [complexSpectralEval]
  map_one' := complexSpectralEval_one P
  map_add' f g := by
    ext vector dual
    simp [complexSpectralEval, add_mul, Finset.sum_add_distrib]
  map_mul' f g := (complexSpectralEval_mul P hp hc f g).symm
  commutes' c := by
    change complexSpectralEval P (fun _ => c) = _
    rw [complexSpectralEval_const, Algebra.algebraMap_eq_smul_one]

def projectionGenerator {m : ℕ} (P : Fin m → Y →L[ℝ] Y) :
    ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y :=
  complexSpectralEval P (fun ε => (projectionDegree ε : ℂ))

def complexProjectionTime {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (t : ℂ) :
    ComplexDualSpace Y →L[ℂ] ComplexDualSpace Y :=
  complexProjectionPolynomial P (Complex.exp (-t))

end Cotype

end

end OAI


