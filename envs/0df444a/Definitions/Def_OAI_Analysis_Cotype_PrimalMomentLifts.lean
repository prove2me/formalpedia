-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
-- name    : OAI_Analysis_Cotype_PrimalMomentLifts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:33:58.277869+00:00
-- url     : https://prove2.me/theorems/fdc9e8e5-8b07-4c27-afe3-6e27740caa96
-- title:
--   Moment maps from sup-sums to l2-sums
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. The cube $\{0,1\}^n$ (Booleans) carries the uniform average $\mathbb E$, the signs $\varepsilon_i=\pm1$, the Walsh characters $w_A(\varepsilon)=\prod_{i\in A}\varepsilon_i$, and the norm $\|f\|_{L_2}=(\mathbb E\|f(\varepsilon)\|^2)^{1/2}$ for $X$-valued functions.
--
--   1. **Coordinate embeddings.** $x\mapsto x$ at a single index of $\ell_2(\Omega;X)$, an isometry. A functional on $\ell_2(\Omega;X)$ restricts to a tuple of functionals on $X$.
--   2. **Moment map.** $f\in\ell_\infty(\{0,1\}^m;X)\mapsto(\mathbb E\,\varepsilon_if)_{i\le m}\in\ell_2^m(X)$. Each moment is bounded by $\|f\|_\infty$, so
--   $$
--   \Bigl(\sum_i\|\mathbb E\,\varepsilon_if\|^2\Bigr)^{1/2}\le\sqrt m\,\|f\|_\infty .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/PrimalMomentLifts.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/PrimalMomentLifts.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def singleL2Linear (a : Ω) : X →ₗ[ℝ] PiLp 2 (fun _ : Ω => X) where
  toFun x := PiLp.single 2 a x
  map_add' x y := PiLp.single_add 2 a
  map_smul' c x := by ext b; simp [PiLp.single_apply, smul_ite]

def singleL2 (a : Ω) : X →L[ℝ] PiLp 2 (fun _ : Ω => X) :=
  (singleL2Linear (X := X) a).mkContinuous 1
    (fun x => by simp [singleL2Linear, PiLp.norm_single])

@[simp] theorem singleL2_apply (a : Ω) (x : X) : singleL2 a x = PiLp.single 2 a x := rfl

def tupleDualCoordinates (ψ : PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ) : Ω → (X →L[ℝ] ℝ) :=
  fun i => ψ.comp (singleL2 i)

def momentSupLinear (m : ℕ) : (Cube m → X) →ₗ[ℝ] PiLp 2 (fun _ : Fin m => X) where
  toFun f := toLp 2 (moment X f)
  map_add' f g := by ext i; simp [moment, average, smul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext i
    simp [moment, average, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    ring

theorem moment_norm_le_sup {m : ℕ} (f : Cube m → X) (i : Fin m) :
    ‖moment X f i‖ ≤ ‖f‖ := by
  calc
    _ ≤ average (fun u => ‖sign (u i) • f u‖) := norm_average_le _
    _ ≤ average (fun _ : Cube m => ‖f‖) := average_mono (fun u => by
      have h := norm_le_pi_norm f u
      cases u i <;> simpa using h)
    _ = _ := by simp [average]

theorem momentSupLinear_bound (m : ℕ) (f : Cube m → X) :
    ‖momentSupLinear m f‖ ≤ Real.sqrt m * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  calc
    _ ≤ ∑ _ : Fin m, ‖f‖^2 := Finset.sum_le_sum (fun i _ =>
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (moment_norm_le_sup f i))
    _ = _ := by simp

def momentSup (m : ℕ) : (Cube m → X) →L[ℝ] PiLp 2 (fun _ : Fin m => X) :=
  (momentSupLinear (X := X) m).mkContinuous (Real.sqrt m) (momentSupLinear_bound m)

@[simp] theorem momentSup_apply (m : ℕ) (f : Cube m → X) (i : Fin m) :
    momentSup m f i = moment X f i := rfl

end Cotype

end

end OAI


