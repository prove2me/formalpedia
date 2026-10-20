-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_L2MomentLifts
-- name    : OAI_Analysis_Cotype_L2MomentLifts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T18:28:50.669871+00:00
-- url     : https://prove2.me/theorems/19e0c453-32ab-4a24-ab96-36248a867cc2
-- title:
--   Moment maps on L2 of the cube
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. The cube $\{0,1\}^n$ (Booleans) carries the uniform average $\mathbb E$, the signs $\varepsilon_i=\pm1$, the Walsh characters $w_A(\varepsilon)=\prod_{i\in A}\varepsilon_i$, and the norm $\|f\|_{L_2}=(\mathbb E\|f(\varepsilon)\|^2)^{1/2}$ for $X$-valued functions.
--
--   1. **Moment bound.** Each moment satisfies $\|\mathbb E\,\varepsilon_if\|\le\|f\|_{L_2}$.
--   2. **$L_2$ moment map.** $f\mapsto(\mathbb E\,\varepsilon_if)_{i\le m}$ from $\ell_2(\{0,1\}^m;X)$ to $\ell_2^m(X)$. With the counting normalization its norm is at most
--   $$
--   \sqrt m\cdot2^{-m/2} .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/L2MomentLifts.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/L2MomentLifts.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
import Definitions.Def_OAI_Analysis_Cotype_CubeFirstChaos
import Definitions.Def_OAI_Analysis_Cotype_FrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_BinaryCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshFrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_FrameFeasibility
import Definitions.Def_OAI_Analysis_Cotype_EquivariantLifts
import Definitions.Def_OAI_Analysis_Cotype_DualAction
import Definitions.Def_OAI_Analysis_Cotype_EquivariantPairing
import Definitions.Def_OAI_Analysis_Cotype_FrameLifts

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def momentL2Linear (m : ℕ) : PiLp 2 (fun _ : Cube m => X) →ₗ[ℝ] PiLp 2 (fun _ : Fin m => X) where
  toFun f := toLp 2 (moment X (fun u => f u))
  map_add' f g := by ext i; simp [moment, average, smul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext i
    simp [moment, average, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    ring

theorem moment_norm_le_cubeL2 {m : ℕ} (f : Cube m → X) (i : Fin m) :
    ‖moment X f i‖ ≤ cubeL2 X f := by
  simpa only [vectorWalsh, character_unitIndex, moment] using vectorWalsh_bound f (unitIndex i)

theorem momentL2Linear_bound (m : ℕ) (f : PiLp 2 (fun _ : Cube m => X)) :
    ‖momentL2Linear m f‖ ≤
      (Real.sqrt m * Real.sqrt ((Fintype.card (Cube m) : ℝ)⁻¹)) * ‖f‖ := by
  have h : ‖momentL2Linear m f‖ ≤ Real.sqrt m * cubeL2 X (fun u => f u) := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (cubeL2_nonneg _))).mp
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
    calc
      _ ≤ ∑ _ : Fin m, cubeL2 X (fun u => f u)^2 := Finset.sum_le_sum (fun i _ =>
        (sq_le_sq₀ (norm_nonneg _) (cubeL2_nonneg _)).mpr (moment_norm_le_cubeL2 _ i))
      _ = _ := by simp
  simpa only [cubeL2_eq_piLp, toLp_ofLp, mul_assoc] using h

def momentL2 (m : ℕ) : PiLp 2 (fun _ : Cube m => X) →L[ℝ] PiLp 2 (fun _ : Fin m => X) :=
  (momentL2Linear (X := X) m).mkContinuous
    (Real.sqrt m * Real.sqrt ((Fintype.card (Cube m) : ℝ)⁻¹)) (momentL2Linear_bound m)

@[simp] theorem momentL2_apply (m : ℕ) (f : PiLp 2 (fun _ : Cube m => X)) (i : Fin m) :
    momentL2 m f i = moment X (fun u => f u) i := rfl

end Cotype

end

end OAI


