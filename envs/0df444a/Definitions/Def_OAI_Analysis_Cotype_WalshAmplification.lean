-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
-- name    : OAI_Analysis_Cotype_WalshAmplification
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:24:28.17717+00:00
-- url     : https://prove2.me/theorems/63d338a1-86c7-4c9b-890a-1a6842363200
-- title:
--   Amplifying operators to l2-sums
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $\Omega$ be finite and $T:X\to Y$ bounded.
--
--   1. **$\ell_2$ amplification.** $T\otimes\mathrm{id}:\ell_2(\Omega;X)\to\ell_2(\Omega;Y)$,
--   $$
--   (x_a)_{a\in\Omega}\mapsto(Tx_a)_{a\in\Omega} ,
--   $$
--   with norm at most $\|T\|$.
--   2. **Walsh transforms.** The Walsh transform of the amplified operator acts coordinatewise. So Walsh estimates for $T$ transfer to $\ell_2$-sums of copies.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/WalshAmplification.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/WalshAmplification.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def l2AmplificationLinear (T : X →L[ℝ] Y) :
    PiLp 2 (fun _ : Ω => X) →ₗ[ℝ] PiLp 2 (fun _ : Ω => Y) where
  toFun x := toLp 2 (fun a => T (x a))
  map_add' x y := by ext a; exact T.map_add _ _
  map_smul' c x := by ext a; exact T.map_smul c _

omit [DecidableEq Ω] in
theorem l2AmplificationLinear_bound (T : X →L[ℝ] Y) (x : PiLp 2 (fun _ : Ω => X)) :
    ‖l2AmplificationLinear T x‖ ≤ ‖T‖ * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _ => by
    simpa [l2AmplificationLinear, mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T) (norm_nonneg (x a)))).mpr
        (T.le_opNorm (x a)))

def l2Amplification (T : X →L[ℝ] Y) :
    PiLp 2 (fun _ : Ω => X) →L[ℝ] PiLp 2 (fun _ : Ω => Y) :=
  (l2AmplificationLinear (Ω := Ω) T).mkContinuous ‖T‖
    (fun x => l2AmplificationLinear_bound T x)

omit [DecidableEq Ω] in
@[simp] theorem l2Amplification_apply (T : X →L[ℝ] Y)
    (x : PiLp 2 (fun _ : Ω => X)) (a : Ω) : l2Amplification T x a = T (x a) := rfl

omit [DecidableEq Ω] in
@[simp] theorem operatorWalsh_amplification_apply {n : ℕ} (T : X →L[ℝ] Y)
    (f : Cube n → PiLp 2 (fun _ : Ω => X)) (v : Cube n) (a : Ω) :
    operatorWalsh (l2Amplification T) f v a =
      operatorWalsh T (fun u => f u a) v := by
  simp [operatorWalsh, vectorWalsh, average]

end Cotype

end

end OAI


