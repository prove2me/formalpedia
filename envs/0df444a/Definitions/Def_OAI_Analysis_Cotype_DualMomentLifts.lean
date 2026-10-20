-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
-- name    : OAI_Analysis_Cotype_DualMomentLifts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:30:03.841881+00:00
-- url     : https://prove2.me/theorems/fc44f829-b5d4-4e8f-96b8-badb705f562f
-- title:
--   Rademacher and moment maps between l2 and L1
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. The cube $\{0,1\}^n$ (Booleans) carries the uniform average $\mathbb E$, the signs $\varepsilon_i=\pm1$, the Walsh characters $w_A(\varepsilon)=\prod_{i\in A}\varepsilon_i$, and the norm $\|f\|_{L_2}=(\mathbb E\|f(\varepsilon)\|^2)^{1/2}$ for $X$-valued functions.
--
--   1. **Rademacher map.** $(x_i)_{i\le m}\in\ell_2^m(X)\mapsto\sum_i\varepsilon_ix_i\in\ell_1(\{0,1\}^m;X)$.
--   2. **Moment map.** $f\mapsto(\mathbb E\,\varepsilon_if)_{i\le m}$, a left inverse:
--   $$
--   \text{moments}\Bigl(\sum_i\varepsilon_ix_i\Bigr)=x .
--   $$
--   3. **Point embeddings.** $x\mapsto$ the function equal to $x$ at one point and $0$ elsewhere, an isometry into the $\ell_1$-sum.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/DualMomentLifts.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/DualMomentLifts.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def rademacherL1Linear (m : ℕ) :
    PiLp 2 (fun _ : Fin m => X) →ₗ[ℝ] PiLp 1 (fun _ : Cube m => X) where
  toFun z := toLp 1 (rademacherSum X (fun i => z i))
  map_add' z w := by ext u; simp [rademacherSum, smul_add, Finset.sum_add_distrib]
  map_smul' c z := by ext u; simp [rademacherSum, Finset.smul_sum, smul_smul, mul_comm]

def momentL1Linear (m : ℕ) :
    PiLp 1 (fun _ : Cube m => X) →ₗ[ℝ] PiLp 2 (fun _ : Fin m => X) where
  toFun f := toLp 2 (moment X (fun u => f u))
  map_add' f g := by ext i; simp [moment, average, smul_add, Finset.sum_add_distrib]
  map_smul' c f := by
    ext i
    simp [moment, average, Finset.smul_sum, smul_smul]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    ring

@[simp] theorem momentL1_rademacherL1 (m : ℕ) (z : PiLp 2 (fun _ : Fin m => X)) :
    momentL1Linear m (rademacherL1Linear m z) = z := by
  ext i
  exact moment_rademacherSum X (fun i => z i) i

def singleL1Linear {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (a : Ω) :
    X →ₗ[ℝ] PiLp 1 (fun _ : Ω => X) where
  toFun x := PiLp.single 1 a x
  map_add' x y := PiLp.single_add 1 a
  map_smul' c x := by ext b; simp [PiLp.single_apply, smul_ite]

def singleL1 {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (a : Ω) :
    X →L[ℝ] PiLp 1 (fun _ : Ω => X) :=
  (singleL1Linear (X := X) a).mkContinuous 1
    (fun x => by simp [singleL1Linear, PiLp.norm_single])

@[simp] theorem singleL1_apply {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (a : Ω) (x : X) :
    singleL1 a x = PiLp.single 1 a x := rfl

end Cotype

end

end OAI


