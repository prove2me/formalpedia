-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
-- name    : OAI_Analysis_Cotype_ProjectionAverages
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:45:58.329187+00:00
-- url     : https://prove2.me/theorems/8806de3f-ba7e-4dd3-92f8-d9bb12b25e7b
-- title:
--   Products of weighted operator sums
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $\Omega$ be finite.
--
--   1. **Choice splitting.** $\Omega\times\Omega^n\cong\Omega^{n+1}$, by choosing the first coordinate separately.
--   2. **Product of sums.** For weights $w_i(a)$ and operators $P_i(a)$,
--   $$
--   \prod_i\sum_aw_i(a)P_i(a)=\sum_{a:\{1..n\}\to\Omega}\Bigl(\prod_iw_i(a_i)\Bigr)\prod_iP_i(a_i),
--   $$
--   the noncommutative expansion of a product of averages.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ProjectionAverages.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionAverages.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def projectionChoiceCons (Ω : Type*) (n : ℕ) :
    Ω × (Fin n → Ω) ≃ (Fin (n+1) → Ω) where
  toFun p := Fin.cons p.1 p.2
  invFun u := (u 0, Fin.tail u)
  left_inv p := by ext i <;> simp
  right_inv u := by ext i; exact Fin.cases (by simp) (fun i => by simp; rfl) i

theorem projectionProduct_weighted_sum {Ω : Type*} [Fintype Ω] {n : ℕ}
    (w : Fin n → Ω → ℝ) (P : Fin n → Ω → X →L[ℝ] X) :
    projectionProduct (fun i => ∑ a, w i a • P i a) =
      ∑ ω : Fin n → Ω, (∏ i, w i (ω i)) • projectionProduct (fun i => P i (ω i)) := by
  classical
  induction n with
  | zero => simp [projectionProduct]
  | succ n ih =>
    rw [← (projectionChoiceCons Ω n).sum_comp]
    simp only [Fintype.sum_prod_type, projectionChoiceCons, Equiv.coe_fn_mk,
      Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, projectionProduct]
    rw [ih]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro ω _
    rw [mul_comm]

end Cotype

end

end OAI


