-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
-- name    : OAI_Analysis_Cotype_ScalarWalsh
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:27:02.965108+00:00
-- url     : https://prove2.me/theorems/0bcd052e-aec9-4b32-9b35-b847c16453cf
-- title:
--   The scalar Walsh transform
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. The cube $\{0,1\}^n$ (Booleans) carries the uniform average $\mathbb E$, the signs $\varepsilon_i=\pm1$, the Walsh characters $w_A(\varepsilon)=\prod_{i\in A}\varepsilon_i$, and the norm $\|f\|_{L_2}=(\mathbb E\|f(\varepsilon)\|^2)^{1/2}$ for $X$-valued functions.
--
--   1. **$L_2$ norm.** $\|f\|_{L_2}^2=\mathbb E\|f(\varepsilon)\|^2$, and the norm is nonnegative.
--   2. **Scalar Walsh transform.** For $f:\{0,1\}^n\to\mathbb R$, the function of frequencies
--   $$
--   p\mapsto\hat f(p)=\mathbb E_\varepsilon f(\varepsilon)w_p(\varepsilon) .
--   $$
--   By Parseval it satisfies $\mathbb E_p|\hat f(p)|^2=2^{-n}\|f\|_{L_2}^2$, and it is an isometry up to normalization.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ScalarWalsh.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ScalarWalsh.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [NormedSpace ℝ X] in
@[simp] theorem cubeL2_nonneg {n : ℕ} (f : Cube n → X) : 0 ≤ cubeL2 X f :=
  Real.sqrt_nonneg _

omit [NormedSpace ℝ X] in
theorem cubeL2_sq {n : ℕ} (f : Cube n → X) :
    cubeL2 X f ^ 2 = average (fun ε => ‖f ε‖ ^ 2) := by
  apply Real.sq_sqrt
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

def scalarWalsh {n : ℕ} (f : Cube n → ℝ) : Cube n → ℝ := fourier f

end Cotype

end

end OAI


