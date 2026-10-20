-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_UniformL1
-- name    : OAI_Analysis_Cotype_UniformL1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:39:29.54938+00:00
-- url     : https://prove2.me/theorems/aed7f77f-10c9-4036-8f78-eba2dbc87d76
-- title:
--   Uniformly containing l1^n
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections.
--
--   1. **$\ell_1$-families.** Vectors $x_i$, $\|x_i\|\le1$, with
--   $$
--   c\sum_i|a_i|\le\Bigl\|\sum_ia_ix_i\Bigr\|\qquad\text{for all scalars }a_i .
--   $$
--   2. **Uniform $\ell_1$.** $X$ contains $\ell_1^n$ uniformly if a single $c>0$ admits such families of every length $n$. By Pisier's theorem this is the failure of nontrivial type, and it is incompatible with K-convexity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/UniformL1.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/UniformL1.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def L1Family {ι : Type*} [Fintype ι] (x : ι → X) (c : ℝ) : Prop :=
  (∀ i, ‖x i‖ ≤ 1) ∧ ∀ a : ι → ℝ, c * ∑ i, |a i| ≤ ‖∑ i, a i • x i‖

def UniformL1 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∃ x : Fin n → X, L1Family x c

end Cotype

end

end OAI


