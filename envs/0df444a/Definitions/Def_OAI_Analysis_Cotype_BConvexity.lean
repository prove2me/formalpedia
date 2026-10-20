-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_BConvexity
-- name    : OAI_Analysis_Cotype_BConvexity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:43:07.253233+00:00
-- url     : https://prove2.me/theorems/62f4771d-7626-4492-b74a-36b28f6537a5
-- title:
--   B-convexity
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections.
--
--   1. **B-convex spaces.** $X$ is B-convex if for some $n\ge1$ and $\delta>0$, every $x_1,\dots,x_n$ in the unit ball has a choice of signs with
--   $$
--   \Bigl\|\sum_i\varepsilon_ix_i\Bigr\|\le n-\delta .
--   $$
--   By Beck's and Pisier's theorems this is equivalent to nontrivial type and to not containing $\ell_1^n$ uniformly.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/BConvexity.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/BConvexity.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def BConvex (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ x : Fin n → X,
    (∀ i, ‖x i‖ ≤ 1) → ∃ ε : Cube n, ‖rademacherSum X x ε‖ ≤ (n : ℝ) - δ

end Cotype

end

end OAI


