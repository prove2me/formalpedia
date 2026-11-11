-- Prove2me | Definitions.Def_ARGFContract_Hardness_ARGF
-- name    : ARGFContract_Hardness_ARGF
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:43:40.803209+00:00
-- url     : https://prove2.me/theorems/5b712e6c-acc9-4556-92a8-5954bb3f632b
-- title:
--   Augmented rank-ordered gain functions (Definition 2.1)
-- statement:
--   Let $E=\{0,\ldots,n-1\}$, let $p_i\in\mathbb R$ be competencies, and let $f:2^E\to\mathbb R$. The mathematical **ARGF** predicate requires anchoring, boundedness, subadditivity and competency dominance:
--
--   $$f(\varnothing)=0,\qquad 0\le f(S)\le1,\qquad f(A\cup B)\le f(A)+f(B),$$
--   $$i,j\notin S,\ p_i\ge p_j\quad\Longrightarrow\quad f(S\cup\{i\})\ge f(S\cup\{j\}).$$
--
--   The uniform polynomial evaluator in `IsInstanceFamily` supplies item (3) separately. No bound on competencies, monotonicity under inclusion, or singleton consistency is added. This predicate is shared by every instance and the verification of the reduction.
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, Optimal Contract Design for Rank Ordered Gain Functions with Modular Costs, STOC 2027 submission #348 (October 2026), Definition 2.1 (1),(2),(4),(5), pp. 6–7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/348.pdf

import Definitions.Def_SubmodOrder_Subadditive

namespace ARGFContract.Hardness

/-- Definition 2.1, pp. 6–7. Item (3) is the separate family evaluator condition.
No monotonicity, singleton consistency, or bound on competencies is assumed. -/
def IsARGF {n : ℕ} (p : Fin n → ℝ) (f : Finset (Fin n) → ℝ) : Prop :=
  f ∅ = 0 ∧ (∀ S, 0 ≤ f S ∧ f S ≤ 1) ∧ SubmodOrder.Subadditive f ∧
  ∀ i j S, i ∉ S → j ∉ S → p j ≤ p i → f (insert j S) ≤ f (insert i S)

end ARGFContract.Hardness


