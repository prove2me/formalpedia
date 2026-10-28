-- Prove2me | Definitions.Def_WildeQIT_condEntropy
-- name    : WildeQIT_condEntropy
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T03:50:34.155611+00:00
-- url     : https://prove2.me/theorems/dd482f8f-fb1a-49e8-a55c-61e25ba1c42f
-- title:
--   Conditional entropy $H(X|Y)$ (Definition 10.2.1)
-- statement:
--   **Definition 10.2.1 (Conditional entropy).** Let $X$ and $Y$ be discrete random variables with joint probability distribution $p_{XY}(x,y)$ on the finite alphabet $\mathcal{X}\times\mathcal{Y}$. The conditional entropy $H(X|Y)$ is the expected conditional information content, where the expectation is with respect to both $X$ and $Y$:
--
--   $$
--   H(X|Y) \equiv \mathbb{E}_{XY}\{i(X|Y)\} = \sum_y p_Y(y)\,H(X|Y=y) = -\sum_{x,y} p_{XY}(x,y)\,\log\bigl(p_{X|Y}(x|y)\bigr),
--   $$
--
--   where $p_Y(y)=\sum_x p_{XY}(x,y)$ is the marginal of $Y$ and $p_{X|Y}(x|y)=p_{XY}(x,y)/p_Y(y)$ is the conditional distribution of $X$ given $Y=y$. The logarithm is base $2$.
--
--   The conditional entropy measures the uncertainty that remains about $X$ once $Y$ is known. It is the building block of the joint entropy chain rule and of the mutual information $I(X;Y)=H(X)-H(X|Y)$.
--
--   **Formalization Note.** `WildeQIT.condEntropy p`, for `p : WildeQIT.FinDist (α × β)` the joint distribution of the pair $(X,Y)$, is the last expression above: $-\sum_{x}\sum_{y} p(x,y)\,\log_2\bigl(p(x,y)/p_Y(y)\bigr)$. It is the entropy of the **first** component conditioned on the **second**; $H(Y|X)$ is obtained by applying it to the swapped joint distribution `p.swap`. When $p_{XY}(x,y)=0$ the term vanishes (convention $0\log 0=0$, automatic since `Real.logb 2 0 = 0`); when $p_Y(y)=0$ every $p_{XY}(x,y)$ with that $y$ is zero as well, so the real-division convention $a/0=0$ never affects the value.
-- source:
--   Wilde, Quantum Information Theory, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), Chapter 10 (Classical Information and Entropy), §Conditional Entropy, Definition 10.2.1, LaTeX label eq-ie:class-cond-ent (book source roster-items.csv line 16427); last displayed form H(X|Y) = −∑_{x,y} p_{XY}(x,y) log p_{X|Y}(x|y).

import Definitions.Def_WildeQIT_FinDist
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Definition 10.2.1 (Conditional entropy):
for discrete random variables `X, Y` with joint distribution `p_{XY}`,
`H(X|Y) ≡ -∑_{x,y} p_{XY}(x,y) log p_{X|Y}(x|y)`, where `p_{X|Y}(x|y) = p_{XY}(x,y)/p_Y(y)`.
-/

namespace WildeQIT

/-- Definition 10.2.1. The conditional entropy `H(X|Y)` of the first component given the
second, for a joint distribution `p` on `α × β`:
`H(X|Y) = -∑_{x,y} p(x,y) log₂ ( p(x,y) / p_Y(y) )`, in bits.
A term with `p(x,y) = 0` contributes `0` (convention `0 log 0 = 0`); when `p_Y(y) = 0`
every `p(x,y)` with that `y` vanishes, so the (junk) quotient `p(x,y)/0` never contributes. -/
noncomputable def condEntropy {α β : Type} [Fintype α] [Fintype β] (p : FinDist (α × β)) : ℝ :=
  -∑ x, ∑ y, p.prob (x, y) * Real.logb 2 (p.prob (x, y) / p.snd.prob y)

end WildeQIT


