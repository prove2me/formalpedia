-- Prove2me | Definitions.Def_WildeQIT_IsMarkovChain
-- name    : WildeQIT_IsMarkovChain
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T05:41:47.411721+00:00
-- url     : https://prove2.me/theorems/1f8cd02a-6eb3-4e64-956b-ed6005114491
-- title:
--   Markov chain $X\to Y\to Z$ of three random variables (§10.7.2)
-- statement:
--   Three discrete random variables $X, Y, Z$ with joint distribution $p_{XYZ}$ on finite alphabets form a **Markov chain** $X\to Y\to Z$ when $Z$ depends on $X$ only through $Y$: $p_{XYZ}(x,y,z)=p_X(x)\,p_{Y|X}(y|x)\,p_{Z|Y}(z|y)$, equivalently $p_{Z|XY}(z|x,y)=p_{Z|Y}(z|y)$ wherever the conditionals are defined. Multiplying through by $p_Y(y)$ gives the division-free condition used here:
--
--   $$
--   p_{XYZ}(x,y,z)\;p_Y(y) \;=\; p_{XY}(x,y)\;p_{YZ}(y,z)\qquad\text{for all }x,y,z,
--   $$
--
--   where $p_{XY}(x,y)=\sum_z p_{XYZ}(x,y,z)$, $p_{YZ}(y,z)=\sum_x p_{XYZ}(x,y,z)$ and $p_Y(y)=\sum_{x,z}p_{XYZ}(x,y,z)$. When $p_Y(y)=0$ both sides vanish, so the condition is exactly the conditional one at every $y$ of positive probability.
--
--   Markov chains are the hypothesis of the data-processing inequality (Theorem 10.7.2), Corollary 10.7.1 and Fano's inequality (Theorem 10.7.3).
--
--   **Formalization Note.** `WildeQIT.FinDist.IsMarkovChain p` for `p : WildeQIT.FinDist (α × β × γ)` (components $X,Y,Z$ in this order, the middle one screening) is `∀ x y z, p.prob (x, y, z) * p.margXY.snd.prob y = p.margXY.prob (x, y) * p.margYZ.prob (y, z)`.
-- source:
--   Wilde, Quantum Information Theory 2nd ed. (Cambridge 2017; arXiv:1106.1445v8), Theorem 10.7.2, §Data-Processing Inequality, LaTeX label thm-ie:data-process (roster-items.csv line 16982); the notion 'X → Y → Z form a Markov chain' used in its statement (stated in division-free form).

import Definitions.Def_WildeQIT_FinDist

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §10.7.2 (Data-Processing Inequality):
three random variables `X, Y, Z` form a Markov chain `X → Y → Z` when
`p_{XYZ}(x,y,z) = p_X(x) p_{Y|X}(y|x) p_{Z|Y}(z|y)`, i.e. `Z` depends on `X` only through `Y`.
Multiplying through by `p_Y(y)` gives the division-free form used here:
`p_{XYZ}(x,y,z) · p_Y(y) = p_{XY}(x,y) · p_{YZ}(y,z)` for all `x, y, z`.
-/

namespace WildeQIT

/-- `X → Y → Z` is a Markov chain (the middle component screens off the first from the last):
`p(x,y,z) · p_Y(y) = p_{XY}(x,y) · p_{YZ}(y,z)` for all `x, y, z`. -/
def FinDist.IsMarkovChain {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinDist (α × β × γ)) : Prop :=
  ∀ x y z, p.prob (x, y, z) * p.margXY.snd.prob y = p.margXY.prob (x, y) * p.margYZ.prob (y, z)

end WildeQIT


