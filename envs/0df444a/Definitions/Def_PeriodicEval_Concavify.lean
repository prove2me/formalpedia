-- Prove2me | Definitions.Def_PeriodicEval_Concavify
-- name    : PeriodicEval_Concavify
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:21.900173+00:00
-- url     : https://prove2.me/theorems/99d24807-0dcb-45cc-9e44-bbd0c894c997
-- title:
--   Smallest concave majorant on $[0,\infty)$ and maximizer selections
-- statement:
--   For a function $g$ on $[0,\infty)$, its **smallest concave majorant** is
--
--   $$\bar g(y):=\inf\{f(y): f \text{ concave on }[0,\infty),\ f\ge g\text{ on }[0,\infty)\},\qquad y\ge0.$$
--
--   For $g=G_a$ this is the function $\bar G_a$ of the paper. For a function $f$ on $[0,\infty)$, a map $y:(0,\infty)\to[0,\infty)$ is a **maximizer selection** if, for every $q>0$, $y(q)$ maximizes $z\mapsto f(z)-qz$ over $z\ge0$:
--
--   $$f(z)-qz\le f(y(q))-q\,y(q)\qquad\text{for all }z\ge0.$$
--
--   The paper writes $y^*_f(q):=\arg\max_{y\ge0}(f(y)-qy)$ and $y^*_a:=y^*_{\bar G_a}$; a maximizer selection is any choice of this argmax when it is not unique.
--
--   **Formalization Note** The infimum is the real infimum over the family of concave majorants. It is a genuine infimum at every $y\ge0$ whenever $g$ has some concave majorant on $[0,\infty)$; every $G_a$ does, being bounded by an affine function there. Values at $y<0$ and $q\le0$ are not used.
-- source:
--   Tse–Zheng, Portfolio Selection, Periodic Evaluations and Risk Taking, SSRN 3971852 (June 20, 2023), Appendix A, p.32 (smallest concave majorant), Lemma 2, p.33, and proof of Proposition 3, p.38 (y*_f(q) := arg max_{y≥0}(f(y) − qy), y*_a = y*_{Ḡ_a})

import Mathlib

namespace PeriodicEval

/-- The smallest concave majorant on `[0, ∞)` of a function `g`: at `y`, the infimum of
`f y` over all functions `f` that are concave on `[0, ∞)` and satisfy `f ≥ g` on `[0, ∞)`.
SSRN 3971852 (June 20, 2023), Appendix A, p.32 ("`Ḡ_a` which is defined as the smallest
concave majorant of `G_a`") and Lemma 2, p.33.

**Formalization Note** The infimum is the real `⨅`. For `y ≥ 0` it is a genuine infimum
whenever `g` has at least one concave majorant on `[0, ∞)` (the family is then nonempty and
bounded below by `g y`); this holds for every `G_a`, which is bounded above by an affine
function on `[0, ∞)`. Values at `y < 0` are not used. -/
noncomputable def concaveMajorant (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  ⨅ f : {f : ℝ → ℝ // ConcaveOn ℝ (Set.Ici 0) f ∧ ∀ z : ℝ, 0 ≤ z → g z ≤ f z}, f.1 y

/-- `y` is a selection of the maximizer of `z ↦ f z − q z` over `z ≥ 0`, for every `q > 0`:
`y q ≥ 0` and `f z − q z ≤ f (y q) − q (y q)` for all `z ≥ 0`. This is the paper's
`y*_f(q) := arg max_{y ≥ 0} (f(y) − qy)`, `q > 0`, SSRN 3971852 (June 20, 2023), proof of
Proposition 3, p.38, written for any choice of maximizer when it is not unique.

**Formalization Note** Only `q > 0` is constrained; `y q` for `q ≤ 0` is irrelevant. -/
def IsArgmaxSelection (f : ℝ → ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ q : ℝ, 0 < q → 0 ≤ y q ∧ ∀ z : ℝ, 0 ≤ z → f z - q * z ≤ f (y q) - q * y q

end PeriodicEval


