-- Prove2me | Definitions.Def_SimpleMenus_pay
-- name    : SimpleMenus_pay
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:55.040281+00:00
-- url     : https://prove2.me/theorems/f22b0991-790c-4670-b96b-31f9a970794e
-- title:
--   Expected payment $t(w)$ of an $n$-level pricing mechanism
-- statement:
--   Fix price levels $v_1\le\dots\le v_n$ and probabilities $x_1,\dots,x_n$. The randomized pricing mechanism posts price $v_l$ with probability $x_l$, so its price density is $\pi=\sum_l x_l\,\delta(\cdot-v_l)$. A buyer with valuation $w$ pays in expectation
--
--   $$t(w)=\int_0^w \pi(u)\,u\,du=\sum_{l\,:\,v_l\le w} x_l\,v_l .$$
--
--   The payment is a nondecreasing step function of $w$; it is the right-hand side of every constraint of Problems (3), (4) and the intermediate programs of the proof of Theorem 1.
--
--   **Formalization Note** The Dirac integral is written in closed form. The atom at $w$ is included ($v_l\le w$): a buyer whose valuation equals the posted price buys, as in the half-open cells $[v_j,v_{j+1})$ of p.ec8.
-- source:
--   Wang, The Power of Simple Menus in Robust Selling Mechanisms, arXiv:2310.17392v3, §2, p.9 (definition of t(v)), and proof of Theorem 1, p.ec8 (PDF p.42), the step form

import Mathlib

namespace SimpleMenus

/-- The expected payment `t(w) = ∫_0^w π(u) u du` of a buyer with valuation `w` under the
`n`-level pricing mechanism `π = Σ_l x_l δ(· − v_l)` (Wang, *The Power of Simple Menus in Robust Selling Mechanisms*, arXiv:2310.17392v3, §2, p.9; the step form is the
display on p.ec8 = PDF p.42: `= Σ_{l=1}^j x_l v_l` for `w ∈ [v_j, v_{j+1})`).

Formalization Note: the Dirac density is integrated in closed form. The atom at `w` itself is
included (`v l ≤ w`): a buyer whose valuation equals the posted price buys (footnote 1, p.2, and
the half-open cells `[v_j, v_{j+1})` of p.ec8). -/
noncomputable def pay {n : ℕ} (v x : Fin n → ℝ) (w : ℝ) : ℝ :=
  ∑ l, if v l ≤ w then x l * v l else 0

end SimpleMenus


