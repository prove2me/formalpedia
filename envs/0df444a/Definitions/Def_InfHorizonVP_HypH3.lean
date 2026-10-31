-- Prove2me | Definitions.Def_InfHorizonVP_HypH3
-- name    : InfHorizonVP_HypH3
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:21.851282+00:00
-- url     : https://prove2.me/theorems/d96b7d20-ccc0-454a-9085-086a2a4d1568
-- title:
--   Hypothesis (H3): Lipschitz integrand with moduli $l_1,l_2$
-- statement:
--   **(H3)** with moduli $l_1,l_2$: $l_1:\mathbb R_+\to\mathbb R_+$ is integrable, $l_2:\mathbb R_+\to\mathbb R_+$ is locally bounded and integrable, and for every $t\ge0$ and $(x,y),(x',y')\in E\times E$,
--   $$
--   |L(t,0,0)|\le l_1(t),\qquad |L(t,x,y)-L(t,x',y')|\le l_1(t)\|x-x'\|+l_2(t)\|y-y'\| .
--   $$
--
--   **Formalization Note** The moduli are parameters; the same $l_1,l_2$ enter (H7).
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §3.1, p.8, (H3)

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Hypothesis (H3), with the moduli `l₁`, `l₂`.**
Frankowska, Sagara, arXiv:1801.00400v3, §3.1, p.8: "(H3) There exist an integrable function
l1 : R+ → R+ and a locally bounded, integrable function l2 : R+ → R+ such that |L(t, 0, 0)| ≤ l1(t)
and |L(t, x, y) − L(t, x′, y′)| ≤ l1(t)‖x − x′‖ + l2(t)‖y − y′‖ for every t ∈ R+ and every
(x, y), (x′, y′) ∈ E × E."

**Formalization Note.** The moduli are arguments: the existential "there exist l₁, l₂" becomes a
universally quantified hypothesis of every theorem, and the same `l₁, l₂` enter (H7). "Integrable"
is Lebesgue integrability on `[0, ∞)`; "locally bounded" is boundedness on every `[0, T]`;
`R+`-valued is nonnegativity on `[0, ∞)`. -/
def HypH3 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ → E → E → ℝ) (l₁ l₂ : ℝ → ℝ) : Prop :=
  IntegrableOn l₁ (Ici 0) ∧ IntegrableOn l₂ (Ici 0) ∧
  (∀ T, BddAbove (l₂ '' Icc 0 T)) ∧
  (∀ t, 0 ≤ t → 0 ≤ l₁ t ∧ 0 ≤ l₂ t) ∧
  (∀ t, 0 ≤ t → |L t 0 0| ≤ l₁ t) ∧
  ∀ t, 0 ≤ t → ∀ x y x' y' : E,
    |L t x y - L t x' y'| ≤ l₁ t * ‖x - x'‖ + l₂ t * ‖y - y'‖

end InfHorizonVP


