-- Prove2me | Definitions.Def_HuangYin_Buys
-- name    : HuangYin_Buys
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:35:18.864063+00:00
-- url     : https://prove2.me/theorems/0827fa9a-14e3-49c5-ad9a-dba64d3a87d1
-- title:
--   The purchase rule (1)
-- statement:
--   A customer whose estimate of receiving product $H$ is $\tilde\xi$ buys the opaque product at price $p$ if and only if
--
--   $$\tilde\xi\, v_H + (1-\tilde\xi)\, v_L \ge p. \qquad (1)$$
--
--   With one anecdote and $\xi_0=0$, a customer with an $L$-anecdote buys iff $p\le v_L$, and a customer with an $H$-anecdote buys iff $p\le v_{HL}$.
--
--   **Formalization Note** The inequality is weak, as printed: at the price $v_{HL}$ the customers with an $H$-anecdote buy. A decidability instance lets the demand branch on the rule.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), equation (1), p. 9

import Mathlib
import Definitions.Def_HuangYin_Params
import Definitions.Def_HuangYin_estimate

namespace HuangYin

/-- **The purchase rule** (equation (1), p. 9).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), p. 9: "customer i purchases the product in period t if and only if
ξ̃ti vH + (1 − ξ̃ti) vL ≥ pt.  (1)"

`Buys P p b` holds when a customer whose single anecdote is `H` (if `b`) or `L` (if `¬ b`), and
whose estimate is therefore `estimate b`, buys the opaque product at price `p`.

**Formalization Note.** The inequality is weak, as printed in (1): at the price `p = vHL` the
customers with an `H`-anecdote buy. The `Decidable` instance only lets `demand` branch on it. -/
def Buys (P : Params) (p : ℝ) (b : Bool) : Prop :=
  p ≤ estimate b * P.vH + (1 - estimate b) * P.vL

noncomputable instance (P : Params) (p : ℝ) (b : Bool) : Decidable (Buys P p b) := by
  unfold Buys; infer_instance

end HuangYin


