-- Prove2me | Definitions.Def_HedgeInv_Value_Model
-- name    : HedgeInv_Value_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T14:17:49.106205+00:00
-- url     : https://prove2.me/theorems/99f39eb5-b764-4e48-a97c-f1b84695df33
-- title:
--   §3 and §3.2, pp. 107–111 — the unhedged payoff (11), the hedged newsvendor payoff (14) and its expected utility
-- statement:
--   This file fixes the model of Gaur and Seshadri's risk-averse hedged newsvendor, in the scaled units of their equation (11).
--
--   A firm orders $I$ units of an item now; demand $T$ periods later is $D = a + bS_T + \varepsilon'$, where $S_T$ is the time-$T$ price of a traded asset and $\varepsilon'$ is a forecast error independent of $S_T$. Write $\varepsilon = \varepsilon'/b$. After scaling all cash flows by $1/((p-s)b)$, with $p$ the selling price, $s$ the salvage value and $c$ the unit cost, the parameters are the scaled initial wealth $W$, the demand intercept $a$, the slope $b$, and the scaled unit cost $c_1 = (ce^{rT}-s)/((p-s)b)$.
--
--   1. The **unhedged wealth** at $S_T = s$, $\varepsilon = e$ is
--   $$W + \Pi_U(I) = W + \min\{s + e,\ (I-a)/b\} - c_1 I.$$
--   2. The firm shorts an amount $\alpha$ of a portfolio whose time-$T$ payoff is $X_T = \varphi(S_T)$ and whose time-0 price $X_0$ grows to the forward value $x_{0r} = X_0e^{rT}$. The **hedged wealth** is
--   $$W + \Pi_H(I,\alpha) = W + \min\{s + e,\ (I-a)/b\} - c_1 I - \alpha\,\varphi(s) + \alpha\,x_{0r}.$$
--   3. For a utility function $u:\mathbb R\to\mathbb R$, a law $\nu$ of $S_T$ and a law $G$ of $\varepsilon$, the **expected utility** of the hedged position is
--   $$\mathbb E[u(\Pi_H(I,\alpha))] = \int_{\mathbb R\times\mathbb R} u\big(W + \min\{s+e,(I-a)/b\} - c_1 I - \alpha\varphi(s) + \alpha x_{0r}\big)\,d(\nu\otimes G)(s,e).$$
--
--   At $\alpha = 0$ the hedged wealth equals the unhedged one. These objects are the common setting of Proposition 5 and its proof.
--
--   Items 2 and 3 (`hedgedPayoff`, `expUtil`) are the shared definitions of `HedgeInv.Order.Model`, which this file imports; this file itself adds the unhedged wealth $W + \Pi_U(I)$ (`unhedgedPayoff`) and the identity $\Pi_H(I,0) = \Pi_U(I)$.
--
--   **Formalization Note** Independence of $S_T$ and $\varepsilon$ is encoded by integrating against the product measure $\nu\otimes G$ on $\mathbb R\times\mathbb R$. The expectation is a Bochner integral, so it is $0$ when the integrand is not integrable; every theorem that uses it carries the integrability it needs. The scaled constants $W$ and $c_1$ are taken as primitive real parameters.
-- source:
--   Gaur & Seshadri, Hedging Inventory Risk Through Market Instruments, Manuf. Serv. Oper. Manag. 7(2) (2005), pp. 107–111, §3 demand model, (11), (12), (14)

import Mathlib
import Definitions.Def_HedgeInv_Order_Model

namespace HedgeInv.Value

open MeasureTheory

/-- The unhedged scaled newsvendor wealth `W + Π_U(I)` of (11) (Gaur & Seshadri 2005, p. 110) at
`S_T = s`, `ε = e`: `W + min (s + e) ((I - a) / b) - c₁ * I`. -/
noncomputable def unhedgedPayoff (W a b c₁ I s e : ℝ) : ℝ :=
  W + min (s + e) ((I - a) / b) - c₁ * I

/-- At `α = 0` the hedged payoff is the unhedged one. -/
@[simp] theorem hedgedPayoff_zero (W a b c₁ : ℝ) (φ : ℝ → ℝ) (x0r I s e : ℝ) :
    HedgeInv.Order.hedgedPayoff W a b c₁ φ x0r I 0 s e = unhedgedPayoff W a b c₁ I s e := by
  simp [HedgeInv.Order.hedgedPayoff, unhedgedPayoff]

end HedgeInv.Value


