-- Prove2me | Definitions.Def_RobustMeanCov_OnePoint_OnePointSupport
-- name    : RobustMeanCov_OnePoint_OnePointSupport
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T21:41:06.904985+00:00
-- url     : https://prove2.me/theorems/3ff1c13a-a08e-4c31-8b00-3521d51ba424
-- title:
--   Definition 3 — the one-point support property
-- statement:
--   A function $u:\mathbb R\to\mathbb R$ has the **one-point support property** if it has the one-point support property with respect to every $(m,s^2)$:
--
--   $$
--   \forall m\in\mathbb R,\ \forall s\ge0:\quad u \text{ has one-point support with respect to } (m,s^2).
--   $$
--
--   Proposition 6 of the paper shows that for such $u$ the robust objective equals $\lim_{p\to0}U(p,x)$ or $\lim_{p\to1}U(p,x)$; Propositions 7 and 8 identify classes of utilities with this property.
--
--   **Formalization Note** "Any $(\mu,\sigma^2)$" is read literally, including $s=0$. There the two-point law is the point mass at $m$, and the condition reduces to a supporting quadratic that touches $u$ at $m$.
-- source:
--   Popescu, Robust Mean-Covariance Solutions for Stochastic Optimization, Oper. Res. 55(1), 2007, p. 103, §3.2, Definition 3 (last sentence)

import Mathlib
import Definitions.Def_RobustMeanCov_OnePoint_OnePointSupportWrt

namespace RobustMeanCov.OnePoint

/-- Definition 3, last sentence (Popescu 2007, p. 103): `u` has the one-point support property
if it has it with respect to every `(m, s²)`, `m ∈ ℝ`, `s ≥ 0`. -/
def OnePointSupport (u : ℝ → ℝ) : Prop :=
  ∀ m s : ℝ, 0 ≤ s → OnePointSupportWrt u m s

end RobustMeanCov.OnePoint


