-- Prove2me | Definitions.Def_FirstOrderFG_Dphi
-- name    : FirstOrderFG_Dphi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:27.611802+00:00
-- url     : https://prove2.me/theorems/5dcdc8a9-0711-4561-a79a-b3fe7257cb2e
-- title:
--   Bregman divergence $D_\varphi$ of $\varphi(z)=z\ln z-\ln(1-z)$
-- statement:
--   For $y,p\in(0,1)$,
--   $$
--   D_\varphi(y,p)=\Big(y\ln\frac yp-y+p\Big)+\Big(\frac{p-y}{1-p}-\ln\frac{1-y}{1-p}\Big),
--   $$
--   the Bregman divergence of $\varphi(z)=z\ln z-\ln(1-z)$ (entropy plus complement barrier).
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, App. B.2, pp.26–27 (φ and proof of Lemma B.2)

import Mathlib

namespace FirstOrderFG

/-- **The Bregman divergence of `φ(z) = z ln z − ln(1 − z)`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, App. B.2, p.26
(`φ(z) ≜ z ln z − ln(1 − z)`) and proof of Lemma B.2, p.27:
`D_φ(y, p) = (y ln(y/p) − y + p) + ((p − y)/(1 − p) − ln((1 − y)/(1 − p)))`. -/
noncomputable def Dphi (y p : ℝ) : ℝ :=
  (y * Real.log (y / p) - y + p) + ((p - y) / (1 - p) - Real.log ((1 - y) / (1 - p)))

end FirstOrderFG


