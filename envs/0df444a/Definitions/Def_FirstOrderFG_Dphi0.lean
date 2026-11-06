-- Prove2me | Definitions.Def_FirstOrderFG_Dphi0
-- name    : FirstOrderFG_Dphi0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:23.871545+00:00
-- url     : https://prove2.me/theorems/f6257ba5-2a84-41ce-bb7e-727e6a525a74
-- title:
--   Bregman divergence $D_{\varphi_0}$ of $\varphi_0(z)=-\ln z$
-- statement:
--   For $y,p>0$,
--   $$
--   D_{\varphi_0}(y,p)=\frac yp-1-\ln\frac yp ,
--   $$
--   the Bregman divergence of the log barrier $\varphi_0(z)=-\ln z$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, App. B.2, p.26 (φ₀ and proof of Lemma B.2)

import Mathlib

namespace FirstOrderFG

/-- **The Bregman divergence of `φ₀(z) = −ln z`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, App. B.2, p.26 (`φ₀(z) ≜ −ln z`) and
proof of Lemma B.2, p.26: `D_{φ₀}(y, p) = y/p − 1 − ln(y/p)`. -/
noncomputable def Dphi0 (y p : ℝ) : ℝ :=
  y / p - 1 - Real.log (y / p)

end FirstOrderFG


