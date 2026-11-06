-- Prove2me | Definitions.Def_FirstOrderFG_psi
-- name    : FirstOrderFG_psi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:27.729196+00:00
-- url     : https://prove2.me/theorems/fbcbc448-f8fe-435e-b2d1-544233329448
-- title:
--   The multiplier $\psi_\gamma$
-- statement:
--   For $K$ arms, horizon $T$ and a parameter $\gamma>0$, the multiplier is
--   $$
--   \psi_\gamma(v)=\frac{v+1/(KT)}{v+\gamma}.
--   $$
--   In Algorithm 2 the parameter is $\gamma=\eta_t/x_{t,0}$ (Eq. (22)).
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Proposition A.3, p.20; Eq. (22), p.9

import Mathlib

namespace FirstOrderFG

/-- **The multiplier `ψ_γ`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Proposition A.3, p.20:
`ψ_γ(v) ≜ (v + 1/(KT)) / (v + γ)`; Eq. (22), p.9, is the case `γ = η_t / x_{t,0}`. -/
noncomputable def psi (K T : ℕ) (γ v : ℝ) : ℝ :=
  (v + 1 / ((K : ℝ) * T)) / (v + γ)

end FirstOrderFG


