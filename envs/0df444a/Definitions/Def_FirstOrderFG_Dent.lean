-- Prove2me | Definitions.Def_FirstOrderFG_Dent
-- name    : FirstOrderFG_Dent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:45:44.575556+00:00
-- url     : https://prove2.me/theorems/c4217b69-294b-479f-acee-0827a6885171
-- title:
--   Entropy Bregman divergence $D_h$
-- statement:
--   For $z,y$ with positive coordinates on $V_{\mathrm{self}}$,
--   $$
--   D_h(z,y)=\sum_{i\in V_{\mathrm{self}}}\Big(z_i\ln\frac{z_i}{y_i}-z_i+y_i\Big),
--   $$
--   the Bregman divergence of the negative entropy $h(p)=\sum_j p_j\ln p_j$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, App. B.1, p.22; §3, p.4

import Mathlib
import Definitions.Def_FirstOrderFG_Vself

namespace FirstOrderFG

/-- **The entropy Bregman divergence `D_h` on `∆(V_self)`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, App. B.1, p.22: "Recall that
`D_h(z, y) = ∑_{i ∈ V_self} (z_i ln(z_i/y_i) − z_i + y_i)`", the Bregman divergence of the negative
entropy `h(p) = ∑ p_j ln p_j` (§3, p.4). -/
noncomputable def Dent {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (z y : Fin K → ℝ) : ℝ :=
  ∑ i ∈ Vself E, (z i * Real.log (z i / y i) - z i + y i)

end FirstOrderFG


