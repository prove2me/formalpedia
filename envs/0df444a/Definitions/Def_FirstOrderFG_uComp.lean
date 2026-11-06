-- Prove2me | Definitions.Def_FirstOrderFG_uComp
-- name    : FirstOrderFG_uComp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:47:34.034169+00:00
-- url     : https://prove2.me/theorems/719851bc-6099-4f17-bf95-35ffba7c54c8
-- title:
--   Smoothed comparator $u^{(b)}$
-- statement:
--   For a master action $b\in\mathcal B$,
--   $$
--   u^{(b)}=\Big(1-\frac{M-1}{2MT}\Big)e_b+\frac1{2MT}\sum_{j\in\mathcal B\setminus\{b\}}e_j\in\mathcal X .
--   $$
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma B.4, p.28

import Mathlib
import Definitions.Def_FirstOrderFG_Bset

namespace FirstOrderFG

/-- **The smoothed comparator `u^{(b)}`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Lemma B.4, p.28:
`u^{(b)} ≜ (1 − (M−1)/(2MT)) e_b + (1/(2MT)) ∑_{j ∈ B∖{b}} e_j ∈ 𝒳`. -/
noncomputable def uComp {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ)
    (b : Option (Fin K)) : Option (Fin K) → ℝ :=
  fun j => if j ∈ Bset E then
    (if j = b then 1 - (((Bset E).card : ℝ) - 1) / (2 * (Bset E).card * T)
      else 1 / (2 * ((Bset E).card : ℝ) * T))
  else 0

end FirstOrderFG


