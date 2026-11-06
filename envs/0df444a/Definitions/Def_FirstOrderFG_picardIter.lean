-- Prove2me | Definitions.Def_FirstOrderFG_picardIter
-- name    : FirstOrderFG_picardIter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:47:49.280804+00:00
-- url     : https://prove2.me/theorems/0d06b629-15c8-4ec1-a13e-dcdc834c13f5
-- title:
--   Picard iterates $q^{(n)}$
-- statement:
--   Given a start $q^{(0)}$, the Picard iterates of $F_{p,\gamma}$ are $q^{(n+1)}=F_{p,\gamma}(q^{(n)})$, i.e. $q^{(n)}=F_{p,\gamma}^{\,n}(q^{(0)})$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Proposition A.3, p.20

import Mathlib
import Definitions.Def_FirstOrderFG_Fmap

namespace FirstOrderFG

/-- **Picard iterates `q^{(n)}`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Proposition A.3, p.20: "Fix any
`q^{(0)} ∈ int(∆(V_self))` and set `q^{(n+1)} = F_{p,γ}(q^{(n)})`." -/
noncomputable def picardIter {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ)
    (p : Fin K → ℝ) (γ : ℝ) (q0 : Fin K → ℝ) (n : ℕ) : Fin K → ℝ :=
  (Fmap E T p γ)^[n] q0

end FirstOrderFG


