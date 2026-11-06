-- Prove2me | Definitions.Def_FirstOrderFG_Pset
-- name    : FirstOrderFG_Pset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:46:04.160231+00:00
-- url     : https://prove2.me/theorems/7ff21fdd-b13d-4ae1-8450-648147d17794
-- title:
--   The clipped base simplex $\mathcal P$
-- statement:
--   With $s=|V_{\mathrm{self}}|$,
--   $$
--   \mathcal P=\big\{p\in\Delta(V_{\mathrm{self}}):\ p_i\ge 1/(sT)\ \text{for all } i\in V_{\mathrm{self}}\big\}.
--   $$
--
--   **Formalization Note** Elements are functions on all arms that vanish off $V_{\mathrm{self}}$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 2, line 2, p.10

import Mathlib
import Definitions.Def_FirstOrderFG_Vself

namespace FirstOrderFG

/-- **The clipped base simplex `𝒫`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 2, line 2, p.10:
`𝒫 ≜ {p ∈ ∆(V_self) : p_i ≥ 1/(sT) for all i ∈ V_self}`, `s = |V_self|`.

**Formalization Note.** Elements are functions `Fin K → ℝ` vanishing off `V_self`. -/
def Pset {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) : Set (Fin K → ℝ) :=
  {p | (∀ i ∈ Vself E, 1 / (((Vself E).card : ℝ) * T) ≤ p i) ∧ (∀ i, i ∉ Vself E → p i = 0)
      ∧ ∑ i ∈ Vself E, p i = 1}

end FirstOrderFG


