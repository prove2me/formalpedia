-- Prove2me | Definitions.Def_FirstOrderFG_Xset
-- name    : FirstOrderFG_Xset
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:47:25.056222+00:00
-- url     : https://prove2.me/theorems/9bd37742-f07d-4934-804f-a375b5ae4ec9
-- title:
--   The clipped master simplex $\mathcal X$
-- statement:
--   With $M=|\mathcal B|$,
--   $$
--   \mathcal X=\big\{x\in\Delta(\mathcal B):\ x_b\ge 1/(2MT)\ \text{for all } b\in\mathcal B\big\}.
--   $$
--
--   **Formalization Note** Elements are functions on `Option (Fin K)` that vanish off $\mathcal B$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 2, line 2, p.10

import Mathlib
import Definitions.Def_FirstOrderFG_Bset

namespace FirstOrderFG

/-- **The clipped master simplex `𝒳`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 2, line 2, p.10:
`𝒳 ≜ {x ∈ ∆(B) : x_b ≥ 1/(2MT) for all b ∈ B}`, `M = |B|`.

**Formalization Note.** Elements are functions `Option (Fin K) → ℝ` vanishing off `B`. -/
def Xset {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) :
    Set (Option (Fin K) → ℝ) :=
  {x | (∀ b ∈ Bset E, 1 / (2 * ((Bset E).card : ℝ) * T) ≤ x b) ∧ (∀ b, b ∉ Bset E → x b = 0)
      ∧ ∑ b ∈ Bset E, x b = 1}

end FirstOrderFG


