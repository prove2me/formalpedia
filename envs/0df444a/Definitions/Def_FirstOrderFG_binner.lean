-- Prove2me | Definitions.Def_FirstOrderFG_binner
-- name    : FirstOrderFG_binner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:47:27.729365+00:00
-- url     : https://prove2.me/theorems/8ba86302-70f0-42bc-8760-80ad7618dbbd
-- title:
--   Inner product $\langle x,g\rangle$ on $\mathbb R^{\mathcal B}$
-- statement:
--   For $x,g\in\mathbb R^{\mathcal B}$, $\langle x,g\rangle=\sum_{b\in\mathcal B}x_b g_b$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, §2, p.3; Algorithm 2, line 14, p.10; Algorithm 4, line 11, p.32

import Mathlib
import Definitions.Def_FirstOrderFG_Bset

namespace FirstOrderFG

/-- **The inner product `⟨x, g⟩` on `ℝ^B`.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, §2, p.3 (inner product) and §4, e.g.
Line 14 and `Z̃_t = ⟨x_t, g̃_t⟩` (Algorithm 4, line 11, p.32). -/
def binner {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (x g : Option (Fin K) → ℝ) : ℝ :=
  ∑ b ∈ Bset E, x b * g b

end FirstOrderFG


