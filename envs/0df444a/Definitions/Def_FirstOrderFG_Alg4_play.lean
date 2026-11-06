-- Prove2me | Definitions.Def_FirstOrderFG_Alg4_play
-- name    : FirstOrderFG_Alg4_play
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:57:30.24041+00:00
-- url     : https://prove2.me/theorems/d87d2951-b2f0-4b91-8efc-fac7d6caf221
-- title:
--   Law of the arm played by Algorithm 4
-- statement:
--   After a history $h$, round $|h|+1$ draws $I\sim\pi_t$ of the instance that survives lines 4–9.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 4, line 10, p.32; Eq. (18), p.8

import Mathlib
import Definitions.Def_FirstOrderFG_Alg4_run
import Definitions.Def_FirstOrderFG_Alg4_prepare
import Definitions.Def_FirstOrderFG_piDist
import Definitions.Def_FirstOrderFG_Alg2_qOf

namespace FirstOrderFG

/-- **The law of the arm played by Algorithm 4.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 4, line 10, p.32, with
Algorithm 2, lines 7–9, and Eq. (18), p.8: after the history `h`, round `|h| + 1` draws
`I ∼ π_t` of the instance surviving lines 4–9. -/
noncomputable def Alg4.play {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (ℓ : ℕ → Fin K → ℝ)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) (h : List (Fin K)) : Fin K → ℝ :=
  piDist E (Alg4.prepare E T q₀ (Alg4.run E T ℓ q₀ h)).inst.x
    (Alg2.qOf E T q₀ (Alg4.prepare E T q₀ (Alg4.run E T ℓ q₀ h)).inst)

end FirstOrderFG


