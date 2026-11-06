-- Prove2me | Definitions.Def_FirstOrderFG_Alg4_run
-- name    : FirstOrderFG_Alg4_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:56:08.709403+00:00
-- url     : https://prove2.me/theorems/dec5b53f-63f5-420f-88a3-51bc5ce3f97d
-- title:
--   State of Algorithm 4 after a history
-- statement:
--   The state of Algorithm 4 before round $|h|+1$ when the arms $h$ were played in rounds $1,\dots,|h|$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 4, p.32

import Mathlib
import Definitions.Def_FirstOrderFG_Alg4_runFrom
import Definitions.Def_FirstOrderFG_Alg4_init

namespace FirstOrderFG

/-- **The state of Algorithm 4 after a history.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 4, p.32.

`Alg4.run E T ℓ q₀ h` is the state before round `|h| + 1` (before its lines 4–9) when the arms
`h` were played in rounds `1, …, |h|`. -/
noncomputable def Alg4.run {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (ℓ : ℕ → Fin K → ℝ)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) (h : List (Fin K)) : Alg4.State K :=
  Alg4.runFrom E T ℓ q₀ 1 (Alg4.init E T) h

end FirstOrderFG


