-- Prove2me | Definitions.Def_FirstOrderFG_Alg4_sumAlong
-- name    : FirstOrderFG_Alg4_sumAlong
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:56:13.930789+00:00
-- url     : https://prove2.me/theorems/d41473b9-2d44-4c6a-9548-48aaf2e3f5ee
-- title:
--   Sum of per-round quantities along a run of Algorithm 4
-- statement:
--   Walking Algorithm 4 along a list of arms, this sums a per-round quantity of the state after lines 4–9 of each round.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Algorithm 4, p.32

import Mathlib
import Definitions.Def_FirstOrderFG_Alg4_step

namespace FirstOrderFG

/-- **A sum of per-round quantities along a run of Algorithm 4.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Algorithm 4, p.32.

`Alg4.sumAlong E T ℓ q₀ F t st h` walks Algorithm 4 from state `st` before round `t` along the arms
`h`, and sums `F t' st'` over the rounds `t'`, where `st'` is the state after lines 4–9 of round
`t'` (the instance that plays round `t'`). -/
noncomputable def Alg4.sumAlong {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (ℓ : ℕ → Fin K → ℝ)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) (F : ℕ → Alg4.State K → ℝ) :
    ℕ → Alg4.State K → List (Fin K) → ℝ
  | _, _, [] => 0
  | t, st, I :: h =>
    F t (Alg4.prepare E T q₀ st) + Alg4.sumAlong E T ℓ q₀ F (t + 1) (Alg4.step E T ℓ q₀ t st I) h

end FirstOrderFG


