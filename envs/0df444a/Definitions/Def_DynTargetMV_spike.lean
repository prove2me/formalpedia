-- Prove2me | Definitions.Def_DynTargetMV_spike
-- name    : DynTargetMV_spike
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:30.821982+00:00
-- url     : https://prove2.me/theorems/3a007ef4-d5d2-4b9a-860e-08303e2fd683
-- title:
--   The spike strategy: $a$ on $[t,t+\varepsilon)$, $b$ elsewhere, (2.4)
-- statement:
--   Given two feedback strategies $a$ and $b$, this is the strategy
--   $$
--   (s,y)\mapsto\begin{cases}a(s,y),& s\in[t,t+\varepsilon),\\ b(s,y),& s\notin[t,t+\varepsilon).\end{cases}
--   $$
--   With $a$ constant equal to $\pi\in\mathbb R^m$ and $b=\hat\pi$, this is the strategy $\pi_{t,\varepsilon,\pi}$ of (2.4), in which the time-$t$ self deviates for a period of length $\varepsilon$. With other choices of $a$ it gives (C.1), (C.19) and the strategies of Lemma 3.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.4), p.7

import Mathlib

namespace DynTargetMV

/-- The strategy that follows `a` on `[t, t+ε)` and `b` elsewhere, the common form of (2.4), (C.1),
(C.19) and of the strategies `π^ε_i` of Lemma 3. With `a` constant in `(s, y)` and `b = π̂` it is
`π_{t,ε,π}` of (2.4). He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.4), p.7. -/
noncomputable def spike {m : ℕ} (t ε : ℝ) (a b : ℝ → ℝ → Fin m → ℝ) : ℝ → ℝ → Fin m → ℝ :=
  fun s y => if t ≤ s ∧ s < t + ε then a s y else b s y

end DynTargetMV


