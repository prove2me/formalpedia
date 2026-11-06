-- Prove2me | Definitions.Def_AltRegret_effCumLoss
-- name    : AltRegret_effCumLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:00:46.531197+00:00
-- url     : https://prove2.me/theorems/42b9ea45-1cf3-4186-b9e4-a5a8961dc54a
-- title:
--   Effective cumulative loss $L_t=\sum_{s=1}^t(c_{s-1}+c_s)$
-- statement:
--   For a loss sequence $c_1,c_2,\dots\in\mathbb R^d$ with $c_0=\mathbf 0$, the **effective cumulative loss** after $t$ rounds is the vector
--   $$
--   L_0=\mathbf 0,\qquad L_t=\sum_{s=1}^{t}(c_{s-1}+c_s)\quad(t\ge1).
--   $$
--   It charges round $s$ with the loss $c_{s-1}+c_s$, the loss of alternating play. It is the vector that line 6 of Algorithm 1 maintains ($L_t\leftarrow L_{t-1}+c_{t-1}+c_t$).
--
--   **Formalization Note** Coordinatewise; for $t=0$ the sum is empty, which gives $L_0=\mathbf 0$.
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, §2.1, p.6

import Mathlib
import Definitions.Def_AltRegret_lossAt

namespace AltRegret

/-- **Effective cumulative loss `L_t`.** Tao–Zheng, arXiv:2608.24731, §2.1, p.6: "we define
`L₀ = 0` and `L_t = ∑_{s=1}^t (c_{s−1} + c_s)` as the effective cumulative loss for `t ≥ 1`."

**Formalization Note.** Coordinatewise, with `c₀ = 0` (see `lossAt`). For `t = 0` the sum is
empty, so `effCumLoss c 0 = 0 = L₀`. This is also the vector maintained by line 6 of
Algorithm 1 (`L_t ← L_{t−1} + c_{t−1} + c_t`). -/
def effCumLoss {d : ℕ} (c : ℕ → Fin d → ℝ) (t : ℕ) : Fin d → ℝ :=
  fun i => ∑ s ∈ Finset.Icc 1 t, (lossAt c (s - 1) i + lossAt c s i)

end AltRegret


