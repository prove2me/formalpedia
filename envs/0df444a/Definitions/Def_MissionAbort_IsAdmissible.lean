-- Prove2me | Definitions.Def_MissionAbort_IsAdmissible
-- name    : MissionAbort_IsAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:49:24.461018+00:00
-- url     : https://prove2.me/theorems/f2f50a9b-5c9e-4256-ac0c-62dd7d2cd89f
-- title:
--   The constraint of (1) and (7)
-- statement:
--   A family of rules is admissible if $a_n(y_{1:n})=1$ whenever $y_n=0$, for $n\in[N-1]$.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §4, (1), p.11, and (7), p.15

import Mathlib
import Definitions.Def_MissionAbort_Rule

namespace MissionAbort

/-- The constraint of (1) and (7) (Sun, Hu & Ye, arXiv:2505.03225v1, pp.11, 15):
`aₙ(y_{1:n}) = 1` if `yₙ = 0`, for `n ∈ [N − 1]`. -/
def IsAdmissible {K : ℕ} (N : ℕ) (a : Rule K) : Prop :=
  ∀ (n : ℕ) (hn : 1 ≤ n), n < N → ∀ y : Fin n → Fin (K + 1),
    y ⟨n - 1, by omega⟩ = 0 → a n y = true

end MissionAbort


