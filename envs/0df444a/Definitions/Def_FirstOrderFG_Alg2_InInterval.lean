-- Prove2me | Definitions.Def_FirstOrderFG_Alg2_InInterval
-- name    : FirstOrderFG_Alg2_InInterval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:23.366565+00:00
-- url     : https://prove2.me/theorems/1e51f202-853a-42cf-a925-d793c3fa68ed
-- title:
--   Membership of a round in a predictable interval
-- statement:
--   For an instance started at round $\tau$, the round $\tau+|h|$ reached after the instance history $h$ belongs to the interval $I$ iff it is at most $T$ and the continuation predicate held at every prefix of $h$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma B.1, p.22

import Mathlib

namespace FirstOrderFG

/-- **Round membership in a predictable interval.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Lemma B.1, p.22.

For an instance started at round `τ`, the round `τ + |hist|` reached after the instance history
`hist` belongs to the interval `I` iff it is at most `T` and the continuation predicate `cont` held
at every prefix of `hist` (including `hist` itself). -/
def Alg2.InInterval {K : ℕ} (T τ : ℕ) (cont : List (Fin K) → Prop) (hist : List (Fin K)) : Prop :=
  τ + hist.length ≤ T ∧ ∀ j ≤ hist.length, cont (hist.take j)

end FirstOrderFG


