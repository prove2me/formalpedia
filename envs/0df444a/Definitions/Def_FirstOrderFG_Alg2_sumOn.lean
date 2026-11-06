-- Prove2me | Definitions.Def_FirstOrderFG_Alg2_sumOn
-- name    : FirstOrderFG_Alg2_sumOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:53:01.713708+00:00
-- url     : https://prove2.me/theorems/62227477-7e35-425c-a7ac-45ba98ca6e1e
-- title:
--   Sum over a predictable interval of rounds $\sum_{t\in I}F_t$
-- statement:
--   An instance started at round $\tau$ runs on an interval $I$ of rounds, membership of round $t$ being decided before round $t$ is sampled: round $t\le T$ is in $I$ while a continuation predicate, evaluated on the instance's past arms, holds. This returns $\sum_{t\in I}F_t$ for a per-round quantity $F_t$ of the state before round $t$.
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, Lemma B.1, p.22

import Mathlib
import Definitions.Def_FirstOrderFG_Alg2_step

namespace FirstOrderFG

open Classical in
/-- **`∑_{t ∈ I} F_t` over a predictable interval of rounds.** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, Lemma B.1, p.22: an instance
"that starts at round `τ` and runs on an interval `I` of rounds, where whether `t ∈ I` is
determined before round `t` is sampled".

`Alg2.sumOn E T ℓ q₀ cont F t st done h` walks the instance along the arms `h`, from global round `t`
and state `st`, with `done` the arms already played by the instance; a round belongs to `I` while
it is at most `T` and `cont` holds of the history so far (once `cont` fails, the interval has
ended). It returns the sum of `F t st_t` over the rounds of `I`, `st_t` the instance state before
round `t`.

**Formalization Note.** `cont` reads only the instance's past arms, which is exactly "determined
before round `t` is sampled" given the fixed history before `τ`. -/
noncomputable def Alg2.sumOn {K : ℕ} (E : Fin K → Fin K → Prop) [DecidableRel E] (T : ℕ) (ℓ : ℕ → Fin K → ℝ)
    (q₀ : (Fin K → ℝ) → ℝ → Fin K → ℝ) (cont : List (Fin K) → Prop)
    (F : ℕ → Alg2.State K → ℝ) : ℕ → Alg2.State K → List (Fin K) → List (Fin K) → ℝ
  | _, _, _, [] => 0
  | t, st, done, I :: rest =>
    if t ≤ T ∧ cont done then
      F t st + Alg2.sumOn E T ℓ q₀ cont F (t + 1) (Alg2.step E T ℓ q₀ t st I) (done ++ [I]) rest
    else 0

end FirstOrderFG


