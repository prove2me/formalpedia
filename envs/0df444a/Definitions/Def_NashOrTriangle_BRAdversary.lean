-- Prove2me | Definitions.Def_NashOrTriangle_BRAdversary
-- name    : NashOrTriangle_BRAdversary
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:52.256652+00:00
-- url     : https://prove2.me/theorems/fce1e71c-360e-444b-a4cc-c3add2a8cf0a
-- title:
--   Adaptive $\delta$-best-response oracle
-- statement:
--   For $\delta \ge 0$, a **$\delta$-best-response ($\delta$-BR) oracle** answers two kinds of queries. Given a finite rational mixture $q$ of columns (a *maximizing* query), it returns a row $a$ with
--   $$
--   M(a, q) \ge U(q) - \delta ;
--   $$
--   given a finite rational mixture $p$ of rows (a *minimizing* query), it returns a column $b$ with
--   $$
--   M(p, b) \le L(p) + \delta .
--   $$
--   A query may also be $\perp$ (no mixture), answered by any strategy; this is how the first strategies are discovered. The oracle may be **adaptive**: its answer to the $n$-th call may depend on $n$, and the oracle may know the algorithm.
--
--   **Formalization Note** The answer is a function of the call index $n$ (counting maximizing and minimizing calls together from $0$) and the query. Against a fixed deterministic algorithm this is as general as a history-dependent adversary: such an adversary produces one run, and the call-indexed oracle replaying that run's answers produces the same run. The oracle must be valid on every finite rational mixture (on an infinite game an exact best response need not exist; then no $0$-BR oracle exists and statements about all such oracles are vacuous for that game).
-- source:
--   Daskalakis–Papadimitriou–Yannakakis, On the Complexity of Infinite Zero-Sum Games, STOC 2027 submission (manuscript sha256 4f8d0962…66f7), §1.1, p.4 (PDF p.5)

import Mathlib
import Definitions.Def_NashOrTriangle_IsFinMix
import Definitions.Def_NashOrTriangle_upper
import Definitions.Def_NashOrTriangle_lower

namespace NashOrTriangle

/-- An adaptive **`δ`-best-response oracle** for the game `M`. `row n q` is the answer to the
`n`-th BR call (counting maximizing and minimizing calls together, from `0`) when it is a
maximizing query on the column mixture `q` (`none` is the query `q = ⊥`); `col n p` likewise
for a minimizing query on the row mixture `p`. Validity: against every finite rational mixture
`q` the returned row `a` has `M(a, q) ≥ U(q) − δ`, and against every finite rational mixture `p`
the returned column `b` has `M(p, b) ≤ L(p) + δ`; a `⊥` query may be answered by any strategy.

Source: Daskalakis–Papadimitriou–Yannakakis, *On the Complexity of Infinite Zero-Sum Games*,
STOC 2027 submission manuscript (sha256 4f8d0962…66f7), §1.1, printed p. 4 (PDF p. 5): "For δ ≥ 0, a δ-best-response (δ-BR) oracle operates as
follows: Given a finite rational mixture q of known columns, it returns a row a with
M(a, q) ≥ U(q) − δ; given a finite rational mixture p of known rows, it returns a column b with
M(p, b) ≤ L(p) + δ." and "Our upper bounds in Section 2 hold even against an adaptive adversary
who gives history-dependent responses and who has knowledge of our algorithm."

**Formalization Note** Adaptivity enters through the call index `n`. Against a fixed
deterministic program this is as general as a fully history-dependent adversary: any such
adversary produces one run, and the call-indexed oracle that replays that run's answers (and
answers every other query validly) produces the same run. The oracle is a total function, valid
on every finite rational mixture; mixtures here are over strategies (the machine translates the
labels of known strategies). For `δ = 0` on an infinite game such an oracle need not exist, in
which case statements quantifying over oracles are vacuous for that game, exactly as in the
paper (an exact best response may not exist). -/
structure BRAdversary {A B : Type*} (M : A → B → ℚ) (δ : ℝ) where
  /-- The row returned by the `n`-th BR call, a maximizing query on `q` (`none` = `⊥`). -/
  row : ℕ → Option (B →₀ ℚ) → A
  /-- The column returned by the `n`-th BR call, a minimizing query on `p` (`none` = `⊥`). -/
  col : ℕ → Option (A →₀ ℚ) → B
  /-- Maximizing answers are `δ`-best responses. -/
  row_valid : ∀ n q, IsFinMix q → upper M q - δ ≤ payoffRow M (row n (some q)) q
  /-- Minimizing answers are `δ`-best responses. -/
  col_valid : ∀ n p, IsFinMix p → payoffCol M p (col n (some p)) ≤ lower M p + δ

end NashOrTriangle


