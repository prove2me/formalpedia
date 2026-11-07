-- Prove2me | Definitions.Def_KSATWindow_Window
-- name    : KSATWindow_Window
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:08.312825+00:00
-- url     : https://prove2.me/theorems/bd5a8ceb-4fca-4c8c-a70f-af58f0b84644
-- title:
--   The with-replacement scaling window $\tilde W_\eta(n)$, its quantiles $\tilde m_u(n)$ and the mean $a_n=\mathbb E T_n$
-- statement:
--   Fix $k\ge 3$ and $n\ge k$, and let $C_1,C_2,\dots$ be independent uniform signed $k$-clauses on $[n]$, with $F_{n,m}=C_1\wedge\dots\wedge C_m$ and $T_n$ the first $m$ for which $F_{n,m}$ is unsatisfiable (the published `SATVariance` vocabulary). This module defines:
--
--   1. $\mathbb P(F_{n,m}\text{ is unsatisfiable})$;
--   2. the quantile $\tilde m_u(n)$, the least $m$ with $\mathbb P(F_{n,m}\text{ is unsatisfiable})\ge u$;
--   3. the window
--   $$\tilde W_\eta(n)=\tilde m_{1-\eta}(n)-\tilde m_\eta(n),\qquad \eta\in(0,1/2);$$
--   4. the mean $a_n=\mathbb E\,T_n$.
--
--   These are the objects of the goal theorem: the window measures how many clauses the transition from satisfiable to unsatisfiable takes.
--
--   **Formalization Note** $\tilde m_u(n)$ is a natural-number infimum, which would be $0$ on an empty set; for $n\ge k$ and $u<1$ the set is nonempty because $T_n$ is almost surely finite. $a_n$ is a Bochner integral; $T_n$ has finite moments for $n\ge k$.
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), §1, p.2 (definitions of m̃_u(n), W̃_η(n), T_n, a_n)

import Mathlib
import Definitions.Def_SATVariance
open MeasureTheory ProbabilityTheory OAI.RandomKSAT

namespace KSATWindow

/-!
# The with-replacement scaling window of random k-SAT

G. Carenini, *A polynomial scaling window for random k-SAT and a proof of the satisfiability
conjecture*, STOC 2027 submission (manuscript sha256 1664cf10…), §1, pp.1–2.

The clause family, the clause stream and the first unsatisfiable count are the published
`SATVariance` vocabulary (`OAI.RandomKSAT`):
* `Clause n k` is a signed k-clause on `[n]` with `k` distinct variables (the set `Cₙ`, p.1);
* `streamLaw n k` is the law of an i.i.d. sequence `C₁, C₂, …` of uniform members of `Cₙ`
  (`ω 0` is `C₁`), and `PrefixSAT ω m` says that `F_{n,m} = C₁ ∧ ⋯ ∧ C_m` is satisfiable (p.2);
* `H ω` is `Tₙ`, the first unsatisfiable clause count, read through `ℕ∞ → ℕ`.

**Formalization Note.** `H` reads an infinite first-failure time as `0`; for `k ≤ n` that is a
null event (`OAI.RandomKSAT.firstFailure_finite_ae`), so `H` is `Tₙ` almost surely.
`quantile n k u` is an `sInf` in `ℕ`, which is `0` on an empty set. For `k ≤ n` and `u < 1` the set
is nonempty, because `Tₙ` is almost surely finite; for `n < k` there are no clauses and the window
is junk, which the asymptotic statements of the mission ignore.
-/

/-- `P(F_{n,m} is unsatisfiable)` (p.2): the probability that the first `m` clauses of the stream
admit no common satisfying assignment. -/
noncomputable def unsatProb (n k m : ℕ) : ℝ :=
  (streamLaw n k).real {ω | ¬ PrefixSAT ω m}

/-- `m̃_u(n)` (p.2): the least `m` for which `P(F_{n,m} is unsatisfiable) ≥ u`.

**Formalization Note.** An `sInf` in `ℕ`; it is `0` when no such `m` exists. -/
noncomputable def quantile (n k : ℕ) (u : ℝ) : ℕ :=
  sInf {m : ℕ | u ≤ unsatProb n k m}

/-- The with-replacement window `W̃_η(n) = m̃_{1−η}(n) − m̃_η(n)` (p.2), for `η ∈ (0, 1/2)`,
as a real number. -/
noncomputable def window (n k : ℕ) (η : ℝ) : ℝ :=
  (quantile n k (1 - η) : ℝ) - (quantile n k η : ℝ)

/-- `aₙ = E Tₙ` (p.2), the mean of the first unsatisfiable clause count.

**Formalization Note.** A Bochner integral; `Tₙ` has finite moments for `k ≤ n` ((2.2), p.5),
so it is the true mean there. -/
noncomputable def meanTime (n k : ℕ) : ℝ :=
  ∫ ω, H ω ∂(streamLaw n k)

end KSATWindow


