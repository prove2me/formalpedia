-- Prove2me | Definitions.Def_EvasivePatterns_periods
-- name    : EvasivePatterns_periods
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:11.689149+00:00
-- url     : https://prove2.me/theorems/396d2f98-0dce-428d-bf96-96d7ac19916f
-- title:
--   Periods $\mathrm{Per}(P)$, smallest period $p$, gcd of the periods $c$, and period support $S_P$
-- statement:
--   Let $P = P_1 \cdots P_m$ be a word. A shift $d$ is a **period** of $P$ if the two copies of $P$ shifted by $d$ agree wherever they overlap:
--   $$
--   P_i = P_{i+d} \qquad (1 \le i \le m-d).
--   $$
--   $\mathrm{Per}(P)$ is the set of all positive periods; it always contains $m$. The mission writes
--   $$
--   p = \min \mathrm{Per}(P), \qquad c = \gcd \mathrm{Per}(P), \qquad S_P = \{0\} \cup \mathrm{Per}(P).
--   $$
--   For example $01100$ has periods $\{4,5\}$ (so $p = 4$, $c = 1$) and $0101$ has periods $\{2,4\}$ (so $p = c = 2$). For a nonempty word $1 \le c \le p \le m$. The quantities $p$ and $c$ are those of the goal theorem.
--
--   **Formalization Note** Mathlib's `List.HasPeriod` is the condition above but also holds for $d = 0$ and every $d \ge m$, so periods are taken in $[1, m]$. The word may be over any alphabet with decidable equality. For the empty word $p$ and $c$ take the value $0$.
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), §1, display (1), p.1 (PDF p.2), lines 21–27; S_P: Proposition 2.1, display (3), p.3 (PDF p.4)

import Mathlib

namespace EvasivePatterns

instance instDecidableHasPeriod {α : Type*} [DecidableEq α] (w : List α) (d : ℕ) :
    Decidable (w.HasPeriod d) :=
  inferInstanceAs (Decidable (w <+: w.take d ++ w))

/-- **The periods `Per(P)` of a word.** A shift `d` is a period of `P = P_1 ⋯ P_m` if
`P_i = P_{i+d}` for `1 ≤ i ≤ m − d`; `Per(P)` is the set of all positive periods, including `m`.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), §1, printed p. 1 (PDF p. 2), lines 21–27: "A shift d is a period if
the two copies agree wherever they overlap; equivalently, P_i = P_{i+d} (1 ≤ i ≤ m − d). […] where
Per(P) contains all positive periods, including m."

**Formalization Note** Mathlib's `List.HasPeriod P d` (`P` is a prefix of `take d P ++ P`) is exactly
`P_i = P_{i+d}` for `1 ≤ i ≤ m − d`; it also holds for `d = 0` and every `d ≥ m`, so `Per(P)` is taken
inside `[1, m]`. The word is over an arbitrary alphabet with decidable equality. `Per([]) = ∅`. -/
def periods {α : Type*} [DecidableEq α] (P : List α) : Finset ℕ :=
  (Finset.Icc 1 P.length).filter (fun d => P.HasPeriod d)

/-- **The smallest period `p = min Per(P)`** (display (1)).

Source: Faro, Marino, Pavone, manuscript (Nov. 2026), §1, display (1), printed p. 1 (PDF p. 2).

**Formalization Note** `sInf` in `ℕ`; for a nonempty word `m ∈ Per(P)`, so the minimum exists and
`1 ≤ p ≤ m`. For the empty word the value is the junk value `0`. -/
noncomputable def minPeriod {α : Type*} [DecidableEq α] (P : List α) : ℕ :=
  sInf (periods P : Set ℕ)

/-- **The gcd of the periods `c = gcd Per(P)`** (display (1)).

Source: Faro, Marino, Pavone, manuscript (Nov. 2026), §1, display (1), printed p. 1 (PDF p. 2).

**Formalization Note** `Finset.gcd` in `ℕ`; for a nonempty word `1 ≤ c ≤ p`. For the empty word the
value is `0`. -/
def gcdPeriods {α : Type*} [DecidableEq α] (P : List α) : ℕ :=
  (periods P).gcd id

/-- **The period support `S_P := {0} ∪ Per(P)`** (display (3)).

Source: Faro, Marino, Pavone, manuscript (Nov. 2026), Proposition 2.1, display (3), printed p. 3
(PDF p. 4). -/
def periodSupport {α : Type*} [DecidableEq α] (P : List α) : Finset ℕ :=
  insert 0 (periods P)

end EvasivePatterns


