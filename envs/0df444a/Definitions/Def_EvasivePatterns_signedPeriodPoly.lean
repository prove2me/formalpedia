-- Prove2me | Definitions.Def_EvasivePatterns_signedPeriodPoly
-- name    : EvasivePatterns_signedPeriodPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:27:14.667269+00:00
-- url     : https://prove2.me/theorems/3f6e1daa-6b48-4e1e-8da9-e93254dcf4e6
-- title:
--   Signed period polynomial $Q_P(z)=\sum_{j\in S_P} q_j z^j$
-- statement:
--   Let $P$ be a binary word and write $\mathrm{wt}(Y)$ for the number of $1$'s in a binary word $Y$. For a length $j$ the **prefix sign** is
--   $$
--   q_j = (-1)^{\mathrm{wt}(P[1..j])}, \qquad q_0 = 1 ,
--   $$
--   and the **signed period polynomial** is
--   $$
--   Q_P(z) = \sum_{j \in S_P} q_j z^j \in \mathbb Z[z], \qquad S_P = \{0\}\cup\mathrm{Per}(P).
--   $$
--   For $P = 01100$ one gets $Q_P(z) = 1 + z^4 + z^5$; for $P = 01$, $Q_P(z) = 1 - z^2$. The polynomial $Q_P$ links the overlap structure of $P$ to the signed counts of texts containing $P$.
--
--   **Formalization Note** `prefixSign P j` is defined for every length $j$ (the sign rule before display (6) uses non-period lengths); `1` is `true`.
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), §2, display (5), p.3 (PDF p.4), lines 97–99

import Mathlib
import Definitions.Def_EvasivePatterns_periods

namespace EvasivePatterns

/-- **The prefix sign `q_j = (−1)^{wt(P[1..j])}`**, where `wt` counts the `1`'s; `q_0 = 1`. The
paper uses it for `j ∈ S_P` and, in the sign rule before display (6), for prefixes of any length.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), §2, printed p. 3 (PDF p. 4), lines 97–98: "Let wt(Y) denote the
number of 1's in a binary word Y. For j ∈ S_P set q_j = (−1)^{wt(P[1..j])}, with q_0 = 1".

**Formalization Note** Binary symbols are `Bool` with `1 ↦ true`, so `wt` is `List.count true`;
`P[1..j]` is `P.take j`. -/
def prefixSign (P : List Bool) (j : ℕ) : ℤ :=
  (-1) ^ ((P.take j).count true)

/-- **The signed period polynomial `Q_P(z) = Σ_{j ∈ S_P} q_j z^j`** (display (5)).

Source: Faro, Marino, Pavone, manuscript (Nov. 2026), §2, display (5), printed p. 3 (PDF p. 4),
lines 98–99.

**Formalization Note** An integer polynomial; `S_P = {0} ∪ Per(P)` is `periodSupport P`. -/
noncomputable def signedPeriodPoly (P : List Bool) : Polynomial ℤ :=
  ∑ j ∈ periodSupport P, Polynomial.C (prefixSign P j) * Polynomial.X ^ j

end EvasivePatterns


