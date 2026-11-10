-- Prove2me | Definitions.Def_EvasivePatterns_signedCount
-- name    : EvasivePatterns_signedCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:27:15.536848+00:00
-- url     : https://prove2.me/theorems/863b1ca2-a0ca-4431-bfec-bb5c7c3a678a
-- title:
--   Signed count $s_n=\sum_{X:\,f_{P,n}(X)=1}(-1)^{\mathrm{wt}(X)}$
-- statement:
--   For a binary pattern $P$ and a length $n$, the **signed count** is the alternating sum, over all texts $X \in \{0,1\}^n$ in which $P$ occurs, of the sign of the number of $1$'s of $X$:
--   $$
--   s_n = \sum_{X \,:\, f_{P,n}(X) = 1} (-1)^{\mathrm{wt}(X)} .
--   $$
--   Up to the sign $(-1)^n$ it is the coefficient of $x_1 \cdots x_n$ in the multilinear polynomial of $f_{P,n}$, so $s_n \ne 0$ forces every position to be read in the worst case. For $P = 01$, $s_2 = -1$ and $s_3 = 0$.
-- source:
--   Faro, Marino, Pavone, A Complete Characterization of Eventually Evasive Binary Patterns, manuscript (Nov. 2026; sha256 e91deef3…), §2, p.4 (PDF p.5), lines 110–111

import Mathlib
import Definitions.Def_EvasivePatterns_occurs

namespace EvasivePatterns

/-- **The signed count `s_n = Σ_{X : f_{P,n}(X) = 1} (−1)^{wt(X)}`**: the sum, over all texts
`X ∈ {0,1}^n` in which `P` occurs, of `(−1)` to the number of `1`'s of `X`.

Source: S. Faro, F. P. Marino, A. Pavone, *A Complete Characterization of Eventually Evasive Binary
Patterns*, manuscript (Nov. 2026), §2, printed p. 4 (PDF p. 5), lines 110–111: "Let f_{P,n}(X) be the
Boolean function which is one exactly when P occurs in X ∈ {0, 1}^n and put
s_n = Σ_{X: f_{P,n}(X)=1} (−1)^{wt(X)}."

**Formalization Note** Texts are `Fin n → Bool` with `1 ↦ true`; `wt(X)` is the number of positions
`i` with `X i = true`. -/
def signedCount (P : List Bool) (n : ℕ) : ℤ :=
  ∑ X ∈ (Finset.univ : Finset (Fin n → Bool)).filter (fun X => occurs P X),
    (-1) ^ ((Finset.univ : Finset (Fin n)).filter (fun i => X i = true)).card

end EvasivePatterns


