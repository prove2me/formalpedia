-- Prove2me | Definitions.Def_BorderDiffEq_signedMinor
-- name    : BorderDiffEq_signedMinor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:21.026308+00:00
-- url     : https://prove2.me/theorems/f9f95fcc-605e-4d9c-896d-a5e07504296f
-- title:
--   Signed maximal minors $A_j=(-1)^j\det(M_{j+1})$
-- statement:
--   Let $M$ be an $r\times(r+1)$ matrix over a commutative ring, and for $0\le j\le r$ let $M_{j+1}$ be the $r\times r$ matrix obtained by deleting the $(j+1)$-st column. The **signed maximal minors** are
--   $$
--   A_j=(-1)^j\det(M_{j+1}),\qquad 0\le j\le r .
--   $$
--   They form a kernel vector of $M$ (Lemma 4.23); for $M=(D^jS_i)$ they are the coefficients of the paper's differential equation (Lemma 5.1).
--
--   **Formalization Note** Columns are 0-based: `signedMinor M j` deletes column `j` and carries the sign $(-1)^j$. With 1-based $j'=j+1$ this is Lemma 4.23's $v_{j'}=(-1)^{j'+1}\det(A_{j'})$.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Lemma 4.23, p.30; Lemma 4.4, p.25; Lemma 5.1, p.31

import Mathlib

namespace BorderDiffEq

/-- **Signed maximal minors of an `r × (r+1)` matrix** (Bhat–Dutta–Kaplan–Shpilka–Shringi,
*Demystifying Border of Structured Algebraic Circuits via Differential Equations*, manuscript (STOC
2027 submission), Lemma 4.23, p.30, Lemma 4.4, p.25, and Lemma 5.1, p.31): for `0 ≤ j ≤ r`,
`A_j := (-1)^j det(M_{j+1})`, where `M_{j+1}` is `M` with its `(j+1)`-st column (1-based) deleted.

**Formalization Note.** Columns are 0-based (`Fin (r+1)`): `signedMinor M j` deletes column `j`
(`Fin.succAbove j` enumerates the remaining columns in order) and carries the sign `(-1)^j`. This is
the paper's `Aⱼ = (-1)^j det(M_{j+1})` (Lemmas 4.4, 5.1) and, with 1-based `j' = j + 1`, its
`v_{j'} = (-1)^{j'+1} det(A_{j'})` (Lemma 4.23). -/
noncomputable def signedMinor {R : Type} [CommRing R] {r : ℕ}
    (M : Matrix (Fin r) (Fin (r + 1)) R) (j : Fin (r + 1)) : R :=
  (-1) ^ (j : ℕ) * (M.submatrix id j.succAbove).det

end BorderDiffEq


