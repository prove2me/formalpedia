-- Prove2me | Definitions.Def_BorderDiffEq_Supplement_Gpoly
-- name    : BorderDiffEq_Supplement_Gpoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:52:37.648883+00:00
-- url     : https://prove2.me/theorems/ee644f2f-c370-4079-a3e3-c79841031a40
-- title:
--   The polynomial $G_n=\prod_{1\le i<j\le n}(x_i+x_j)$
-- statement:
--   $$
--   G_n(x)=\prod_{1\le i<j\le n}(x_i+x_j)\in F[x_1,\dots,x_n].
--   $$
--   Its $k$-th power is the hard polynomial of the lower bound for borders of sums of powers of roABPs (Theorem 2.9).
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Theorem 2.9, p.10; Theorem 9.6, p.71

import Mathlib

namespace BorderDiffEq.Supplement

/-- **The polynomial `Gₙ(x) := ∏_{1 ≤ i < j ≤ n} (xᵢ + xⱼ)`** (Bhat–Dutta–Kaplan–Shpilka–Shringi,
*Demystifying Border of Structured Algebraic Circuits via Differential Equations*, manuscript
(STOC 2027 submission), Theorem 2.9, p.10, and Theorem 9.6, p.71).

**Formalization Note.** Variables are `Fin n` (0-indexed); the product runs over the pairs
`(i, j)` with `i < j`. -/
noncomputable def Gpoly (F : Type) [CommRing F] (n : ℕ) : MvPolynomial (Fin n) F :=
  ∏ p ∈ (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2),
    (MvPolynomial.X p.1 + MvPolynomial.X p.2)

end BorderDiffEq.Supplement


