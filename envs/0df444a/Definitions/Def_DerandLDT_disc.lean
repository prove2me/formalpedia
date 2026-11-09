-- Prove2me | Definitions.Def_DerandLDT_disc
-- name    : DerandLDT_disc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:04:34.320348+00:00
-- url     : https://prove2.me/theorems/a0a44076-2b60-4be3-bb7d-81f590b5e220
-- title:
--   Discriminant $\mathrm{Disc}(f) = \mathrm{Res}(f, f^{(1)})$
-- statement:
--   For a univariate polynomial $f$ over a commutative ring, the **discriminant** in the sense of the paper is the resultant of $f$ and its first-order Hasse derivative $f^{(1)} = \partial f$:
--   $$
--   \mathrm{Disc}(f) = \mathrm{Res}(f, f^{(1)}) = \det \mathrm{Syl}(f, f^{(1)}),
--   $$
--   the determinant of the $(d_1 + d_2) \times (d_1 + d_2)$ Sylvester matrix of $f$ and $f^{(1)}$, where $d_1 = \deg f$ and $d_2 = \deg f^{(1)}$.
--
--   Over a field, $\mathrm{Disc}(f) \neq 0$ exactly when $f$ and $f^{(1)}$ are coprime, which is how the paper detects squarefree polynomials (Corollaries 3.12 and 3.13).
--
--   **Formalization Note** The resultant is Mathlib's `Polynomial.resultant` with its default sizes, the natural degrees of $f$ and $f^{(1)}$; on the paper's domain ($d_1, d_2 \ge 1$) this is the paper's Sylvester matrix. This is not Mathlib's `Polynomial.discr`, which is normalized by the leading coefficient and a sign.
-- source:
--   Harsha–Kopparty–Kumar–Saptharishi–Sudan, On derandomizing the line-point low-degree test, STOC 2027 submission (manuscript sha256 d57e7d6f…80df), Definition 3.10, p.13

import Mathlib

set_option autoImplicit false

namespace DerandLDT

/-- **Discriminant** `Disc(f) = Res(f, f⁽¹⁾)`: Harsha, Kopparty, Kumar, Saptharishi, Sudan,
*On derandomizing the line-point low-degree test*, STOC 2027 submission manuscript
(sha256 d57e7d6f…80df), Definition 3.10, p.13: "The resultant of `f` and its first order Hasse
derivative `f⁽¹⁾` is referred to as the Discriminant of `f` and is denoted by `Disc(f)`."

**Formalization Note.** The resultant is Mathlib's `Polynomial.resultant`, the determinant of
the Sylvester matrix with the default sizes `deg f` and `deg f⁽¹⁾`; on the paper's domain
(`deg f ≥ 1`, `deg f⁽¹⁾ ≥ 1`) this is the paper's Sylvester matrix, and outside it Mathlib's
convention extends the definition. This is **not** Mathlib's `Polynomial.discr`, which is
normalized by the leading coefficient and a sign. -/
noncomputable def disc {R : Type*} [CommRing R] (f : Polynomial R) : R :=
  Polynomial.resultant f (Polynomial.hasseDeriv 1 f)

end DerandLDT


