-- Prove2me | Definitions.Def_BorderDiffEq_wronskian
-- name    : BorderDiffEq_wronskian
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:25:13.447698+00:00
-- url     : https://prove2.me/theorems/12b8d536-aa5f-468e-ab8a-a8c26a2ea698
-- title:
--   The Wronskian $W(f_1,\dots,f_r)$ (Definition 4.1)
-- statement:
--   Let $A$ be a commutative ring and $f_1,\dots,f_r\in A[z]$, with $D=\partial/\partial z$. The **Wronskian** is the determinant
--   $$
--   W(f_1,\dots,f_r)=\det\begin{pmatrix} f_1 & Df_1 & \cdots & D^{r-1}f_1\\ \vdots & \vdots & & \vdots\\ f_r & Df_r & \cdots & D^{r-1}f_r\end{pmatrix}.
--   $$
--   For $r=0$ it is $1$.
--
--   Over a field of characteristic zero it vanishes exactly when the $f_i$ are linearly dependent (Lemma 4.2); it is the leading coefficient of the paper's differential equation.
--
--   **Formalization Note** The $f_i$ form a family indexed by `Fin r`; column $j$ (0-based) holds $D^jf_i$, with $D$ = `Polynomial.derivative`.
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Definition 4.1, p.24

import Mathlib

namespace BorderDiffEq

/-- **The Wronskian, Definition 4.1** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of
Structured Algebraic Circuits via Differential Equations*, manuscript (STOC 2027 submission),
Definition 4.1, p.24): `W(f₁, …, f_r)` is the determinant of the `r × r` matrix whose `i`-th row is
`(fᵢ, D fᵢ, D² fᵢ, …, D^{r-1} fᵢ)`, `D = ∂/∂z`.

**Formalization Note.** The `fᵢ` are univariate polynomials in `z` over a commutative ring `A`
(for the paper's `F(ε)[y, z, x]`, `A` is the ring of polynomials in `(y, x)`), indexed by `Fin r`;
`D` is `Polynomial.derivative` and column `j` (0-based) holds `D^j fᵢ`. -/
noncomputable def wronskian {A : Type} [CommRing A] {r : ℕ} (f : Fin r → Polynomial A) :
    Polynomial A :=
  (Matrix.of fun i j : Fin r => Polynomial.derivative^[(j : ℕ)] (f i)).det

end BorderDiffEq


