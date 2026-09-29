-- Prove2me | Definitions.Def_eulerMascheroni_rivoalPoly
-- name    : eulerMascheroni_rivoalPoly
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-25T21:19:26.407203+00:00
-- url     : https://prove2.me/theorems/f9794513-64cc-48bd-84b1-027717576d50
-- title:
--   Integer polynomials $N_n$, $D_n$, $U_{n,j}$, $P_n$ for Rivoal's forms
-- statement:
--   Integer polynomials behind Rivoal's forms in $1,e,e\operatorname{Ein}(1)$ (the polynomial side of their elementary proof).
--
--   Fix $n\ge1$ and write $X^{(j)}=X(X-1)\cdots(X-j+1)$ for the falling factorial (Mathlib's `descPochhammer`). Define in $\mathbb Z[X]$
--   $$
--   N_n(X)=\prod_{i=n+1}^{3n}(X-i),\qquad D_n(X)=\prod_{i=0}^{n}(X-i),\qquad
--   U_{n,j}(X)=X^{(j)}\prod_{\substack{0\le i\le n\\ i\ne j}}(X-i)\quad(0\le j\le n),
--   $$
--   and the integers
--   $$
--   b_{n,j}=(-1)^{n-j}\beta_{n,j}=(-1)^{n-j}\frac{(3n-j)!}{\big(j!\,(n-j)!\big)^2}\qquad(0\le j\le n).
--   $$
--   Finally
--   $$
--   P_n=\Big(N_n-\sum_{j=0}^{n}b_{n,j}\,U_{n,j}\Big)\ \mathrm{div}\ D_n ,
--   $$
--   the quotient of Euclidean division by the monic polynomial $D_n$.
--
--   The division is exact, and $P_n$ is the polynomial part of the partial-fraction expansion
--   $$
--   \frac{N_n(x)}{D_n(x)}=P_n(x)+\sum_{j=0}^n b_{n,j}\,\frac{x^{(j)}}{x-j}.
--   $$
--   Its values at $x=0,\dots,n-1$ determine the constant coefficient $p'_n$ of Rivoal's forms. These facts are proved as separate theorems.
--
--   **Formalization Note** $b_{n,j}$ (`bInt`) is written with natural-number division `(3n-j)! / (j!(n-j)!)^2`, which is exact for $j\le n$ (a separate theorem identifies it with $(-1)^{n-j}$ `beta n j` of `eulerMascheroni_rivoalForms`). $P_n$ (`polyP`) is `Polynomial.divByMonic`.
-- source:
--   T. Rivoal, Michigan Math. J. 61 (2012), Prop. 4 and Lemma 4 (https://rivoal.perso.math.cnrs.fr/articles/gammater.pdf); polynomial side (Lemmas A0-A5) of the accompanying elementary proof (research notes Q_CHILD_PROOF.md, section 2).

import Definitions.Def_eulerMascheroni_rivoalForms
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
Integer polynomials behind Rivoal's forms (polynomial side of the elementary proof).

For `n ≥ 1`:
* `polyN n = ∏_{i=n+1}^{3n} (X - i)`, `polyD n = ∏_{i=0}^{n} (X - i)` (monic, in `ℤ[X]`);
* `bInt n j = (-1)^(n-j) β_{n,j}` as an integer (natural-number division, exact by Lemma B1);
* `polyU n j = X^{(j)} · ∏_{0 ≤ i ≤ n, i ≠ j} (X - i)` with `X^{(j)} = descPochhammer ℤ j`;
* `polyP n = (polyN n - ∑_{j ≤ n} bInt n j · polyU n j) /ₘ polyD n`, the polynomial part of the
  partial-fraction expansion `N/D = P + ∑_j b_j X^{(j)}/(X - j)`.
-/

noncomputable section
namespace EulerMascheroni.Rivoal
open Polynomial

/-- `b_{n,j} = (-1)^(n-j) (3n-j)! / (j! (n-j)!)²` as an integer. -/
def bInt (n j : ℕ) : ℤ :=
  (-1) ^ (n - j) * (((3 * n - j).factorial / (j.factorial * (n - j).factorial) ^ 2 : ℕ) : ℤ)

/-- `N_n(X) = ∏_{i=n+1}^{3n} (X - i)`. -/
def polyN (n : ℕ) : ℤ[X] := ∏ i ∈ Finset.Icc (n + 1) (3 * n), (X - C (i : ℤ))

/-- `D_n(X) = ∏_{i=0}^{n} (X - i) = X^{(n+1)}`. -/
def polyD (n : ℕ) : ℤ[X] := ∏ i ∈ Finset.range (n + 1), (X - C (i : ℤ))

/-- `U_{n,j}(X) = X^{(j)} · ∏_{0 ≤ i ≤ n, i ≠ j} (X - i)`. -/
def polyU (n j : ℕ) : ℤ[X] :=
  descPochhammer ℤ j * ∏ i ∈ (Finset.range (n + 1)).erase j, (X - C (i : ℤ))

/-- `P_n = (N_n - ∑_{j ≤ n} b_{n,j} U_{n,j}) /ₘ D_n`. -/
def polyP (n : ℕ) : ℤ[X] :=
  (polyN n - ∑ j ∈ Finset.range (n + 1), C (bInt n j) * polyU n j) /ₘ polyD n

end EulerMascheroni.Rivoal


