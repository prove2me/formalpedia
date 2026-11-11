-- Prove2me | Definitions.Def_SparseLowFactors_BoundedDeg_Sylvester
-- name    : SparseLowFactors_BoundedDeg_Sylvester
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:22:47.064016+00:00
-- url     : https://prove2.me/theorems/076805e5-7e83-4a57-ac48-e64398e2a476
-- title:
--   Sylvester matrix, resultant, discriminant, and Hensel-ready points
-- statement:
--   Let $R$ be a commutative ring, $f=\sum_{i\le m}f_iX^i$ and $g=\sum_{i\le n} g_iX^i$ in $R[X]$.
--
--   1. The **Sylvester matrix** $\mathrm{Syl}(f,g)$ (Definition 2.15) is the $(m+n)\times(m+n)$ matrix whose first $n$ columns carry the coefficients $f_m,f_{m-1},\dots,f_0$ of $f$, column $j$ starting in row $j$, and whose last $m$ columns carry $g_n,\dots,g_0$, column $n+j'$ starting in row $j'$ (rows and columns from $0$); all other entries are $0$. With $m=\deg f$ and $n=\deg g$ this is the printed matrix.
--   2. The **resultant** is $\mathrm{Res}(f,g)=\det\mathrm{Syl}(f,g)$, and the **discriminant** is $\mathrm{Disc}(f)=\mathrm{Res}(f,f')$ with $f'$ the formal derivative (Definition 2.16), taken with the sizes $\deg f$ and $\deg f-1$.
--   3. For $f\in F[X][Y]$ monic in $Y$ and a point $\alpha$, $f$ is **Hensel-ready at $X=\alpha$** (Definition 2.25) if, writing $f=h_1^{e_1}\cdots h_r^{e_r}$ for its irreducible factorization with the $h_i$ monic in $Y$,
--   $$\mathrm{Res}_Y(h_i,h_j)(\alpha)\neq0\ (i\neq j),\qquad \mathrm{Disc}_Y(h_i)(\alpha)\neq0\ (\text{all } i).$$
--
--   Hensel-readiness is the non-degeneracy condition under which every root of $f(\alpha,Y)$ lifts to a unique power-series root (Lemma 2.26).
--
--   **Formalization Note** The matrix is laid out exactly as printed (Mathlib's `Polynomial.sylvester` uses another layout, and Lemma 2.20 depends on the layout). $\mathrm{Disc}$ uses the explicit sizes $(\deg f,\deg f-1)$ as in the proof of Lemma 2.20; they agree with $\deg f'$ when $\mathrm{char}\,F=0$ or $>\deg f$. $\mathrm{Res}_Y,\mathrm{Disc}_Y$ are computed over the coefficient ring $A$ ($A=F[X]$, or $F(X)[T]$ in Theorem 2.28); they are the same elements as over the fraction field. Hensel-readiness is phrased for the polynomials it is applied to (monic in $Y$): the irreducible factors are ranged over as the monic irreducible divisors, each irreducible factor of a monic polynomial being an associate of exactly one of them. The evaluation $X\mapsto\alpha$ is a ring map `ev`.
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 20 (Definitions 2.15, 2.16), p. 23 (Definition 2.25)

import Mathlib

set_option autoImplicit false

/-!
# Sylvester matrix, resultant, discriminant (Definitions 2.15, 2.16) and Hensel-ready points
(Definition 2.25)

Bhattacharjee, Kothary, Rai, Saraf, arXiv:2606.27293 (held version, sha256 9837a932…), §2.4 p. 20,
§2.6 p. 23.
-/

namespace SparseLowFactors.BoundedDeg

open Polynomial

/-- The Sylvester matrix of Definition 2.15 (p. 20) with explicit sizes `m` (for `f`) and `n`
(for `g`), laid out as printed, indices from `0`: the first `n` columns hold the coefficients of `f`,
column `j < n` carrying `f_m, f_{m-1}, …, f_0` in rows `j, …, j + m`; column `n + j'` (`j' < m`)
carries `g_n, …, g_0` in rows `j', …, j' + n`; all other entries are `0`. With `m = deg f`,
`n = deg g` it is `Syl(f, g)`. (Mathlib's `Polynomial.sylvester` uses another layout.) -/
def syl {R : Type*} [Semiring R] (f g : Polynomial R) (m n : ℕ) :
    Matrix (Fin (m + n)) (Fin (m + n)) R :=
  Matrix.of fun i j =>
    if (j : ℕ) < n then
      (if (j : ℕ) ≤ i ∧ (i : ℕ) ≤ j + m then f.coeff (m - (i - j)) else 0)
    else
      (if (j : ℕ) - n ≤ i ∧ (i : ℕ) ≤ (j - n) + n then g.coeff (n - (i - (j - n))) else 0)

/-- `Syl(f, g)` with the sizes of Definition 2.15: `deg f` and `deg g`. -/
noncomputable def sylv {R : Type*} [Semiring R] (f g : Polynomial R) :
    Matrix (Fin (f.natDegree + g.natDegree)) (Fin (f.natDegree + g.natDegree)) R :=
  syl f g f.natDegree g.natDegree

/-- The resultant `Res(f, g) = det Syl(f, g)` (Definition 2.15). -/
noncomputable def res {R : Type*} [CommRing R] (f g : Polynomial R) : R := (sylv f g).det

/-- `Syl(f, f')` with explicit sizes `deg f` and `deg f − 1` (the degree of `f'` when
`char = 0` or `char > deg f`, as in the proof of Lemma 2.20). -/
noncomputable def sylDeriv {R : Type*} [Semiring R] (f : Polynomial R) :
    Matrix (Fin (f.natDegree + (f.natDegree - 1))) (Fin (f.natDegree + (f.natDegree - 1))) R :=
  syl f (derivative f) f.natDegree (f.natDegree - 1)

/-- The discriminant `Disc(f) = Res(f, f')` (Definition 2.16), `f'` the formal derivative, with the
sizes `deg f`, `deg f − 1`. -/
noncomputable def disc {R : Type*} [CommRing R] (f : Polynomial R) : R := (sylDeriv f).det

/-- **Hensel-ready** (Definition 2.25, p. 23), for a polynomial `f` monic in `Y` over a coefficient
ring `A` (`A = F[X]`, or `F(X)[T]` in Theorem 2.28) and an evaluation `ev : A →+* k` (`X ↦ α`):
for the irreducible factors `h_i` of `f`, taken monic in `Y`, `Res_Y(h_i, h_j)(α) ≠ 0` for
`h_i ≠ h_j` and `Disc_Y(h_i)(α) ≠ 0`. Res and Disc are computed over `A` (they are the same
elements of `F(X)` as over the fraction field). For `f` monic every irreducible factor is an
associate of exactly one monic one, so ranging over the monic irreducible divisors is ranging over
the factors `h_1, …, h_r` of the irreducible factorization. -/
def HenselReady {A k : Type*} [CommRing A] [CommRing k] (f : Polynomial A) (ev : A →+* k) : Prop :=
  (∀ h₁ h₂ : Polynomial A, h₁.Monic → Irreducible h₁ → h₁ ∣ f → h₂.Monic → Irreducible h₂ →
      h₂ ∣ f → h₁ ≠ h₂ → ev (res h₁ h₂) ≠ 0) ∧
  (∀ h : Polynomial A, h.Monic → Irreducible h → h ∣ f → ev (disc h) ≠ 0)

end SparseLowFactors.BoundedDeg


