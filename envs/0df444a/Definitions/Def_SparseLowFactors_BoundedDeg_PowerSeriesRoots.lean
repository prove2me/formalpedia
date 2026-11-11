-- Prove2me | Definitions.Def_SparseLowFactors_BoundedDeg_PowerSeriesRoots
-- name    : SparseLowFactors_BoundedDeg_PowerSeriesRoots
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:22:46.654202+00:00
-- url     : https://prove2.me/theorems/c6535f8e-6bce-4c2a-9136-2816a7e248c2
-- title:
--   Power-series roots $\Phi_\beta$, $F(T,Y)=f(TX,Y)$, $R_e(Z)$ and the factor-lift
-- statement:
--   Let $f(X,Y)\in F[X][Y]$ and let $L\supseteq F$ be a field.
--
--   1. For $\beta\in L$, $\Phi_\beta\in L[[X]]$ is the **power-series root** of $f$ with constant term $\beta$: $f(X,\Phi_\beta)=0$ and $\Phi_\beta(0)=\beta$ (Lemma 2.26 and the notation after it, p. 23).
--   2. $F(T,Y):=f(TX,Y)$, replacing every $X_i$ by $TX_i$ (p. 24), a polynomial in $T,Y$ over $F[X]$; $\deg_T F$ is its $T$-degree, and $F(0,Y)$ its value at $T=0$.
--   3. For $G(T,Y)$ over $F[X]$ and $\beta\in L$, $\Phi_\beta(T)\in L[X][[T]]$ is the power-series root of $G$ in $T$ with constant term $\beta$ (pp. 24, 30).
--   4. For $e\ge1$ and $D\ge0$ (p. 24),
--   $$R_e(Z)=Z+\sum_{m=0}^{2e(D+1)}[Y^{em+e-2}]\Big\{\Big(\frac{e!}{\partial_Y^eF(0,Z)}\Big)^{m+1}\frac{\partial_YF(T,Y+Z)}{e}\Big(\frac{\partial_Y^eF(0,Z)}{e!}Y^e-F(T,Y+Z)\Big)^m\Big\},$$
--   where $[Y^r]\{P\}$ is the coefficient of $Y^r$ in $P$ and $\partial_Y^e$ the $e$-th derivative in $Y$. It is defined in any ring receiving $F[X][T]$, at any point substituted for $Z$: in the rational function field $F(X,T,Z)$ at $Z$, and in $L[X][T]$ at $Z=\beta$.
--   5. The **factor-lift** (Definition 3.3) of a factor $q(Y)$ of $F(0,Y)$ with multiset of roots $S$ in $L$ is $\prod_{\beta\in S}(Y-\Phi_\beta(T))\ \mathrm{Trunc}\ T^{D+1}$, $D=\deg_T F$, a polynomial in $T$ and $Y$ over $L[X]$.
--
--   The factor-lift is how a factor of the univariate polynomial $F(0,Y)$ is lifted to a candidate factor of $f$, and $R_e$ is the closed formula that makes the truncated roots computable by small constant-depth circuits (Theorem 2.28).
--
--   **Formalization Note** $\Phi_\beta$ and $\Phi_\beta(T)$ are defined by choice among the roots with the given constant term, and as $0$ when there is none; under Hensel-readiness (Lemma 2.26) the root exists and is unique, so the choice is the paper's $\Phi_\beta$. In $R_e$, divisions by $e$, $e!$ and $\partial_Y^eF(0,Z)$ are multiplications by inverses of units (`Ring.inverse`); where $R_e$ is used these are units ($\mathrm{char}\,F=0$ or $>d\ge e$; $\beta$ has multiplicity exactly $e$). The coefficient $[Y^{em+e-2}]$ is $0$ when $em+e-2<0$ (only $e=1,m=0$). Truncation in $T$ is applied coefficientwise in $Y$. Two helper maps are included: $F(T,Y)$ as an element of $F[X_1,\dots,X_n,T,Y]$ (variables `Sum.inl i`, `Sum.inr 0`, `Sum.inr 1`), and the embedding of $F[X][T]$ into $F(X,T,Z)$.
-- source:
--   Bhattacharjee, Kothary, Rai, Saraf, Deterministic Algorithms for Low Individual Degree Factors of Sparse Polynomials, arXiv:2606.27293 (held version, sha256 9837a932…), p. 23 (Lemma 2.26 and following), p. 24 (§2.6, R_e), p. 30 (Definition 3.3), p. 53 (App. B.2)

import Mathlib

set_option autoImplicit false

/-!
# Power-series roots `Φ_β`, the substitution `X ↦ T X`, `R_e(Z)` and the factor-lift

Bhattacharjee, Kothary, Rai, Saraf, arXiv:2606.27293 (held version, sha256 9837a932…): Lemma 2.26
and the notation `Φ_β` (p. 23), `F(T, Y) := f(TX, Y)` and `R_e(Z)` (p. 24), `Φ_β(T)` (pp. 24, 30),
Definition 3.3 (factor-lift, p. 30).

Conventions. `f(X, Y) ∈ F[X][Y]` is `Polynomial (MvPolynomial (Fin n) F)`; `F(T, Y) ∈ F[X][T, Y]` is
`Polynomial (Polynomial (MvPolynomial (Fin n) F))` (outer variable `Y`, inner `T`). Roots `β` live in a
field `L` extending `F`.
-/

namespace SparseLowFactors.BoundedDeg

open Polynomial

/-- The embedding `F[X] → L[[X]]` of polynomials over `F` into power series over the extension `L`. -/
noncomputable def toPS {σ F L : Type*} [CommRing F] [CommRing L] [Algebra F L] :
    MvPolynomial σ F →+* MvPowerSeries σ L :=
  (MvPolynomial.coeToMvPowerSeries.ringHom).comp (MvPolynomial.map (algebraMap F L))

/-- `f(0, Y) ∈ F[Y]`: the coefficients of `f` evaluated at `X = 0`. -/
noncomputable def atZero {σ F : Type*} [CommRing F] (f : Polynomial (MvPolynomial σ F)) :
    Polynomial F :=
  f.map MvPolynomial.constantCoeff

/-- `Φ_β ∈ L[[X]]` (p. 23): the power-series root of `f(X, Y)` with constant term `β`, i.e.
`f(X, Φ_β) = 0` and `Φ_β(0) = β`. When `f` is monic and Hensel-ready at `0` (Lemma 2.26) such a
root exists and is unique for every root `β` of `f(0, Y)`; the definition picks one when one exists
(then it is that unique root) and is `0` otherwise. -/
noncomputable def psRoot {σ F : Type*} [CommRing F] (f : Polynomial (MvPolynomial σ F))
    (L : Type*) [CommRing L] [Algebra F L] (β : L) : MvPowerSeries σ L :=
  open Classical in
  if h : ∃ Φ : MvPowerSeries σ L, MvPowerSeries.constantCoeff Φ = β ∧
      (f.map (toPS (L := L))).eval Φ = 0 then h.choose else 0

/-- The substitution `X_i ↦ T X_i` (p. 24): `P(X) ↦ P(TX) ∈ F[X][T]`. -/
noncomputable def scaleT {n : ℕ} {F : Type*} [CommRing F] :
    MvPolynomial (Fin n) F →+* Polynomial (MvPolynomial (Fin n) F) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X)

/-- `F(T, Y) := f(TX, Y)` (p. 24). -/
noncomputable def bigF {n : ℕ} {F : Type*} [CommRing F] (f : Polynomial (MvPolynomial (Fin n) F)) :
    Polynomial (Polynomial (MvPolynomial (Fin n) F)) :=
  f.map scaleT

/-- `deg_T F` for `F(T, Y) ∈ F[X][T, Y]`: the largest `T`-degree of a `Y`-coefficient. -/
noncomputable def degT {A : Type*} [Semiring A] (G : Polynomial (Polynomial A)) : ℕ :=
  G.support.sup fun i => (G.coeff i).natDegree

/-- `F(0, Y) ∈ F[X][Y]` for `F(T, Y)`: set `T = 0`. -/
noncomputable def atTZero {A : Type*} [CommRing A] (G : Polynomial (Polynomial A)) : Polynomial A :=
  G.map (Polynomial.evalRingHom 0)

/-- `Φ_β(T) ∈ L[X][[T]]` (pp. 24, 30): the power-series root in `T` of `F(T, Y)`, with coefficients
in `L[X]`, whose constant term is `β`. When `F` is monic in `Y` and Hensel-ready at `T = 0` it is
unique; the definition picks one when one exists and is `0` otherwise. -/
noncomputable def psRootT {n : ℕ} {F : Type*} [CommRing F]
    (G : Polynomial (Polynomial (MvPolynomial (Fin n) F))) (L : Type*) [CommRing L] [Algebra F L]
    (β : L) : PowerSeries (MvPolynomial (Fin n) L) :=
  open Classical in
  if h : ∃ Φ : PowerSeries (MvPolynomial (Fin n) L),
      PowerSeries.constantCoeff Φ = MvPolynomial.C β ∧
      (G.map ((Polynomial.coeToPowerSeries.ringHom).comp
        (Polynomial.mapRingHom (MvPolynomial.map (algebraMap F L))))).eval Φ = 0 then h.choose
  else 0

/-- **`R_e(Z)`** (p. 24, and Appendix B.2 p. 53), evaluated in a commutative ring `A` that receives
`F[X][T]` through `φ`, at a point `z ∈ A` substituted for `Z`:
`R_e(z) = z + Σ_{m=0}^{2e(D+1)} [Y^{em+e-2}] { (e!/∂_Y^e F(0, z))^{m+1} · (∂_Y F(T, Y + z)/e) ·
((∂_Y^e F(0, z)/e!) Y^e − F(T, Y + z))^m }`.
Divisions are by `e`, `e!` and `∂_Y^e F(0, z)`, written with `Ring.inverse` (the inverse of a unit);
under the hypotheses where `R_e` is used these are units. The coefficient `[Y^{em+e-2}]` is `0` when
`em + e − 2 < 0` (only `e = 1, m = 0`). Taking `A` the field of rational functions in `X, T, Z` and
`z = Z` gives the rational function `R_e(Z)`; taking `A = L[X][T]` and `z = β` gives `R_e(β)`. -/
noncomputable def Rgen {R A : Type*} [CommRing R] [CommRing A] (φ : Polynomial R →+* A) (z : A)
    (e D : ℕ) (G : Polynomial (Polynomial R)) : A :=
  let Gz : Polynomial A := (G.map φ).comp (X + C z)
  let G0 : Polynomial A := (atTZero G).map (φ.comp Polynomial.C)
  let cz : A := (derivative^[e] G0).eval z
  let ef : A := (e.factorial : A)
  z + ∑ m ∈ Finset.range (2 * e * (D + 1) + 1),
    (if 2 ≤ e * m + e then
      ((C ((ef * Ring.inverse cz) ^ (m + 1) * Ring.inverse (e : A)) * derivative Gz *
        (C (cz * Ring.inverse ef) * X ^ e - Gz) ^ m).coeff (e * m + e - 2))
    else 0)

/-- The coefficientwise truncation `P Trunc T^{D+1}` of `P ∈ (L[X][[T]])[Y]`, a polynomial in `T`
and `Y` (outer `Y`, inner `T`). -/
noncomputable def truncTY {B : Type*} [CommRing B] (N : ℕ) (P : Polynomial (PowerSeries B)) :
    Polynomial (Polynomial B) :=
  ∑ i ∈ Finset.range (P.natDegree + 1), Polynomial.monomial i (PowerSeries.trunc N (P.coeff i))

/-- **Factor-lift** (Definition 3.3, p. 30) of a factor `q(Y)` of `F(0, Y)`, `S` the multiset of
roots of `q` in `L`: `∏_{β ∈ S} (Y − Φ_β(T)) Trunc T^{D+1}`, with `D = deg_T F`. -/
noncomputable def factorLift {n : ℕ} {F : Type*} [CommRing F]
    (G : Polynomial (Polynomial (MvPolynomial (Fin n) F))) (L : Type*) [Field L] [Algebra F L]
    (q : Polynomial F) : Polynomial (Polynomial (MvPolynomial (Fin n) L)) :=
  truncTY (degT G + 1)
    (((q.map (algebraMap F L)).roots.map fun β => (X - C (psRootT G L β))).prod)

/-- The polynomial `F(T, Y) ∈ F[X][T][Y]` as an element of `F[X_1, …, X_n, T, Y]`, variables
`Sum.inl i = X_i`, `Sum.inr 0 = T`, `Sum.inr 1 = Y` (the variable set a circuit for `F(T, Y)` uses). -/
noncomputable def toMvXTY {n : ℕ} {F : Type*} [CommRing F]
    (G : Polynomial (Polynomial (MvPolynomial (Fin n) F))) : MvPolynomial (Fin n ⊕ Fin 2) F :=
  G.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.rename Sum.inl).toRingHom
    (MvPolynomial.X (Sum.inr 0))) (MvPolynomial.X (Sum.inr 1))

/-- The embedding of `F[X][T]` into the field `F(X, T, Z)` of rational functions in the variables
`Sum.inl i = X_i`, `Sum.inr 0 = T`, `Sum.inr 1 = Z`, in which `R_e(Z)` is a rational function. -/
noncomputable def embXT {n : ℕ} {F : Type*} [Field F] :
    Polynomial (MvPolynomial (Fin n) F) →+* FractionRing (MvPolynomial (Fin n ⊕ Fin 2) F) :=
  (algebraMap (MvPolynomial (Fin n ⊕ Fin 2) F) (FractionRing (MvPolynomial (Fin n ⊕ Fin 2) F))).comp
    (Polynomial.eval₂RingHom (MvPolynomial.rename Sum.inl).toRingHom (MvPolynomial.X (Sum.inr 0)))

end SparseLowFactors.BoundedDeg


