-- Prove2me | Definitions.Def_GoldProxGap_locator
-- name    : GoldProxGap_locator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:21:47.726314+00:00
-- url     : https://prove2.me/theorems/39066395-9427-40eb-87af-eb6300a1b15b
-- title:
--   Locators $L_S$, the constant $\lambda=L_S'$, Frobenius roots $c^{1/b}$ and polynomial roots $(L_D-\lambda X)^{1/b}$
-- statement:
--   For a finite set $S$ of field elements, its **locator** (vanishing polynomial) is
--   $$
--   L_S(X)=\prod_{x\in S}(X-x).
--   $$
--   For an affine $\mathbb F_b$-space $D$ (in particular a binary additive domain) the derivative $L_D'$ is a nonzero constant $\lambda$, the coefficient of $X$ in $L_D$.
--
--   In a finite field of characteristic $p$, and for $b=p^k$, the map $x\mapsto x^b$ is a bijection; $c^{1/b}$ is its inverse (for $b=2$, the square root $\sqrt c$). For a polynomial $P$ all of whose exponents are divisible by $b$, $P^{1/b}$ is obtained by dividing every exponent by $b$ and taking $b$-th roots of the coefficients. In particular $R=(L_D-\lambda X)^{1/b}$ is the polynomial with $R(x)^b=L_D(x)-\lambda x$.
--
--   **Formalization Note** `locLam S` is the coefficient of $X$ in $L_S$; for the domains of the paper it equals the constant $L_S'$. `frobRoot F p k` is the inverse of the iterated Frobenius `iterateFrobeniusEquiv F p k`. `polyRoot p k P` is Mathlib's `Polynomial.contract (p^k) P` with each coefficient replaced by its $p^k$-th root; on a polynomial with exponents not all divisible by $b$ it discards the other terms, and it is only applied to $L_D-\lambda X$ and to derivatives in characteristic two, whose exponents are divisible by $b$.
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Definition 3.8, p.20; paragraph before Lemma 3.13, p.22

import Mathlib

open Polynomial

namespace GoldProxGap

/-!
# Locators and Frobenius roots

Dao, Kominers, Thaler, Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary
Fields*, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…), Definition 3.8,
p.20, and the paragraph before Lemma 3.13, p.22.

**Formalization Note.**
* `locator S = ∏_{x ∈ S} (X − x)` (Definition 3.8).
* `locLam S` is the coefficient of `X` in `L_S`. For an affine flat (or affine `F_b`-space) the
  derivative `L_S′` is a nonzero constant (p.20, p.22), and that constant is this coefficient;
  it is the paper's `λ = L′_D` (and `λ₀` of §5.3).
* `frobRoot F p k` is the inverse of the Frobenius power `x ↦ x ^ (p ^ k)`, a bijection on a
  perfect ring of characteristic `p` (every finite field); `frobRoot F p k c` is the paper's unique
  `b`-th root `c^{1/b}` with `b = p ^ k` (p.22), and for `p = 2, k = 1` the square root `√c`.
* `polyRoot p k P` takes the coefficients of `X^{b n}` in `P` (Mathlib's `Polynomial.contract b`)
  and replaces each by its `b`-th root: for a polynomial whose exponents are all divisible by `b`
  it is the unique polynomial `R` with `R(x)^b = P(x)` coefficientwise, which is how the paper
  defines `(L_D − λX)^{1/b}` and `√(L_D − λX)` (p.22).
-/

/-- Definition 3.8: the locator (vanishing polynomial) `L_S(X) = ∏_{x ∈ S} (X − x)`. -/
noncomputable def locator {F : Type*} [Field F] (S : Finset F) : F[X] :=
  ∏ x ∈ S, (X - C x)

/-- The coefficient of `X` in `L_S`; for an affine flat it is the constant derivative `λ = L_S′`. -/
noncomputable def locLam {F : Type*} [Field F] (S : Finset F) : F :=
  (locator S).coeff 1

/-- The `p ^ k`-th root: the inverse of the Frobenius power `x ↦ x ^ (p ^ k)`. -/
noncomputable def frobRoot (F : Type*) [CommRing F] (p k : ℕ) [ExpChar F p] [PerfectRing F p] :
    F ≃+* F :=
  (iterateFrobeniusEquiv F p k).symm

/-- `P^{1/b}` with `b = p ^ k`: keep the coefficients of the exponents divisible by `b`, divide
those exponents by `b`, and take `b`-th roots of the coefficients. -/
noncomputable def polyRoot {F : Type*} [CommRing F] (p k : ℕ) [ExpChar F p] [PerfectRing F p]
    (P : F[X]) : F[X] :=
  (contract (p ^ k) P).map (frobRoot F p k : F →+* F)

end GoldProxGap


