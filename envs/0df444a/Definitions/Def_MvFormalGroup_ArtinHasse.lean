-- Prove2me | Definitions.Def_MvFormalGroup_ArtinHasse
-- name    : MvFormalGroup_ArtinHasse
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/2de536aa-2898-511c-b66f-4f77032d7cc6
-- title:
--   Artin–Hasse exponential and Witt coordinate polynomials
-- statement:
--   Fix a prime $p$. For $n\in\mathbb N$, `moebExponent p n` is $0$ if $p\mid n$ and otherwise the $p$-adic integer $-\mu(n)\cdot n^{-1}$ (the inverse taken in $\mathbb Z_p$, where $n$ is a unit); `moebFactor p n` is $1$ for $n=0$ and otherwise the binomial series of $\mathbb Z_p$ with exponent `moebExponent p n` substituted at $-X^n$, i.e. the $p$-integral power series $(1-X^n)^{-\mu(n)/n}$; `moebProd p k` is the finite product of these factors over $0<n\le k$ with $p\nmid n$; and `series p` is the power series whose $k$-th coefficient is the $k$-th coefficient of `moebProd p k`, i.e. the Artin–Hasse exponential $E_p\in 1+X\,\mathbb Z_p[[X]]$ presented as the Möbius product, the truncation being harmless because the omitted factors are $\equiv 1$ modulo $X^{k+1}$. Its constant and linear coefficients are both $1$.
--
--   Over a commutative $\mathbb Z_p$-algebra $A$, `scaled p q z` is the series with $k$-th coefficient the image of the $(k/q)$-th coefficient of $E_p$ times $z^{k/q}$ when $q\mid k$ and $0$ otherwise, that is $E_p(zX^q)$; it has constant coefficient $1$ and commutes with $\mathbb Z_p$-algebra maps. `prodSeries p z N` is $\prod_{m<N}E_p(z_mX^{p^m})$ for a sequence $z:\mathbb N\to A$, again with constant coefficient $1$ and compatible with base change. The coordinate polynomials `coord p n` $\in\mathbb Z_p[x_0,x_1,\dots]$ are the coefficient of $X^{n+1}$ in `prodSeries` evaluated at the variables $x_m$ with $N=n+1$; `aeval_coord` evaluates them at any sequence $z$ in $A$ as the coefficient of $X^{n+1}$ in $\prod_{m\le n}E_p(z_mX^{p^m})$, `isWeightedHomogeneous_coord` shows `coord p n` is weighted homogeneous of weight $n+1$ for the weights $x_m\mapsto p^m$, and `coord_zero` gives $x_0$. Finally `toCharP p R` is the ring map $\mathbb Z_p\to\mathbb Z/p\to R$ for $R$ of characteristic $p$, and `fam p R n` is the image of `coord p n` under it, viewed as a multivariate formal power series in the variables indexed by $\mathbb N$. The module records that the coefficients of `fam` are the reductions of those of `coord`, that a nonzero coefficient forces weight $n+1$, that each `fam p R n` has zero constant term, that the whole family is substitutable (`MvPowerSeries.HasSubst`), that `fam p R 0 = X 0`, and that the coefficient of $x_0$ in `fam p R n` is $1$ for $n=0$ and $0$ otherwise.
--
--   **Relation to Mathlib.** Built on Mathlib's `PadicInt`, `binomialSeries`, the Möbius function and (multivariate) power-series substitution; the Artin–Hasse exponential and the associated coordinate polynomials are the project's own definitions.
--
--   **Where it is used.** The family `fam p R` is in the shape of substitutable homomorphism data between multivariate formal power series over a ring $R$ of characteristic $p$, as used in the project's formal-group and Cartier-module development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvFormalGroup_ArtinHasse.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open PowerSeries

namespace MvFormalGroup

namespace ArtinHasse

variable (p : ℕ) [hp : Fact p.Prime]

def moebExponent (n : ℕ) : ℤ_[p] :=
  if p ∣ n then 0 else -(ArithmeticFunction.moebius n : ℤ_[p]) * Ring.inverse (n : ℤ_[p])

def moebFactor (n : ℕ) : ℤ_[p]⟦X⟧ :=
  if n = 0 then 1 else (binomialSeries ℤ_[p] (moebExponent p n)).subst (-(X : ℤ_[p]⟦X⟧) ^ n)

def moebProd (k : ℕ) : ℤ_[p]⟦X⟧ :=
  ∏ n ∈ (Finset.Ioc 0 k).filter (fun n => ¬ p ∣ n), moebFactor p n

def series : ℤ_[p]⟦X⟧ :=
  PowerSeries.mk fun k => coeff k (moebProd p k)

theorem hasSubst_neg_X_pow {n : ℕ} (hn : n ≠ 0) : HasSubst (-(X : ℤ_[p]⟦X⟧) ^ n) :=
  HasSubst.of_constantCoeff_zero' (by simp [hn])

theorem constantCoeff_moebFactor (n : ℕ) : constantCoeff (moebFactor p n) = 1 := by
  unfold moebFactor
  split_ifs with hn
  · exact map_one _
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' (hasSubst_neg_X_pow p hn),
      finsum_eq_single _ 0 fun d hd => ?_]
    · simp
    · rw [coeff_zero_eq_constantCoeff_apply, map_pow, map_neg, map_pow, constantCoeff_X, zero_pow hn,
        neg_zero, zero_pow hd, smul_zero]

theorem constantCoeff_moebProd (k : ℕ) : constantCoeff (moebProd p k) = 1 := by
  rw [moebProd, map_prod]
  exact Finset.prod_eq_one fun n _ => constantCoeff_moebFactor p n

theorem constantCoeff_series : constantCoeff (series p) = 1 := by
  rw [series, PowerSeries.constantCoeff_mk, coeff_zero_eq_constantCoeff_apply, constantCoeff_moebProd]

theorem coeff_one_series : coeff 1 (series p) = 1 := by
  rw [series, coeff_mk, moebProd]
  have hset : (Finset.Ioc 0 1).filter (fun n => ¬ p ∣ n) = {1} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h0, h1⟩, -⟩; omega
    · rintro rfl; exact ⟨⟨zero_lt_one, le_rfl⟩, hp.out.not_dvd_one⟩
  have hneg : ∀ d : ℕ, (-(X : ℤ_[p]⟦X⟧)) ^ d = ((-1 : ℤ_[p]) ^ d) • (X : ℤ_[p]⟦X⟧) ^ d := fun d => by
    rw [← neg_one_smul ℤ_[p] (X : ℤ_[p]⟦X⟧), smul_pow]
  rw [hset, Finset.prod_singleton, moebFactor, if_neg one_ne_zero, pow_one,
    coeff_subst' (HasSubst.of_constantCoeff_zero' (by simp)), finsum_eq_single _ 1 fun d hd => ?_]
  · have hexp : moebExponent p 1 = -1 := by
      rw [moebExponent, if_neg hp.out.not_dvd_one, ArithmeticFunction.moebius_apply_one, Int.cast_one,
        Nat.cast_one, Ring.inverse_one, mul_one]
    rw [binomialSeries_coeff, hexp, Ring.choose_one_right, hneg 1, map_smul, pow_one, pow_one,
      coeff_one_X]
    simp
  · rw [hneg d, map_smul, coeff_X_pow, if_neg (Ne.symm hd), smul_zero, smul_zero]

variable {A : Type*} [CommRing A] [Algebra ℤ_[p] A]

def scaled (q : ℕ) (z : A) : A⟦X⟧ :=
  PowerSeries.mk fun k => if q ∣ k then algebraMap ℤ_[p] A (coeff (k / q) (series p)) * z ^ (k / q) else 0

theorem coeff_scaled (q : ℕ) (z : A) (k : ℕ) :
    coeff k (scaled p q z) =
      if q ∣ k then algebraMap ℤ_[p] A (coeff (k / q) (series p)) * z ^ (k / q) else 0 :=
  coeff_mk _ _

theorem constantCoeff_scaled (q : ℕ) (z : A) : constantCoeff (scaled p q z) = 1 := by
  rw [scaled, PowerSeries.constantCoeff_mk, if_pos (dvd_zero q), Nat.zero_div,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_series, map_one, pow_zero, mul_one]

theorem map_scaled {B : Type*} [CommRing B] [Algebra ℤ_[p] B] (φ : A →ₐ[ℤ_[p]] B) (q : ℕ) (z : A) :
    PowerSeries.map (φ : A →+* B) (scaled p q z) = scaled p q (φ z) := by
  ext k
  rw [coeff_map, coeff_scaled, coeff_scaled]
  split_ifs
  · rw [RingHom.coe_coe, map_mul, map_pow, AlgHom.commutes]
  · exact map_zero _

def prodSeries (z : ℕ → A) (N : ℕ) : A⟦X⟧ :=
  ∏ m ∈ Finset.range N, scaled p (p ^ m) (z m)

theorem constantCoeff_prodSeries (z : ℕ → A) (N : ℕ) : constantCoeff (prodSeries p z N) = 1 := by
  rw [prodSeries, map_prod]
  exact Finset.prod_eq_one fun m _ => constantCoeff_scaled p _ _

theorem map_prodSeries {B : Type*} [CommRing B] [Algebra ℤ_[p] B] (φ : A →ₐ[ℤ_[p]] B) (z : ℕ → A)
    (N : ℕ) : PowerSeries.map (φ : A →+* B) (prodSeries p z N) = prodSeries p (fun m => φ (z m)) N := by
  rw [prodSeries, prodSeries, map_prod]
  exact Finset.prod_congr rfl fun m _ => map_scaled p φ _ _

def coord (n : ℕ) : MvPolynomial ℕ ℤ_[p] :=
  coeff (n + 1) (prodSeries p (fun m => (MvPolynomial.X m : MvPolynomial ℕ ℤ_[p])) (n + 1))

theorem aeval_coord (z : ℕ → A) (n : ℕ) :
    MvPolynomial.aeval z (coord p n) = coeff (n + 1) (prodSeries p z (n + 1)) := by
  rw [coord]
  change ((MvPolynomial.aeval z : MvPolynomial ℕ ℤ_[p] →ₐ[ℤ_[p]] A) : MvPolynomial ℕ ℤ_[p] →+* A)
      (coeff (n + 1) (prodSeries p (fun m => (MvPolynomial.X m : MvPolynomial ℕ ℤ_[p])) (n + 1))) = _
  rw [← coeff_map, map_prodSeries]
  simp

theorem isWeightedHomogeneous_coeff_scaled_X (m k : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun i : ℕ => p ^ i)
      (coeff k (scaled p (p ^ m) (MvPolynomial.X m : MvPolynomial ℕ ℤ_[p]))) k := by
  rw [coeff_scaled]
  split_ifs with hdvd
  · rw [MvPolynomial.algebraMap_eq]
    have h := ((MvPolynomial.isWeightedHomogeneous_X ℤ_[p] (fun i : ℕ => p ^ i) m).pow (k / p ^ m)).C_mul
      (coeff (k / p ^ m) (series p))
    have hw : (k / p ^ m) • (fun i : ℕ => p ^ i) m = k := by
      show (k / p ^ m) * p ^ m = k
      exact Nat.div_mul_cancel hdvd
    rwa [hw] at h
  · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _

theorem isWeightedHomogeneous_coord (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun i : ℕ => p ^ i) (coord p n) (n + 1) := by
  classical
  rw [coord, prodSeries, coeff_prod]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun l hl => ?_
  have hsum : (Finset.range (n + 1)).sum l = n + 1 := (Finset.mem_finsuppAntidiag.mp hl).1
  have h := MvPolynomial.IsWeightedHomogeneous.prod (Finset.range (n + 1))
    (fun m => coeff (l m) (scaled p (p ^ m) (MvPolynomial.X m : MvPolynomial ℕ ℤ_[p]))) (fun m => l m)
    (w := fun i : ℕ => p ^ i) fun m _ => isWeightedHomogeneous_coeff_scaled_X p m (l m)
  rwa [hsum] at h

theorem coord_zero : coord p 0 = MvPolynomial.X 0 := by
  rw [coord, prodSeries, zero_add, Finset.prod_range_one, pow_zero, coeff_scaled, if_pos (one_dvd _),
    Nat.div_one, coeff_one_series, map_one, one_mul, pow_one]

variable (R : Type u) [CommRing R] [CharP R p]

def toCharP : ℤ_[p] →+* R := (ZMod.castHom (dvd_refl p) R).comp (PadicInt.toZMod (p := p))

def fam (n : ℕ) : MvPowerSeries ℕ R :=
  ↑(MvPolynomial.map (toCharP p R) (coord p n))

theorem coeff_fam (n : ℕ) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (fam p R n) = toCharP p R (MvPolynomial.coeff e (coord p n)) := by
  rw [fam, MvPolynomial.coeff_coe, MvPolynomial.coeff_map]

theorem weight_eq_of_coeff_fam_ne_zero {n : ℕ} {e : ℕ →₀ ℕ} (h : MvPowerSeries.coeff e (fam p R n) ≠ 0) :
    Finsupp.weight (fun i : ℕ => p ^ i) e = n + 1 := by
  rw [coeff_fam] at h
  have h' : MvPolynomial.coeff e (coord p n) ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  exact isWeightedHomogeneous_coord p n h'

theorem constantCoeff_fam (n : ℕ) : MvPowerSeries.constantCoeff (fam p R n) = 0 := by
  by_contra h
  have h' : MvPowerSeries.coeff (0 : ℕ →₀ ℕ) (fam p R n) ≠ 0 := by
    rwa [MvPowerSeries.coeff_zero_eq_constantCoeff]
  have hw := weight_eq_of_coeff_fam_ne_zero p R h'
  simp at hw

theorem hasSubst_fam : MvPowerSeries.HasSubst (fam p R) := by
  refine ⟨fun n => by rw [constantCoeff_fam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_lt_nat (Finsupp.weight (fun i : ℕ => p ^ i) e)).subset ?_
  intro n hn
  have hw := weight_eq_of_coeff_fam_ne_zero p R hn
  show n < Finsupp.weight (fun i : ℕ => p ^ i) e
  omega

theorem fam_zero : fam p R 0 = MvPowerSeries.X 0 := by
  rw [fam, coord_zero, MvPolynomial.map_X, MvPolynomial.coe_X]

theorem coeff_single_zero_fam (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 1) (fam p R n) = if n = 0 then 1 else 0 := by
  classical
  split_ifs with hn
  · subst hn
    rw [fam_zero, MvPowerSeries.coeff_X, if_pos rfl]
  · by_contra h
    have hw := weight_eq_of_coeff_fam_ne_zero p R (Ne.symm h ∘ Eq.symm)
    rw [Finsupp.weight_single, pow_zero, smul_eq_mul, mul_one] at hw
    exact hn (by omega)

end ArtinHasse

end MvFormalGroup

end


