-- Prove2me | Definitions.Def_MvFormalGroup_BigWittFrobenius
-- name    : MvFormalGroup_BigWittFrobenius
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/c6ff7ae5-b12d-5744-bf5e-3b273d55f763
-- title:
--   Witt coordinates, Frobenius and p-typical projector polynomial families
-- statement:
--   Work in one variable $T$ over the ring $\mathbb{Z}[a_0,a_1,\dots]$ of integral polynomials in countably many variables, with $a_m$ written `X m`. The generic series `genSeries` is $1+\sum_{m\ge 0}a_mT^{m+1}$. The auxiliary products `killProd` are defined recursively by `killProd 0 = genSeries` and $\mathrm{killProd}(k+1) = \mathrm{killProd}(k)\cdot(1 - C(c_k)T^{k+1})$, where $c_k$ is the coefficient of $T^{k+1}$ in `killProd k`; the **Witt coordinate** `wittCoord k` is exactly that coefficient $c_k$, so that $1+\sum_m a_mT^{m+1}=\prod_k(1-b_kT^{k+1})^{-1}$ with $b_k=$ `wittCoord k`. Accompanying lemmas give $b_0=a_0$, the closed form `killProd k = genSeries · ∏_{i<k}(1-C(b_i)T^{i+1})`, the vanishing of the coefficients of $T,\dots,T^{k}$ in `killProd k`, constant coefficient $1$, and vanishing constant term of each $b_k$.
--
--   For weights, `awt m = m+1`; `IsIsobaric n P` is the predicate that for every $j$ the coefficient of $T^j$ in $P$ is weighted homogeneous of weight $nj$ for `awt`. It is closed under products, differences, powers and finite products, holds for `genSeries` and `killProd` with $n=1$, and yields that $b_k$ is weighted homogeneous of weight $k+1$.
--
--   `geomSeries c e` is $\sum_{q}c^qT^{eq}$, the inverse of $1-cT^e$ for $e\neq 0$. With $d_k=\gcd(k+1,n)$, `frobFactor n k` is $\bigl(1-b_k^{\,n/d_k}T^{(k+1)/d_k}\bigr)^{-d_k}$, and the **Frobenius polynomial** `frobPoly n m` is the coefficient of $T^{m+1}$ in $\prod_{k<n(m+1)}$ `frobFactor n k`; it is weighted homogeneous of weight $n(m+1)$, has zero constant term for $n\neq0$, vanishes identically for $n=0$, and `frobPoly 1 m = X m`. The **$p$-typical projector** polynomials are `projPoly p k = wittCoord (p^k-1)`, weighted homogeneous of weight $p^k$.
--
--   The ring homomorphism `evalOmegaInv t` specialises $a_m\mapsto t^{m+1}$ coefficientwise, i.e. restricts to the curve $(1-tT)^{-1}$; under it `genSeries` becomes `geomSeries t 1`, $b_k$ becomes $t$ for $k=0$ and $0$ otherwise, `frobPoly n m` becomes $t^{n(m+1)}$ for $n\neq0$, and `projPoly p k` becomes $t$ for $k=0$ and $0$ otherwise when $p\ge 2$. Finally `toFam R P` reduces an integral polynomial modulo the canonical map $\mathbb{Z}\to R$ and views it in `MvPowerSeries ℕ R`; the families `wittCoordFam`, `frobFam n`, `projFam p` so obtained have zero constant coefficients and are shown to be admissible for substitution (`MvPowerSeries.HasSubst`), the last for $p\ge2$, via the weight bounds coming from weighted homogeneity.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient machinery used here — `MvPolynomial`, `PowerSeries`/`MvPowerSeries` with `MvPowerSeries.subst` and `HasSubst`, and `IsWeightedHomogeneous` — but not these coordinate polynomials for the big Witt formal group, its Frobenius operators or the $p$-typical projector; those are the project's own, and are unrelated to Mathlib's `WittVector` polynomials.
--
--   **Where it is used.** These families are the integral coordinate data for the big Witt formal group, whose group law is formalised in the companion module, and they provide the Frobenius endomorphisms and Cartier's $p$-typical projector in the form (families of power series with nilpotent-friendly substitution) in which homomorphisms out of the Witt formal groups are expressed further on in the formal-group layer of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvFormalGroup_BigWittFrobenius.lean

import Mathlib
import Definitions.Def_MvFormalGroup_BigWittLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

namespace BigWittLaw

open MvPolynomial

def genSeries : PowerSeries (MvPolynomial ℕ ℤ) :=
  PowerSeries.mk fun n => Nat.casesOn n 1 fun m => X m

@[simp] theorem coeff_genSeries_zero : PowerSeries.coeff 0 genSeries = 1 := by
  simp [genSeries, PowerSeries.coeff_mk]

@[simp] theorem coeff_genSeries_succ (m : ℕ) : PowerSeries.coeff (m + 1) genSeries = X m := by
  simp [genSeries, PowerSeries.coeff_mk]

@[simp] theorem constantCoeff_genSeries : PowerSeries.constantCoeff genSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_genSeries_zero]

def killProd : ℕ → PowerSeries (MvPolynomial ℕ ℤ)
  | 0 => genSeries
  | k + 1 => killProd k *
      (1 - PowerSeries.C (PowerSeries.coeff (k + 1) (killProd k)) * PowerSeries.X ^ (k + 1))

def wittCoord (k : ℕ) : MvPolynomial ℕ ℤ := PowerSeries.coeff (k + 1) (killProd k)

theorem killProd_zero : killProd 0 = genSeries := rfl

theorem killProd_succ (k : ℕ) :
    killProd (k + 1) = killProd k * (1 - PowerSeries.C (wittCoord k) * PowerSeries.X ^ (k + 1)) := rfl

theorem wittCoord_eq (k : ℕ) : wittCoord k = PowerSeries.coeff (k + 1) (killProd k) := rfl

@[simp] theorem wittCoord_zero : wittCoord 0 = X 0 := by
  rw [wittCoord_eq, killProd_zero, coeff_genSeries_succ]

theorem killProd_eq_mul_prod (k : ℕ) :
    killProd k = genSeries * ∏ i ∈ Finset.range k,
      (1 - PowerSeries.C (wittCoord i) * PowerSeries.X ^ (i + 1)) := by
  induction k with
  | zero => simp [killProd_zero]
  | succ k ih => rw [killProd_succ, ih, Finset.prod_range_succ, mul_assoc]

@[simp] theorem constantCoeff_killProd (k : ℕ) : PowerSeries.constantCoeff (killProd k) = 1 := by
  induction k with
  | zero => exact constantCoeff_genSeries
  | succ k ih =>
    rw [killProd_succ, map_mul, ih, one_mul, map_sub, map_one, map_mul, map_pow,
      PowerSeries.constantCoeff_X, zero_pow (Nat.succ_ne_zero k), mul_zero, sub_zero]

theorem coeff_mul_one_sub_C_mul_X_pow {A : Type*} [CommRing A] (P : PowerSeries A) (c : A)
    (k j : ℕ) :
    PowerSeries.coeff j (P * (1 - PowerSeries.C c * PowerSeries.X ^ (k + 1))) =
      PowerSeries.coeff j P - if k + 1 ≤ j then c * PowerSeries.coeff (j - (k + 1)) P else 0 := by
  rw [mul_sub, mul_one, map_sub]
  congr 1
  split_ifs with h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show k + 1 + d = d + (k + 1) by omega, ← mul_assoc, mul_comm P, mul_assoc,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow, Nat.add_sub_cancel]
  · rw [not_le] at h
    rw [← mul_assoc, mul_comm P, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
      Finset.sum_eq_zero, mul_zero]
    rintro ⟨i, l⟩ hil
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hil
    rw [PowerSeries.coeff_X_pow, if_neg, mul_zero]
    omega

theorem coeff_killProd_eq_zero {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    PowerSeries.coeff j (killProd k) = 0 := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    rw [killProd_succ, coeff_mul_one_sub_C_mul_X_pow]
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · rw [if_neg (by omega), sub_zero]
      exact ih hj (by omega)
    · have hjk' : j = k + 1 := le_antisymm hjk h
      subst hjk'
      rw [if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        constantCoeff_killProd, mul_one, ← wittCoord_eq, sub_self]

abbrev awt : ℕ → ℕ := fun m => m + 1

def IsIsobaric (n : ℕ) (P : PowerSeries (MvPolynomial ℕ ℤ)) : Prop :=
  ∀ j, IsWeightedHomogeneous awt (PowerSeries.coeff j P) (n * j)

theorem IsIsobaric.coeff {n : ℕ} {P : PowerSeries (MvPolynomial ℕ ℤ)} (h : IsIsobaric n P) (j : ℕ) :
    IsWeightedHomogeneous awt (PowerSeries.coeff j P) (n * j) := h j

theorem isIsobaric_one (n : ℕ) : IsIsobaric n 1 := by
  intro j
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · subst h; rw [mul_zero]; exact isWeightedHomogeneous_one ℤ awt
  · exact isWeightedHomogeneous_zero ℤ awt _

theorem IsIsobaric.mul {n : ℕ} {P Q : PowerSeries (MvPolynomial ℕ ℤ)} (hP : IsIsobaric n P)
    (hQ : IsIsobaric n Q) : IsIsobaric n (P * Q) := by
  intro j
  rw [PowerSeries.coeff_mul]
  refine IsWeightedHomogeneous.sum _ _ _ fun il hil => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hil
  have h := (hP il.1).mul (hQ il.2)
  rwa [← mul_add, hil] at h

theorem IsIsobaric.sub {n : ℕ} {P Q : PowerSeries (MvPolynomial ℕ ℤ)} (hP : IsIsobaric n P)
    (hQ : IsIsobaric n Q) : IsIsobaric n (P - Q) := by
  intro j
  rw [map_sub]
  exact (weightedHomogeneousSubmodule ℤ awt (n * j)).sub_mem (hP j) (hQ j)

theorem IsIsobaric.prod {n : ℕ} {ι : Type*} (s : Finset ι) (P : ι → PowerSeries (MvPolynomial ℕ ℤ))
    (h : ∀ i ∈ s, IsIsobaric n (P i)) : IsIsobaric n (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact isIsobaric_one n
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

theorem IsIsobaric.pow {n : ℕ} {P : PowerSeries (MvPolynomial ℕ ℤ)} (hP : IsIsobaric n P) (e : ℕ) :
    IsIsobaric n (P ^ e) := by
  induction e with
  | zero => rw [pow_zero]; exact isIsobaric_one n
  | succ e ih => rw [pow_succ]; exact ih.mul hP

theorem isIsobaric_C_mul_X_pow {n e : ℕ} {c : MvPolynomial ℕ ℤ} (hc : IsWeightedHomogeneous awt c (n * e)) :
    IsIsobaric n (PowerSeries.C c * PowerSeries.X ^ e) := by
  intro j
  rw [PowerSeries.coeff_C_mul_X_pow]
  split_ifs with h
  · subst h; exact hc
  · exact isWeightedHomogeneous_zero ℤ awt _

theorem isIsobaric_genSeries : IsIsobaric 1 genSeries := by
  intro j
  cases j with
  | zero => rw [coeff_genSeries_zero, mul_zero]; exact isWeightedHomogeneous_one ℤ awt
  | succ m => rw [coeff_genSeries_succ, one_mul]; exact isWeightedHomogeneous_X ℤ awt m

theorem isIsobaric_killProd (k : ℕ) : IsIsobaric 1 (killProd k) := by
  induction k with
  | zero => exact isIsobaric_genSeries
  | succ k ih =>
    rw [killProd_succ]
    refine ih.mul ((isIsobaric_one 1).sub (isIsobaric_C_mul_X_pow ?_))
    exact ih (k + 1)

theorem isWeightedHomogeneous_wittCoord (k : ℕ) : IsWeightedHomogeneous awt (wittCoord k) (k + 1) := by
  have h := isIsobaric_killProd k (k + 1)
  rwa [one_mul] at h

theorem constantCoeff_wittCoord (k : ℕ) : constantCoeff (wittCoord k) = 0 := by
  by_contra h
  have h' : coeff (0 : ℕ →₀ ℕ) (wittCoord k) ≠ 0 := by rwa [← constantCoeff_eq]
  have hw := isWeightedHomogeneous_wittCoord k h'
  simp at hw

def geomSeries {A : Type*} [CommRing A] (c : A) (e : ℕ) : PowerSeries A :=
  PowerSeries.mk fun j => if e ∣ j then c ^ (j / e) else 0

theorem coeff_geomSeries {A : Type*} [CommRing A] (c : A) (e j : ℕ) :
    PowerSeries.coeff j (geomSeries c e) = if e ∣ j then c ^ (j / e) else 0 :=
  PowerSeries.coeff_mk _ _

@[simp] theorem constantCoeff_geomSeries {A : Type*} [CommRing A] (c : A) (e : ℕ) :
    PowerSeries.constantCoeff (geomSeries c e) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_geomSeries, if_pos (dvd_zero e),
    Nat.zero_div, pow_zero]

theorem one_sub_C_mul_X_pow_mul_geomSeries {A : Type*} [CommRing A] (c : A) {e : ℕ} (he : e ≠ 0) :
    (1 - PowerSeries.C c * PowerSeries.X ^ e) * geomSeries c e = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
  ext j
  rw [mul_comm, coeff_mul_one_sub_C_mul_X_pow, coeff_geomSeries, PowerSeries.coeff_one]
  by_cases hj : k + 1 ≤ j
  · rw [if_pos hj, coeff_geomSeries]
    have hj0 : j ≠ 0 := by omega
    rw [if_neg hj0]
    by_cases hd : k + 1 ∣ j
    · have hd' : k + 1 ∣ j - (k + 1) := Nat.dvd_sub hd (dvd_refl _)
      rw [if_pos hd, if_pos hd']
      obtain ⟨q, rfl⟩ := hd
      have hq : 1 ≤ q := by
        rcases q with _ | q
        · simp at hj
        · exact Nat.succ_pos q
      rw [show (k + 1) * q - (k + 1) = (k + 1) * (q - 1) by rw [Nat.mul_sub, mul_one],
        Nat.mul_div_cancel_left _ (Nat.succ_pos k), Nat.mul_div_cancel_left _ (Nat.succ_pos k),
        ← pow_succ', Nat.sub_add_cancel hq, sub_self]
    · have hd' : ¬ k + 1 ∣ j - (k + 1) := by
        intro h
        apply hd
        have := Nat.dvd_add h (dvd_refl (k + 1))
        rwa [Nat.sub_add_cancel hj] at this
      rw [if_neg hd, if_neg hd', mul_zero, sub_zero]
  · rw [if_neg hj, sub_zero]
    by_cases hj0 : j = 0
    · subst hj0
      rw [if_pos (dvd_zero _), if_pos rfl, Nat.zero_div, pow_zero]
    · rw [if_neg hj0, if_neg]
      rintro ⟨q, rfl⟩
      rcases q with _ | q
      · exact hj0 (mul_zero _)
      · apply hj
        calc k + 1 = (k + 1) * 1 := (mul_one _).symm
          _ ≤ (k + 1) * (q + 1) := Nat.mul_le_mul_left _ (by omega)

def frobFactor (n k : ℕ) : PowerSeries (MvPolynomial ℕ ℤ) :=
  geomSeries (wittCoord k ^ (n / Nat.gcd (k + 1) n)) ((k + 1) / Nat.gcd (k + 1) n) ^ Nat.gcd (k + 1) n

def frobPoly (n m : ℕ) : MvPolynomial ℕ ℤ :=
  PowerSeries.coeff (m + 1) (∏ k ∈ Finset.range (n * (m + 1)), frobFactor n k)

@[simp] theorem constantCoeff_frobFactor (n k : ℕ) : PowerSeries.constantCoeff (frobFactor n k) = 1 := by
  rw [frobFactor, map_pow, constantCoeff_geomSeries, one_pow]

theorem isIsobaric_geomSeries {n e : ℕ} {c : MvPolynomial ℕ ℤ} (hc : IsWeightedHomogeneous awt c (n * e)) :
    IsIsobaric n (geomSeries c e) := by
  intro j
  rw [coeff_geomSeries]
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      rw [zero_mul, Nat.zero_div, pow_zero, mul_zero]
      exact isWeightedHomogeneous_one ℤ awt
    · rw [Nat.mul_div_cancel_left _ he]
      have h := hc.pow q
      rwa [smul_eq_mul, show q * (n * e) = n * (e * q) by ring] at h
  · exact isWeightedHomogeneous_zero ℤ awt _

theorem isIsobaric_frobFactor (n k : ℕ) : IsIsobaric n (frobFactor n k) := by
  refine (isIsobaric_geomSeries ?_).pow _
  have h := (isWeightedHomogeneous_wittCoord k).pow (n / Nat.gcd (k + 1) n)
  rw [smul_eq_mul] at h
  convert h using 1
  set g := Nat.gcd (k + 1) n with hg
  have hd : g ∣ k + 1 := Nat.gcd_dvd_left _ _
  have hd' : g ∣ n := Nat.gcd_dvd_right _ _
  calc n * ((k + 1) / g) = n / g * g * ((k + 1) / g) := by rw [Nat.div_mul_cancel hd']
    _ = n / g * (g * ((k + 1) / g)) := by ring
    _ = n / g * (k + 1) := by rw [Nat.mul_div_cancel' hd]

theorem isWeightedHomogeneous_frobPoly (n m : ℕ) :
    IsWeightedHomogeneous awt (frobPoly n m) (n * (m + 1)) :=
  (IsIsobaric.prod _ _ fun k _ => isIsobaric_frobFactor n k) (m + 1)

theorem constantCoeff_frobPoly {n : ℕ} (hn : n ≠ 0) (m : ℕ) : constantCoeff (frobPoly n m) = 0 := by
  by_contra h
  have h' : coeff (0 : ℕ →₀ ℕ) (frobPoly n m) ≠ 0 := by rwa [← constantCoeff_eq]
  have hw := isWeightedHomogeneous_frobPoly n m h'
  simp only [Finsupp.weight_apply, Finsupp.sum_zero_index] at hw
  exact absurd hw.symm (Nat.mul_ne_zero hn (Nat.succ_ne_zero m))

theorem frobPoly_zero_left (m : ℕ) : frobPoly 0 m = 0 := by
  rw [frobPoly, zero_mul, Finset.range_zero, Finset.prod_empty, PowerSeries.coeff_one, if_neg]
  exact Nat.succ_ne_zero m

theorem genSeries_eq_killProd_mul_prod_geomSeries (K : ℕ) :
    genSeries = killProd K * ∏ k ∈ Finset.range K, geomSeries (wittCoord k) (k + 1) := by
  rw [killProd_eq_mul_prod, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one, mul_one]
  intro k _
  exact one_sub_C_mul_X_pow_mul_geomSeries _ (Nat.succ_ne_zero k)

theorem coeff_prod_geomSeries_wittCoord {K j : ℕ} (hj : j ≤ K) :
    PowerSeries.coeff j (∏ k ∈ Finset.range K, geomSeries (wittCoord k) (k + 1)) =
      PowerSeries.coeff j genSeries := by
  rw [genSeries_eq_killProd_mul_prod_geomSeries K, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ', Nat.sub_zero,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_killProd, one_mul,
    Finset.sum_eq_zero, zero_add]
  intro i hi
  rw [coeff_killProd_eq_zero (Nat.succ_pos i) (by have := Finset.mem_range.mp hi; omega), zero_mul]

theorem frobFactor_one (k : ℕ) : frobFactor 1 k = geomSeries (wittCoord k) (k + 1) := by
  rw [frobFactor, Nat.gcd_one_right, Nat.div_one, Nat.div_one, pow_one, pow_one]

theorem frobPoly_one (m : ℕ) : frobPoly 1 m = X m := by
  rw [frobPoly, one_mul]
  simp only [frobFactor_one]
  rw [coeff_prod_geomSeries_wittCoord le_rfl, coeff_genSeries_succ]

section OmegaInv

variable {A : Type*} [CommRing A] (t : A)

def evalOmegaInv : PowerSeries (MvPolynomial ℕ ℤ) →+* PowerSeries A :=
  PowerSeries.map (MvPolynomial.aeval fun m : ℕ => t ^ (m + 1)).toRingHom

theorem coeff_evalOmegaInv (P : PowerSeries (MvPolynomial ℕ ℤ)) (j : ℕ) :
    PowerSeries.coeff j (evalOmegaInv t P) =
      MvPolynomial.aeval (fun m : ℕ => t ^ (m + 1)) (PowerSeries.coeff j P) :=
  PowerSeries.coeff_map _ _ _

theorem evalOmegaInv_genSeries : evalOmegaInv t genSeries = geomSeries t 1 := by
  ext j
  rw [coeff_evalOmegaInv, coeff_geomSeries, if_pos (one_dvd j), Nat.div_one]
  cases j with
  | zero => rw [coeff_genSeries_zero, map_one, pow_zero]
  | succ m => rw [coeff_genSeries_succ, MvPolynomial.aeval_X]

theorem evalOmegaInv_C_mul_X_pow (c : MvPolynomial ℕ ℤ) (e : ℕ) :
    evalOmegaInv t (PowerSeries.C c * PowerSeries.X ^ e) =
      PowerSeries.C (MvPolynomial.aeval (fun m : ℕ => t ^ (m + 1)) c) * PowerSeries.X ^ e := by
  rw [evalOmegaInv, map_mul, map_pow]
  simp [PowerSeries.map_C, PowerSeries.map_X]

theorem evalOmegaInv_killProd_succ (k : ℕ) : evalOmegaInv t (killProd (k + 1)) = 1 := by
  induction k with
  | zero =>
    rw [killProd_succ, map_mul, killProd_zero, evalOmegaInv_genSeries, map_sub, map_one,
      evalOmegaInv_C_mul_X_pow, wittCoord_zero, MvPolynomial.aeval_X, zero_add, pow_one, mul_comm]
    exact one_sub_C_mul_X_pow_mul_geomSeries t one_ne_zero
  | succ k ih =>
    rw [killProd_succ, map_mul, ih, one_mul, map_sub, map_one, evalOmegaInv_C_mul_X_pow, wittCoord_eq,
      ← coeff_evalOmegaInv, ih, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero _), map_zero, zero_mul,
      sub_zero]

theorem aeval_omegaInv_wittCoord (k : ℕ) :
    MvPolynomial.aeval (fun m : ℕ => t ^ (m + 1)) (wittCoord k) = if k = 0 then t else 0 := by
  cases k with
  | zero => rw [wittCoord_zero, MvPolynomial.aeval_X, if_pos rfl, zero_add, pow_one]
  | succ k =>
    rw [if_neg (Nat.succ_ne_zero k), wittCoord_eq, ← coeff_evalOmegaInv, evalOmegaInv_killProd_succ,
      PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero _)]

theorem evalOmegaInv_geomSeries (c : MvPolynomial ℕ ℤ) (e : ℕ) :
    evalOmegaInv t (geomSeries c e) = geomSeries (MvPolynomial.aeval (fun m : ℕ => t ^ (m + 1)) c) e := by
  ext j
  rw [coeff_evalOmegaInv, coeff_geomSeries, coeff_geomSeries]
  split_ifs
  · rw [map_pow]
  · rw [map_zero]

omit t in
theorem geomSeries_zero {e : ℕ} (he : e ≠ 0) : geomSeries (0 : A) e = 1 := by
  ext j
  rw [coeff_geomSeries, PowerSeries.coeff_one]
  by_cases hj : j = 0
  · subst hj; rw [if_pos (dvd_zero e), if_pos rfl, Nat.zero_div, pow_zero]
  · rw [if_neg hj]
    split_ifs with h
    · rw [zero_pow]
      intro h0
      rw [Nat.div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · exact he h0
      · exact hj (Nat.eq_zero_of_dvd_of_lt h h0)
    · rfl

theorem evalOmegaInv_frobFactor {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    evalOmegaInv t (frobFactor n k) = if k = 0 then geomSeries (t ^ n) 1 else 1 := by
  rw [frobFactor, map_pow, evalOmegaInv_geomSeries, map_pow, aeval_omegaInv_wittCoord]
  have hg : 0 < Nat.gcd (k + 1) n := Nat.gcd_pos_of_pos_left _ (Nat.succ_pos k)
  split_ifs with hk
  · subst hk
    rw [zero_add, Nat.gcd_one_left, Nat.div_one, Nat.div_one, pow_one]
  · have h1 : n / Nat.gcd (k + 1) n ≠ 0 :=
      Nat.div_ne_zero_iff.mpr ⟨hg.ne', Nat.gcd_le_right _ (Nat.pos_of_ne_zero hn)⟩
    have h2 : (k + 1) / Nat.gcd (k + 1) n ≠ 0 :=
      Nat.div_ne_zero_iff.mpr ⟨hg.ne', Nat.gcd_le_left _ (Nat.succ_pos k)⟩
    rw [zero_pow h1, geomSeries_zero h2, one_pow]

theorem aeval_omegaInv_frobPoly {n : ℕ} (hn : n ≠ 0) (m : ℕ) :
    MvPolynomial.aeval (fun m : ℕ => t ^ (m + 1)) (frobPoly n m) = t ^ (n * (m + 1)) := by
  rw [frobPoly, ← coeff_evalOmegaInv, map_prod]
  simp only [evalOmegaInv_frobFactor t hn]
  have h0 : (0 : ℕ) ∈ Finset.range (n * (m + 1)) :=
    Finset.mem_range.mpr (Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.succ_pos m))
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.filter_eq' , if_pos h0,
    Finset.prod_singleton, coeff_geomSeries, if_pos (one_dvd _), Nat.div_one, ← pow_mul]

end OmegaInv

def projPoly (p k : ℕ) : MvPolynomial ℕ ℤ := wittCoord (p ^ k - 1)

@[simp] theorem projPoly_zero (p : ℕ) : projPoly p 0 = X 0 := by
  rw [projPoly, pow_zero, Nat.sub_self, wittCoord_zero]

theorem isWeightedHomogeneous_projPoly {p : ℕ} (hp : 0 < p) (k : ℕ) :
    IsWeightedHomogeneous awt (projPoly p k) (p ^ k) := by
  have h := isWeightedHomogeneous_wittCoord (p ^ k - 1)
  rwa [Nat.sub_add_cancel (Nat.one_le_pow k p hp)] at h

theorem constantCoeff_projPoly (p k : ℕ) : constantCoeff (projPoly p k) = 0 :=
  constantCoeff_wittCoord _

theorem aeval_omegaInv_projPoly {A : Type*} [CommRing A] (t : A) {p : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    MvPolynomial.aeval (fun m : ℕ => t ^ (m + 1)) (projPoly p k) = if k = 0 then t else 0 := by
  rw [projPoly, aeval_omegaInv_wittCoord]
  cases k with
  | zero => rw [pow_zero, Nat.sub_self]
  | succ k =>
    rw [if_neg (Nat.succ_ne_zero k), if_neg]
    have : p ^ (k + 1) ≥ 2 := le_trans hp (Nat.le_self_pow (Nat.succ_ne_zero k) p)
    omega

section Families

variable (R : Type u) [CommRing R]

def toFam (P : MvPolynomial ℕ ℤ) : MvPowerSeries ℕ R :=
  ↑(MvPolynomial.map (Int.castRingHom R) P)

theorem coeff_toFam (P : MvPolynomial ℕ ℤ) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (toFam R P) = ((coeff e P : ℤ) : R) := by
  rw [toFam, MvPolynomial.coeff_coe, coeff_map, eq_intCast]

theorem constantCoeff_toFam {P : MvPolynomial ℕ ℤ} (hP : constantCoeff P = 0) :
    MvPowerSeries.constantCoeff (toFam R P) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_toFam, ← constantCoeff_eq, hP,
    Int.cast_zero]

theorem weight_eq_of_coeff_toFam_ne_zero {P : MvPolynomial ℕ ℤ} {w : ℕ}
    (hP : IsWeightedHomogeneous awt P w) {e : ℕ →₀ ℕ} (h : MvPowerSeries.coeff e (toFam R P) ≠ 0) :
    Finsupp.weight awt e = w := by
  rw [coeff_toFam] at h
  exact hP fun h0 => h (by rw [h0, Int.cast_zero])

def wittCoordFam : ℕ → MvPowerSeries ℕ R := fun k => toFam R (wittCoord k)

def frobFam (n : ℕ) : ℕ → MvPowerSeries ℕ R := fun m => toFam R (frobPoly n m)

def projFam (p : ℕ) : ℕ → MvPowerSeries ℕ R := fun k => toFam R (projPoly p k)

@[simp] theorem wittCoordFam_apply (k : ℕ) : wittCoordFam R k = toFam R (wittCoord k) := rfl
@[simp] theorem frobFam_apply (n m : ℕ) : frobFam R n m = toFam R (frobPoly n m) := rfl
@[simp] theorem projFam_apply (p k : ℕ) : projFam R p k = toFam R (projPoly p k) := rfl

theorem projFam_zero (p : ℕ) : projFam R p 0 = MvPowerSeries.X 0 := by
  rw [projFam_apply, projPoly_zero, toFam, map_X, MvPolynomial.coe_X]

theorem wittCoordFam_zero : wittCoordFam R 0 = MvPowerSeries.X 0 := by
  rw [wittCoordFam_apply, wittCoord_zero, toFam, map_X, MvPolynomial.coe_X]

theorem constantCoeff_wittCoordFam (k : ℕ) : MvPowerSeries.constantCoeff (wittCoordFam R k) = 0 :=
  constantCoeff_toFam R (constantCoeff_wittCoord k)

theorem constantCoeff_frobFam {n : ℕ} (hn : n ≠ 0) (m : ℕ) :
    MvPowerSeries.constantCoeff (frobFam R n m) = 0 :=
  constantCoeff_toFam R (constantCoeff_frobPoly hn m)

theorem constantCoeff_projFam (p k : ℕ) : MvPowerSeries.constantCoeff (projFam R p k) = 0 :=
  constantCoeff_toFam R (constantCoeff_projPoly p k)

theorem hasSubst_wittCoordFam : MvPowerSeries.HasSubst (wittCoordFam R) := by
  refine ⟨fun k => by rw [constantCoeff_wittCoordFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_le_nat (Finsupp.weight awt e)).subset fun k hk => ?_
  have hw := weight_eq_of_coeff_toFam_ne_zero R (isWeightedHomogeneous_wittCoord k) hk
  show k ≤ Finsupp.weight awt e
  omega

theorem hasSubst_frobFam (n : ℕ) : MvPowerSeries.HasSubst (frobFam R n) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : frobFam R 0 = 0 := by
      funext m
      rw [frobFam_apply, frobPoly_zero_left, toFam, map_zero, MvPolynomial.coe_zero]
      rfl
    rw [h0]
    exact MvPowerSeries.HasSubst.zero
  refine ⟨fun m => by rw [constantCoeff_frobFam R hn.ne']; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_le_nat (Finsupp.weight awt e)).subset fun m hm => ?_
  have hw := weight_eq_of_coeff_toFam_ne_zero R (isWeightedHomogeneous_frobPoly n m) hm
  show m ≤ Finsupp.weight awt e
  rw [hw]
  calc m ≤ m + 1 := Nat.le_succ m
    _ = 1 * (m + 1) := (one_mul _).symm
    _ ≤ n * (m + 1) := Nat.mul_le_mul_right _ hn

theorem hasSubst_projFam {p : ℕ} (hp : 2 ≤ p) : MvPowerSeries.HasSubst (projFam R p) := by
  refine ⟨fun k => by rw [constantCoeff_projFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_lt_nat (Finsupp.weight awt e)).subset fun k hk => ?_
  have hw := weight_eq_of_coeff_toFam_ne_zero R (isWeightedHomogeneous_projPoly (by omega) k) hk
  show k < Finsupp.weight awt e
  rw [hw]
  exact Nat.lt_pow_self (by omega)

end Families

end BigWittLaw

end MvFormalGroup

end


