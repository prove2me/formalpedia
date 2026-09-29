-- Prove2me | Definitions.Def_MvFormalGroup_BigWittLaw
-- name    : MvFormalGroup_BigWittLaw
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/83c3617a-5dfe-55c6-bda4-e2a5afbc8115
-- title:
--   Addition law of the big Witt formal group
-- statement:
--   Fix a commutative ring $R$. This module records the addition family of the big Witt formal group $\widehat\Lambda$, whose points over a commutative ring are power series $1+a_0t+a_1t^2+\cdots$ under multiplication, written in the coordinates $a_n =$ (coefficient of $t^{n+1}$). Two blocks of variables indexed by $\mathrm{Fin}\,2\times\mathbb{N}$ are used, $a_m = X_{(0,m)}$ and $b_m = X_{(1,m)}$. For $n\in\mathbb{N}$, `addPoly n` is the integral polynomial
--   $$\Sigma_n = X_{(0,n)} + X_{(1,n)} + \sum_{i<n} X_{(0,i)}X_{(1,n-1-i)} \in \mathbb{Z}[X_{(0,m)},X_{(1,m)}],$$
--   and `addFam R n` is its image in $R[[X_{(0,m)},X_{(1,m)}]]$, obtained by mapping coefficients along $\mathbb{Z}\to R$ and coercing a polynomial to a multivariate power series; `addFam_eq` gives the same explicit shape with `MvPowerSeries.X`.
--
--   The accompanying lemmas are: `aeval_addPoly` and `subst_addFam`, evaluating $\Sigma_n$ at an arbitrary family of elements of a commutative ring, respectively substituting an arbitrary substitutable family $u$ of power series, with value $u(0,n)+u(1,n)+\sum_{i<n}u(0,i)\,u(1,n-1-i)$; `subst_coe_addFam`, compatibility of substitution of (coerced, base-changed) polynomials into `addFam R n` with evaluation of the same polynomials in `addPoly n`; `coeff_succ_mul` and `coeff_succ_mul_eq_aeval`, the generating-function identity that for one-variable power series $F,G$ over a commutative ring with constant coefficient $1$, the coefficient of $t^{n+1}$ in $FG$ equals $\Sigma_n$ evaluated at the coefficients of $t^{m+1}$ in $F$ and in $G$; `constantCoeff_addPoly` and `constantCoeff_addFam`, vanishing of the constant term; `isWeightedHomogeneous_addPoly` and `weight_eq_of_coeff_addFam_ne_zero`, weighted homogeneity of degree $n+1$ for the weight assigning $m+1$ to each variable with second index $m$; and `hasSubst_addFam`, that the family $(\Sigma_n)_{n\ge0}$ satisfies Mathlib's substitutability condition, the finiteness part following from the weight computation. No associativity, commutativity or inverse statement is asserted here.
--
--   **Relation to Mathlib.** The substitution apparatus for multivariate power series (`MvPowerSeries.subst`, `MvPowerSeries.HasSubst`) and weighted homogeneity (`IsWeightedHomogeneous`, `Finsupp.weight`) are Mathlib's; Mathlib has no formal groups in infinitely many variables, so the addition family itself is recorded here, in the same format used for the $p$-typical Witt formal group.
--
--   **Where it is used.** The family $(\Sigma_n)_n$ is the carrier for statements about homomorphisms $\widehat\Lambda\to\Phi$ into a finite-dimensional formal group law — Cartier's first theorem identifying such homomorphisms with curves on $\Phi$, and the Artin–Hasse exponential as a homomorphism from the $p$-typical Witt formal group — which underlie the Cartier-module description of formal groups used in the study of $p$-divisible groups attached to the Galois representations in the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvFormalGroup_BigWittLaw.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

namespace BigWittLaw

open MvPolynomial

def addPoly (n : ℕ) : MvPolynomial (Fin 2 × ℕ) ℤ :=
  X (0, n) + X (1, n) + ∑ i ∈ Finset.range n, X (0, i) * X (1, n - 1 - i)

theorem aeval_addPoly {A : Type*} [CommRing A] (g : Fin 2 × ℕ → A) (n : ℕ) :
    aeval g (addPoly n) = g (0, n) + g (1, n) + ∑ i ∈ Finset.range n, g (0, i) * g (1, n - 1 - i) := by
  simp [addPoly, map_add, map_sum, map_mul]

theorem coeff_succ_mul {A : Type*} [CommRing A] {F G : PowerSeries A}
    (hF : PowerSeries.constantCoeff F = 1) (hG : PowerSeries.constantCoeff G = 1) (n : ℕ) :
    PowerSeries.coeff (n + 1) (F * G) =
      PowerSeries.coeff (n + 1) F + PowerSeries.coeff (n + 1) G +
        ∑ i ∈ Finset.range n, PowerSeries.coeff (i + 1) F * PowerSeries.coeff (n - 1 - i + 1) G := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.sub_self, tsub_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, hF, hG,
    mul_one, one_mul]
  have hsum : ∑ i ∈ Finset.range n,
      PowerSeries.coeff (i + 1) F * PowerSeries.coeff (n + 1 - (i + 1)) G =
      ∑ i ∈ Finset.range n, PowerSeries.coeff (i + 1) F * PowerSeries.coeff (n - 1 - i + 1) G := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < n := Finset.mem_range.mp hi
    have h2 : n + 1 - (i + 1) = n - 1 - i + 1 := by omega
    rw [h2]
  rw [hsum]
  ring

theorem coeff_succ_mul_eq_aeval {A : Type*} [CommRing A] {F G : PowerSeries A}
    (hF : PowerSeries.constantCoeff F = 1) (hG : PowerSeries.constantCoeff G = 1) (n : ℕ) :
    PowerSeries.coeff (n + 1) (F * G) =
      aeval (fun im : Fin 2 × ℕ =>
        (![fun m => PowerSeries.coeff (m + 1) F, fun m => PowerSeries.coeff (m + 1) G] :
          Fin 2 → ℕ → A) im.1 im.2) (addPoly n) := by
  rw [coeff_succ_mul hF hG, aeval_addPoly]
  simp

theorem constantCoeff_addPoly (n : ℕ) : constantCoeff (addPoly n) = 0 := by
  simp [addPoly, constantCoeff_X]

theorem isWeightedHomogeneous_addPoly (n : ℕ) :
    IsWeightedHomogeneous (fun im : Fin 2 × ℕ => im.2 + 1) (addPoly n) (n + 1) := by
  refine IsWeightedHomogeneous.add (IsWeightedHomogeneous.add ?_ ?_) ?_
  · exact isWeightedHomogeneous_X ℤ _ _
  · exact isWeightedHomogeneous_X ℤ _ _
  · refine IsWeightedHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i < n := Finset.mem_range.mp hi
    have h := (isWeightedHomogeneous_X ℤ (fun im : Fin 2 × ℕ => im.2 + 1) ((0 : Fin 2), i)).mul
      (isWeightedHomogeneous_X ℤ (fun im : Fin 2 × ℕ => im.2 + 1) ((1 : Fin 2), n - 1 - i))
    have hw : (i + 1) + (n - 1 - i + 1) = n + 1 := by omega
    rwa [hw] at h

variable (R : Type u) [CommRing R]

def addFam (n : ℕ) : MvPowerSeries (Fin 2 × ℕ) R :=
  ↑(MvPolynomial.map (Int.castRingHom R) (addPoly n))

theorem addFam_eq (n : ℕ) :
    addFam R n = MvPowerSeries.X (0, n) + MvPowerSeries.X (1, n) +
      ∑ i ∈ Finset.range n, MvPowerSeries.X (0, i) * MvPowerSeries.X (1, n - 1 - i) := by
  have hc : ∀ P : MvPolynomial (Fin 2 × ℕ) R,
      (P : MvPowerSeries (Fin 2 × ℕ) R) = MvPolynomial.coeToMvPowerSeries.ringHom P := fun _ => rfl
  rw [addFam, hc]
  simp [addPoly, map_add, map_sum, map_mul]

theorem constantCoeff_addFam (n : ℕ) : MvPowerSeries.constantCoeff (addFam R n) = 0 := by
  rw [addFam, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe,
    coeff_map, ← constantCoeff_eq, constantCoeff_addPoly, map_zero]

theorem weight_eq_of_coeff_addFam_ne_zero {n : ℕ} {e : Fin 2 × ℕ →₀ ℕ}
    (h : MvPowerSeries.coeff e (addFam R n) ≠ 0) :
    Finsupp.weight (fun im : Fin 2 × ℕ => im.2 + 1) e = n + 1 := by
  rw [addFam, MvPolynomial.coeff_coe, coeff_map] at h
  have h' : coeff e (addPoly n) ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  exact isWeightedHomogeneous_addPoly n h'

theorem hasSubst_addFam : MvPowerSeries.HasSubst (addFam R) := by
  refine ⟨fun n => by rw [constantCoeff_addFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_lt_nat (Finsupp.weight (fun im : Fin 2 × ℕ => im.2 + 1) e)).subset ?_
  intro n hn
  have hw := weight_eq_of_coeff_addFam_ne_zero R hn
  show n < Finsupp.weight (fun im : Fin 2 × ℕ => im.2 + 1) e
  omega

variable {R}

theorem subst_coe_addFam {τ : Type*} (g : Fin 2 × ℕ → MvPolynomial τ ℤ) (n : ℕ) :
    MvPowerSeries.subst (fun im => ((MvPolynomial.map (Int.castRingHom R) (g im) : MvPolynomial τ R) :
      MvPowerSeries τ R)) (addFam R n) =
      ((MvPolynomial.map (Int.castRingHom R) (aeval g (addPoly n)) : MvPolynomial τ R) :
        MvPowerSeries τ R) := by
  rw [addFam, MvPowerSeries.subst_coe]
  set G : Fin 2 × ℕ → MvPowerSeries τ R := fun im =>
    ((MvPolynomial.map (Int.castRingHom R) (g im) : MvPolynomial τ R) : MvPowerSeries τ R)
  let ψ₁ : MvPolynomial (Fin 2 × ℕ) ℤ →+* MvPowerSeries τ R :=
    (aeval G).toRingHom.comp (MvPolynomial.map (Int.castRingHom R))
  let ψ₂ : MvPolynomial (Fin 2 × ℕ) ℤ →+* MvPowerSeries τ R :=
    (MvPolynomial.coeToMvPowerSeries.ringHom (σ := τ) (R := R)).comp
      ((MvPolynomial.map (Int.castRingHom R)).comp (aeval g).toRingHom)
  have hψ : ψ₁ = ψ₂ := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun im => ?_)
    · exact RingHom.congr_fun (RingHom.ext_int (ψ₁.comp (C : ℤ →+* MvPolynomial (Fin 2 × ℕ) ℤ))
        (ψ₂.comp (C : ℤ →+* MvPolynomial (Fin 2 × ℕ) ℤ))) r
    · simp [ψ₁, ψ₂, G]
  exact RingHom.congr_fun hψ (addPoly n)

theorem subst_addFam {τ : Type*} {S : Type*} [CommRing S] [Algebra R S]
    {u : Fin 2 × ℕ → MvPowerSeries τ S} (hu : MvPowerSeries.HasSubst u) (n : ℕ) :
    MvPowerSeries.subst u (addFam R n) =
      u (0, n) + u (1, n) + ∑ i ∈ Finset.range n, u (0, i) * u (1, n - 1 - i) := by
  rw [addFam_eq, ← MvPowerSeries.coe_substAlgHom hu]
  simp only [map_add, map_sum, map_mul]
  simp only [MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X hu]

end BigWittLaw

end MvFormalGroup

end


