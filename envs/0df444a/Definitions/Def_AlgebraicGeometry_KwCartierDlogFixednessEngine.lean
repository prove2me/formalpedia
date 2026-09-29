-- Prove2me | Definitions.Def_AlgebraicGeometry_KwCartierDlogFixednessEngine
-- name    : AlgebraicGeometry_KwCartierDlogFixednessEngine
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/49daf352-2bc8-5928-940f-9302af00e703
-- title:
--   Cartier operator fixes logarithmic differentials, via a generic model
-- statement:
--   Fix a prime $\ell$. The generic model consists of two one-variable polynomials over $\mathbb{Z}[X_0,\dots,X_{\ell-1}]$: `kw_cfx_G` $=\sum_{i<\ell} X_i T^i$, the generic polynomial of degree $<\ell$, and `kw_cfx_Gpow` $=\sum_{i<\ell} X_i^{\ell} T^{\ell i}$, its Frobenius twist. The supporting lemmas record that the difference $G^{\ell}-G^{[\ell]}$ reduces to $0$ modulo $\ell$ (hence each of its coefficients is divisible by $\ell$ in the coefficient ring), that $G'=\sum_i X_i\,i\,T^{i-1}$, that $\deg(G^{\ell-1}G')\le \ell(\ell-1)$, and the central congruence: for $m+1<\ell$ the coefficient of $T^{\ell m+(\ell-1)}$ in $G^{\ell-1}G'$ equals $(m+1)X_{m+1}^{\ell}+\ell e$ for some $e$, while for $m+1\ge \ell$ that coefficient vanishes.
--
--   The transport section works with a field $F$ of characteristic $\ell$, an algebra over a field $K$, and the subobject `kw_pke_pthPowers F ℓ` of $\ell$-th powers of $F$. For $t\in F$, `kw_cfx_tau` is $t^{\ell}$ viewed there; `kw_cfx_vext` extends a family $v:\mathrm{Fin}\,\ell\to$ $\ell$-th powers to all naturals by zero; `kw_cfx_phiP v`, `kw_cfx_phi v` and `kw_cfx_Phi t v` are the evaluation ring homomorphisms sending $X_i\mapsto v_i$ (into the $\ell$-th powers, then into $F$) and $T\mapsto t$; and `kw_cfx_fstarOf t v` $=\sum_{i<\ell} i\,v_i\,t^{i-1}$. The accompanying identities say that $\Phi$ applied to $G$ recovers $f$ when $v$ is the $\ell$-th-power-coordinate family of $f$ in powers of $t$, that $\Phi$ applied to $G'$ gives `kw_cfx_fstarOf`, that coordinates of $\Phi(q)$ are obtained by grouping coefficients of $q$ by residues modulo $\ell$, that $n^{\ell}=n$ for natural $n$, that $D_{F/K}f = (\mathrm{kw\_cfx\_fstarOf})\cdot D_{F/K}t$, and that $(\mathrm{kw\_cfx\_fstarOf})^{\ell}$ equals $\sum_{m<\ell-1}(m+1)v_{m+1}^{\ell}\tau^{m}$, which is exactly the $(\ell-1)$-st coordinate of $\Phi(G^{\ell-1}G')$.
--
--   The conclusion `kw_cfx_C_dlog_fixed`: for $t\in F$ with $D_{F/K}t\ne 0$ spanning $\Omega_{F/K}$, with separability of $F$ over the field attached to $t$ by `kw_pke_expansionField` and with $\deg\,\mathrm{minpoly}_{F^{\ell}}(t)=\ell$, and for $f\ne 0$, the operator `kw_cart_C` fixes $\mathrm{dlog}\,f = f^{-1}\,D_{F/K}f$.
--
--   **Relation to Mathlib.** Mathlib has no Cartier operator on Kähler differentials; `kw_cart_C` and the generic model used here are the project's own, built on Mathlib's `MvPolynomial`, `Polynomial.eval₂`, `Polynomial.derivative` and `KaehlerDifferential`.
--
--   **Where it is used.** Together with the semilinearity of `kw_cart_C`, this identity places the image of $\mathrm{dlog}$ inside the space of differentials fixed by the Cartier operator, the step used in the Hasse–Witt style bound on $\ell$-torsion of the degree-zero divisor class group of a curve in characteristic $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_KwCartierDlogFixednessEngine.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_KwCartierOperatorTCoordEngine
import Definitions.Def_ModularCurve_KwNo6HspecCartierDlogCampaignFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial AlgebraicCurve.KwPke AlgebraicCurve.KwCart

noncomputable section

namespace AlgebraicCurve.KwCfx

theorem kw_cfx_axiomAnchor : True :=
  have _h₁ : True = True := propext Iff.rfl
  have _h₂ : ℕ := Classical.choice ⟨0⟩
  have _h₃ : Quot.mk (fun (_ _ : ℕ) => True) 0 = Quot.mk (fun (_ _ : ℕ) => True) 1 :=
    Quot.sound trivial
  trivial

section GenericModel

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

def kw_cfx_G : Polynomial (MvPolynomial (Fin ℓ) ℤ) :=
  ∑ i : Fin ℓ, C (MvPolynomial.X i) * X ^ (i : ℕ)

def kw_cfx_Gpow : Polynomial (MvPolynomial (Fin ℓ) ℤ) :=
  ∑ i : Fin ℓ, C (MvPolynomial.X i ^ ℓ) * X ^ (ℓ * (i : ℕ))

theorem kw_cfx_z1_map_eq :
    (kw_cfx_G ℓ ^ ℓ - kw_cfx_Gpow ℓ).map
      (MvPolynomial.map (Int.castRingHom (ZMod ℓ))) = 0 := by
  have _ := kw_cfx_axiomAnchor
  haveI : CharP (MvPolynomial (Fin ℓ) (ZMod ℓ)) ℓ :=
    charP_of_injective_ringHom (MvPolynomial.C_injective (Fin ℓ) (ZMod ℓ)) ℓ
  haveI : CharP (Polynomial (MvPolynomial (Fin ℓ) (ZMod ℓ))) ℓ :=
    charP_of_injective_ringHom (Polynomial.C_injective
      (R := MvPolynomial (Fin ℓ) (ZMod ℓ))) ℓ
  rw [Polynomial.map_sub, Polynomial.map_pow, sub_eq_zero]
  have hG : (kw_cfx_G ℓ).map (MvPolynomial.map (Int.castRingHom (ZMod ℓ)))
      = ∑ i : Fin ℓ, C (MvPolynomial.X i) * X ^ (i : ℕ) := by
    rw [kw_cfx_G, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      MvPolynomial.map_X]
  have hGpow : (kw_cfx_Gpow ℓ).map (MvPolynomial.map (Int.castRingHom (ZMod ℓ)))
      = ∑ i : Fin ℓ, C (MvPolynomial.X i ^ ℓ) * X ^ (ℓ * (i : ℕ)) := by
    rw [kw_cfx_Gpow, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
      map_pow, MvPolynomial.map_X]
  rw [hG, hGpow, sum_pow_char]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← Polynomial.C_pow, ← pow_mul, Nat.mul_comm (i : ℕ) ℓ]

theorem kw_cfx_z1 (k : ℕ) :
    MvPolynomial.C ((ℓ : ℕ) : ℤ) ∣ (kw_cfx_G ℓ ^ ℓ - kw_cfx_Gpow ℓ).coeff k := by
  have _ := kw_cfx_axiomAnchor
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have h1 : MvPolynomial.map (Int.castRingHom (ZMod ℓ))
      ((kw_cfx_G ℓ ^ ℓ - kw_cfx_Gpow ℓ).coeff k) = 0 := by
    have h := congrArg (fun p => p.coeff k) (kw_cfx_z1_map_eq ℓ)
    simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using h
  rw [MvPolynomial.C_dvd_iff_dvd_coeff]
  intro mono
  have h2 : ((((kw_cfx_G ℓ ^ ℓ - kw_cfx_Gpow ℓ).coeff k).coeff mono : ℤ)
      : ZMod ℓ) = 0 := by
    have h := congrArg (fun p => MvPolynomial.coeff mono p) h1
    simpa only [MvPolynomial.coeff_map, MvPolynomial.coeff_zero,
      Int.coe_castRingHom] using h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mp h2

omit hℓ in

theorem kw_cfx_z_derivG :
    derivative (kw_cfx_G ℓ)
      = ∑ i : Fin ℓ, C (MvPolynomial.X i * ((i : ℕ) : MvPolynomial (Fin ℓ) ℤ))
          * X ^ ((i : ℕ) - 1) := by
  have _ := kw_cfx_axiomAnchor
  rw [kw_cfx_G, derivative_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [derivative_C_mul_X_pow]

theorem kw_cfx_z2 (m : ℕ) (hm : m + 1 < ℓ) :
    ∃ e : MvPolynomial (Fin ℓ) ℤ,
      (kw_cfx_G ℓ ^ (ℓ - 1) * derivative (kw_cfx_G ℓ)).coeff (ℓ * m + (ℓ - 1))
        = ((m + 1 : ℕ) : MvPolynomial (Fin ℓ) ℤ)
            * MvPolynomial.X (⟨m + 1, hm⟩ : Fin ℓ) ^ ℓ
          + ((ℓ : ℕ) : MvPolynomial (Fin ℓ) ℤ) * e := by
  have _ := kw_cfx_axiomAnchor
  have hpos := hℓ.out.pos
  have h2 := hℓ.out.two_le
  have hsucc : ℓ - 1 + 1 = ℓ := by omega

  have hpow : kw_cfx_G ℓ ^ ℓ = kw_cfx_G ℓ ^ ((ℓ - 1) + 1) := by
    rw [hsucc]
  have ha : derivative (kw_cfx_G ℓ ^ ℓ)
      = C ((ℓ : ℕ) : MvPolynomial (Fin ℓ) ℤ)
          * (kw_cfx_G ℓ ^ (ℓ - 1) * derivative (kw_cfx_G ℓ)) := by
    rw [hpow, derivative_pow_succ, mul_assoc, ← Nat.cast_add_one, hsucc]

  have hb : derivative (kw_cfx_G ℓ ^ ℓ)
      = derivative (kw_cfx_Gpow ℓ)
        + derivative (kw_cfx_G ℓ ^ ℓ - kw_cfx_Gpow ℓ) := by
    rw [derivative_sub]
    ring

  have hc2 : (derivative (kw_cfx_Gpow ℓ)).coeff (ℓ * m + (ℓ - 1))
      = MvPolynomial.X (⟨m + 1, hm⟩ : Fin ℓ) ^ ℓ
          * ((ℓ * (m + 1) : ℕ) : MvPolynomial (Fin ℓ) ℤ) := by
    rw [kw_cfx_Gpow, derivative_sum]
    have hterm : ∀ i : Fin ℓ,
        derivative (C (MvPolynomial.X i ^ ℓ) * X ^ (ℓ * (i : ℕ))
          : Polynomial (MvPolynomial (Fin ℓ) ℤ))
        = C (MvPolynomial.X i ^ ℓ * ((ℓ * (i : ℕ) : ℕ) : MvPolynomial (Fin ℓ) ℤ))
            * X ^ (ℓ * (i : ℕ) - 1) := fun i => derivative_C_mul_X_pow _ _
    rw [Finset.sum_congr rfl fun i _ => hterm i, finsetSum_coeff]
    rw [Finset.sum_eq_single (⟨m + 1, hm⟩ : Fin ℓ)]
    · have hval : (((⟨m + 1, hm⟩ : Fin ℓ) : ℕ)) = m + 1 := rfl
      have hidx : ℓ * m + (ℓ - 1) = ℓ * (((⟨m + 1, hm⟩ : Fin ℓ) : ℕ)) - 1 := by
        rw [hval, Nat.mul_succ]
        omega
      rw [coeff_C_mul, coeff_X_pow, if_pos hidx, mul_one, hval]
    · intro j _ hji
      have hne : ℓ * m + (ℓ - 1) ≠ ℓ * (j : ℕ) - 1 := by
        intro heq
        rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hjpos
        · rw [hj0, Nat.mul_zero, Nat.zero_sub] at heq
          omega
        · have hj1 : ℓ * (j : ℕ) - 1 + 1 = ℓ * (j : ℕ) :=
            Nat.succ_pred_eq_of_pos (Nat.mul_pos hpos hjpos)
          have hlm : ℓ * m + (ℓ - 1) + 1 = ℓ * (m + 1) := by
            rw [Nat.mul_succ]
            omega
          have hmul : ℓ * (m + 1) = ℓ * (j : ℕ) := by omega
          have hjm : m + 1 = (j : ℕ) := Nat.eq_of_mul_eq_mul_left hpos hmul
          exact hji (Fin.ext hjm.symm)
      rw [coeff_C_mul, coeff_X_pow, if_neg hne, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

  have hn1 : ℓ * m + (ℓ - 1) + 1 = ℓ * (m + 1) := by
    rw [Nat.mul_succ]
    omega
  obtain ⟨e₀, he₀⟩ := kw_cfx_z1 ℓ (ℓ * (m + 1))
  have hc3 : (derivative (kw_cfx_G ℓ ^ ℓ - kw_cfx_Gpow ℓ)).coeff (ℓ * m + (ℓ - 1))
      = MvPolynomial.C ((ℓ : ℕ) : ℤ) * e₀
          * ((ℓ * (m + 1) : ℕ) : MvPolynomial (Fin ℓ) ℤ) := by
    have hcast : ((ℓ * m + (ℓ - 1) : ℕ) : MvPolynomial (Fin ℓ) ℤ) + 1
        = ((ℓ * (m + 1) : ℕ) : MvPolynomial (Fin ℓ) ℤ) := by
      exact_mod_cast congrArg (Nat.cast (R := MvPolynomial (Fin ℓ) ℤ)) hn1
    rw [coeff_derivative, show ℓ * m + (ℓ - 1) + 1 = ℓ * (m + 1) from hn1, he₀, hcast]

  have hCl : (MvPolynomial.C ((ℓ : ℕ) : ℤ) : MvPolynomial (Fin ℓ) ℤ)
      = ((ℓ : ℕ) : MvPolynomial (Fin ℓ) ℤ) := map_natCast MvPolynomial.C ℓ
  have hkey : ((ℓ : ℕ) : MvPolynomial (Fin ℓ) ℤ)
        * (kw_cfx_G ℓ ^ (ℓ - 1) * derivative (kw_cfx_G ℓ)).coeff (ℓ * m + (ℓ - 1))
      = MvPolynomial.X (⟨m + 1, hm⟩ : Fin ℓ) ^ ℓ
          * ((ℓ * (m + 1) : ℕ) : MvPolynomial (Fin ℓ) ℤ)
        + MvPolynomial.C ((ℓ : ℕ) : ℤ) * e₀
            * ((ℓ * (m + 1) : ℕ) : MvPolynomial (Fin ℓ) ℤ) := by
    calc ((ℓ : ℕ) : MvPolynomial (Fin ℓ) ℤ)
          * (kw_cfx_G ℓ ^ (ℓ - 1) * derivative (kw_cfx_G ℓ)).coeff (ℓ * m + (ℓ - 1))
        = (C ((ℓ : ℕ) : MvPolynomial (Fin ℓ) ℤ)
            * (kw_cfx_G ℓ ^ (ℓ - 1) * derivative (kw_cfx_G ℓ))).coeff
              (ℓ * m + (ℓ - 1)) := by
          rw [coeff_C_mul]
      _ = (derivative (kw_cfx_G ℓ ^ ℓ)).coeff (ℓ * m + (ℓ - 1)) := by rw [← ha]
      _ = (derivative (kw_cfx_Gpow ℓ)).coeff (ℓ * m + (ℓ - 1))
            + (derivative (kw_cfx_G ℓ ^ ℓ - kw_cfx_Gpow ℓ)).coeff
                (ℓ * m + (ℓ - 1)) := by
          rw [hb, coeff_add]
      _ = _ := by rw [hc2, hc3]
  have hne : ((ℓ : ℕ) : MvPolynomial (Fin ℓ) ℤ) ≠ 0 := by
    rw [← hCl]
    exact MvPolynomial.C_ne_zero.mpr
      (Int.natCast_ne_zero.mpr hℓ.out.ne_zero)
  refine ⟨e₀ * ((m + 1 : ℕ) : MvPolynomial (Fin ℓ) ℤ), mul_left_cancel₀ hne ?_⟩
  rw [hkey, hCl]
  push_cast
  ring

theorem kw_cfx_z3_natDegree_le :
    (kw_cfx_G ℓ ^ (ℓ - 1) * derivative (kw_cfx_G ℓ)).natDegree ≤ ℓ * (ℓ - 1) := by
  have _ := kw_cfx_axiomAnchor
  have hG : (kw_cfx_G ℓ).natDegree ≤ ℓ - 1 := by
    rw [kw_cfx_G]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_
    have := i.isLt
    omega
  have hG' : (derivative (kw_cfx_G ℓ)).natDegree ≤ ℓ - 1 := by
    rw [kw_cfx_z_derivG]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine le_trans (Polynomial.natDegree_C_mul_X_pow_le _ _) ?_
    have := i.isLt
    omega
  have hpow : (kw_cfx_G ℓ ^ (ℓ - 1)).natDegree ≤ (ℓ - 1) * (ℓ - 1) :=
    le_trans Polynomial.natDegree_pow_le (Nat.mul_le_mul_left _ hG)
  have hmul := Polynomial.natDegree_mul_le
    (p := kw_cfx_G ℓ ^ (ℓ - 1)) (q := derivative (kw_cfx_G ℓ))
  have hsucc : ℓ - 1 + 1 = ℓ := by have := hℓ.out.pos; omega
  have harith : (ℓ - 1) * (ℓ - 1) + (ℓ - 1) = ℓ * (ℓ - 1) := by
    calc (ℓ - 1) * (ℓ - 1) + (ℓ - 1) = ((ℓ - 1) + 1) * (ℓ - 1) := by ring
      _ = ℓ * (ℓ - 1) := by rw [hsucc]
  omega

theorem kw_cfx_z3_coeff_zero (m : ℕ) (hm : ℓ ≤ m + 1) :
    (kw_cfx_G ℓ ^ (ℓ - 1) * derivative (kw_cfx_G ℓ)).coeff (ℓ * m + (ℓ - 1)) = 0 := by
  have _ := kw_cfx_axiomAnchor
  refine Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (kw_cfx_z3_natDegree_le ℓ) ?_)
  have h2 := hℓ.out.two_le
  have hmm : ℓ - 1 ≤ m := by omega
  have h3 : ℓ * (ℓ - 1) ≤ ℓ * m := Nat.mul_le_mul_left ℓ hmm
  omega

end GenericModel

section Transport

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP F ℓ]

def kw_cfx_tau (t : F) : kw_pke_pthPowers F ℓ :=
  ⟨t ^ ℓ, (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨t, rfl⟩⟩

@[simp]
theorem kw_cfx_tau_coe (t : F) : ((kw_cfx_tau (ℓ := ℓ) t : kw_pke_pthPowers F ℓ)
    : F) = t ^ ℓ := rfl

def kw_cfx_vext (v : Fin ℓ → kw_pke_pthPowers F ℓ) (n : ℕ) :
    kw_pke_pthPowers F ℓ :=
  if h : n < ℓ then v ⟨n, h⟩ else 0

theorem kw_cfx_vext_of_lt (v : Fin ℓ → kw_pke_pthPowers F ℓ) {n : ℕ} (h : n < ℓ) :
    kw_cfx_vext v n = v ⟨n, h⟩ := by
  have _ := kw_cfx_axiomAnchor
  rw [kw_cfx_vext, dif_pos h]

def kw_cfx_phiP (v : Fin ℓ → kw_pke_pthPowers F ℓ) :
    MvPolynomial (Fin ℓ) ℤ →+* kw_pke_pthPowers F ℓ :=
  (MvPolynomial.aeval v).toRingHom

theorem kw_cfx_phiP_X (v : Fin ℓ → kw_pke_pthPowers F ℓ) (j : Fin ℓ) :
    kw_cfx_phiP v (MvPolynomial.X j) = v j := by
  have _ := kw_cfx_axiomAnchor
  exact MvPolynomial.aeval_X v j

def kw_cfx_phi (v : Fin ℓ → kw_pke_pthPowers F ℓ) :
    MvPolynomial (Fin ℓ) ℤ →+* F :=
  ((kw_pke_pthPowers F ℓ).subtype).comp (kw_cfx_phiP v)

theorem kw_cfx_phi_apply (v : Fin ℓ → kw_pke_pthPowers F ℓ)
    (x : MvPolynomial (Fin ℓ) ℤ) :
    kw_cfx_phi v x = ((kw_cfx_phiP v x : kw_pke_pthPowers F ℓ) : F) := by
  have _ := kw_cfx_axiomAnchor
  rfl

def kw_cfx_Phi (t : F) (v : Fin ℓ → kw_pke_pthPowers F ℓ) :
    Polynomial (MvPolynomial (Fin ℓ) ℤ) →+* F :=
  Polynomial.eval₂RingHom (kw_cfx_phi v) t

theorem kw_cfx_Phi_apply (t : F) (v : Fin ℓ → kw_pke_pthPowers F ℓ)
    (q : Polynomial (MvPolynomial (Fin ℓ) ℤ)) :
    kw_cfx_Phi t v q = Polynomial.eval₂ (kw_cfx_phi v) t q := by
  have _ := kw_cfx_axiomAnchor
  rfl

theorem kw_cfx_t4_natCast_pow (n : ℕ) : ((n : F)) ^ ℓ = (n : F) := by
  have _ := kw_cfx_axiomAnchor
  have h := map_natCast (frobenius F ℓ) n
  rwa [frobenius_def] at h

theorem kw_cfx_t1_Phi_G (t : F)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    (f : F) :
    kw_cfx_Phi t (kw_cart_repr t hsep hdeg f) (kw_cfx_G ℓ) = f := by
  have _ := kw_cfx_axiomAnchor
  rw [kw_cfx_G, map_sum]
  have hterm : ∀ i : Fin ℓ,
      kw_cfx_Phi t (kw_cart_repr t hsep hdeg f) (C (MvPolynomial.X i) * X ^ (i : ℕ))
        = ((kw_cart_repr t hsep hdeg f i : F)) * t ^ (i : ℕ) := by
    intro i
    rw [map_mul, map_pow, kw_cfx_Phi_apply, kw_cfx_Phi_apply, eval₂_C, eval₂_X,
      kw_cfx_phi_apply, kw_cfx_phiP_X]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  exact (kw_cart_repr_spec t hsep hdeg f).symm

def kw_cfx_fstarOf (t : F) (v : Fin ℓ → kw_pke_pthPowers F ℓ) : F :=
  ∑ i : Fin ℓ, ((i : ℕ) : F) * ((v i : F)) * t ^ ((i : ℕ) - 1)

theorem kw_cfx_t2_Phi_dG (t : F) (v : Fin ℓ → kw_pke_pthPowers F ℓ) :
    kw_cfx_Phi t v (derivative (kw_cfx_G ℓ)) = kw_cfx_fstarOf t v := by
  have _ := kw_cfx_axiomAnchor
  rw [kw_cfx_z_derivG, map_sum, kw_cfx_fstarOf]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, kw_cfx_Phi_apply, kw_cfx_Phi_apply, eval₂_C, eval₂_X,
    map_mul, map_natCast, kw_cfx_phi_apply, kw_cfx_phiP_X]
  ring

theorem kw_cfx_t3_repr_Phi (t : F)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    (v : Fin ℓ → kw_pke_pthPowers F ℓ)
    (q : Polynomial (MvPolynomial (Fin ℓ) ℤ)) (N : ℕ) (hN : q.natDegree < ℓ * N) :
    kw_cart_repr t hsep hdeg (kw_cfx_Phi t v q)
      = fun r : Fin ℓ => ∑ m ∈ Finset.range N,
          kw_cfx_phiP v (q.coeff (ℓ * m + (r : ℕ))) * kw_cfx_tau (ℓ := ℓ) t ^ m := by
  have _ := kw_cfx_axiomAnchor
  have hpos := hℓ.out.pos
  refine kw_cart_repr_unique t hsep hdeg ?_
  have h0 : kw_cfx_Phi t v q
      = ∑ k ∈ Finset.range (ℓ * N), kw_cfx_phi v (q.coeff k) * t ^ k := by
    rw [kw_cfx_Phi_apply]
    exact eval₂_eq_sum_range' (kw_cfx_phi v) hN t
  calc kw_cfx_Phi t v q
      = ∑ k ∈ Finset.range (ℓ * N), kw_cfx_phi v (q.coeff k) * t ^ k := h0
    _ = ∑ p ∈ Finset.range N ×ˢ Finset.range ℓ,
          kw_cfx_phi v (q.coeff (ℓ * p.1 + p.2)) * t ^ (ℓ * p.1 + p.2) := by
        refine Finset.sum_nbij' (fun k => (k / ℓ, k % ℓ)) (fun p => ℓ * p.1 + p.2)
          ?_ ?_ ?_ ?_ ?_
        · intro k hk
          rw [Finset.mem_range] at hk
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
          refine ⟨?_, Nat.mod_lt _ hpos⟩
          rw [Nat.div_lt_iff_lt_mul hpos, Nat.mul_comm N ℓ]
          exact hk
        · intro p hp
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
          rw [Finset.mem_range]
          show ℓ * p.1 + p.2 < ℓ * N
          have h1 : p.1 + 1 ≤ N := hp.1
          have h2 : ℓ * (p.1 + 1) ≤ ℓ * N := Nat.mul_le_mul_left ℓ h1
          rw [Nat.mul_succ] at h2
          omega
        · intro k _
          exact Nat.div_add_mod k ℓ
        · intro p hp
          rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
          have hd : (ℓ * p.1 + p.2) / ℓ = p.1 := by
            rw [Nat.mul_add_div hpos, Nat.div_eq_of_lt hp.2, Nat.add_zero]
          have hm : (ℓ * p.1 + p.2) % ℓ = p.2 := by
            rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hp.2]
          exact Prod.ext hd hm
        · intro k _
          show kw_cfx_phi v (q.coeff k) * t ^ k
              = kw_cfx_phi v (q.coeff (ℓ * (k / ℓ) + k % ℓ))
                  * t ^ (ℓ * (k / ℓ) + k % ℓ)
          rw [Nat.div_add_mod k ℓ]
    _ = ∑ m ∈ Finset.range N, ∑ r ∈ Finset.range ℓ,
          kw_cfx_phi v (q.coeff (ℓ * m + r)) * t ^ (ℓ * m + r) :=
        Finset.sum_product _ _ _
    _ = ∑ r ∈ Finset.range ℓ, ∑ m ∈ Finset.range N,
          kw_cfx_phi v (q.coeff (ℓ * m + r)) * t ^ (ℓ * m + r) :=
        Finset.sum_comm
    _ = ∑ r ∈ Finset.range ℓ,
          (∑ m ∈ Finset.range N, kw_cfx_phi v (q.coeff (ℓ * m + r)) * (t ^ ℓ) ^ m)
            * t ^ r := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [pow_add, pow_mul, mul_assoc]
    _ = ∑ i : Fin ℓ,
          (((fun r : Fin ℓ => ∑ m ∈ Finset.range N,
              kw_cfx_phiP v (q.coeff (ℓ * m + (r : ℕ)))
                * kw_cfx_tau (ℓ := ℓ) t ^ m) i : kw_pke_pthPowers F ℓ) : F)
            * t ^ (i : ℕ) := by
        rw [← Fin.sum_univ_eq_sum_range (fun r =>
          (∑ m ∈ Finset.range N, kw_cfx_phi v (q.coeff (ℓ * m + r)) * (t ^ ℓ) ^ m)
            * t ^ r) ℓ]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        push_cast
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [kw_cfx_phi_apply, kw_cfx_tau_coe]

end Transport

section Assembly

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP F ℓ]

theorem kw_cfx_D_eq (t : F)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    (f : F) :
    KaehlerDifferential.D K F f
      = kw_cfx_fstarOf t (kw_cart_repr t hsep hdeg f)
          • KaehlerDifferential.D K F t := by
  have _ := kw_cfx_axiomAnchor
  conv_lhs => rw [kw_cart_repr_spec t hsep hdeg f]
  rw [map_sum, kw_cfx_fstarOf, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Derivation.leibniz]
  have hDv : KaehlerDifferential.D K F ((kw_cart_repr t hsep hdeg f i : F)) = 0 := by
    rw [← kw_cart_root_pow (kw_cart_repr t hsep hdeg f i)]
    exact kw_cart_d_pow_zero _
  rw [hDv, smul_zero, add_zero, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F,
    smul_smul, smul_smul]
  congr 1
  ring

theorem kw_cfx_fstar_pow_char (t : F) (v : Fin ℓ → kw_pke_pthPowers F ℓ) :
    kw_cfx_fstarOf t v ^ ℓ
      = ((∑ m ∈ Finset.range (ℓ - 1),
            ((m + 1 : ℕ) : kw_pke_pthPowers F ℓ) * kw_cfx_vext v (m + 1) ^ ℓ
              * kw_cfx_tau (ℓ := ℓ) t ^ m : kw_pke_pthPowers F ℓ) : F) := by
  have _ := kw_cfx_axiomAnchor
  have h2 := hℓ.out.two_le
  have hℓ1 : ℓ - 1 + 1 = ℓ := by omega

  have hR : ((∑ m ∈ Finset.range (ℓ - 1),
        ((m + 1 : ℕ) : kw_pke_pthPowers F ℓ) * kw_cfx_vext v (m + 1) ^ ℓ
          * kw_cfx_tau (ℓ := ℓ) t ^ m : kw_pke_pthPowers F ℓ) : F)
      = ∑ m ∈ Finset.range (ℓ - 1),
          ((m + 1 : ℕ) : F) * ((kw_cfx_vext v (m + 1) : F)) ^ ℓ * (t ^ ℓ) ^ m := by
    push_cast
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [kw_cfx_tau_coe]
  rw [hR, kw_cfx_fstarOf, sum_pow_char]

  have hterm : ∀ i : Fin ℓ,
      (((i : ℕ) : F) * ((v i : F)) * t ^ ((i : ℕ) - 1)) ^ ℓ
        = ((i : ℕ) : F) * ((kw_cfx_vext v (i : ℕ) : F)) ^ ℓ * (t ^ ℓ) ^ ((i : ℕ) - 1) := by
    intro i
    rw [mul_pow, mul_pow, kw_cfx_t4_natCast_pow, ← pow_mul,
      Nat.mul_comm ((i : ℕ) - 1) ℓ, pow_mul, kw_cfx_vext_of_lt v i.isLt, Fin.eta]
  rw [Finset.sum_congr rfl fun i _ => hterm i]

  rw [Fin.sum_univ_eq_sum_range (fun k =>
    ((k : ℕ) : F) * ((kw_cfx_vext v k : F)) ^ ℓ * (t ^ ℓ) ^ (k - 1)) ℓ]

  have hrange : Finset.range ℓ = Finset.range ((ℓ - 1) + 1) := by rw [hℓ1]
  rw [hrange, Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, add_zero, Nat.add_sub_cancel]

theorem kw_cfx_repr_top (t : F)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    (v : Fin ℓ → kw_pke_pthPowers F ℓ) :
    kw_cart_repr t hsep hdeg
        (kw_cfx_Phi t v (kw_cfx_G ℓ ^ (ℓ - 1) * derivative (kw_cfx_G ℓ)))
        ⟨ℓ - 1, by have := hℓ.out.pos; omega⟩
      = ∑ m ∈ Finset.range (ℓ - 1),
          ((m + 1 : ℕ) : kw_pke_pthPowers F ℓ) * kw_cfx_vext v (m + 1) ^ ℓ
            * kw_cfx_tau (ℓ := ℓ) t ^ m := by
  have _ := kw_cfx_axiomAnchor
  have hpos := hℓ.out.pos
  have h2 := hℓ.out.two_le
  have hℓ1 : ℓ - 1 + 1 = ℓ := by omega

  have hmulsq : ℓ * ℓ = ℓ * (ℓ - 1) + ℓ := by
    calc ℓ * ℓ = ℓ * ((ℓ - 1) + 1) := by rw [hℓ1]
      _ = ℓ * (ℓ - 1) + ℓ := by rw [Nat.mul_succ]
  have hdeg' : (kw_cfx_G ℓ ^ (ℓ - 1) * derivative (kw_cfx_G ℓ)).natDegree
      < ℓ * ℓ := by
    have h := kw_cfx_z3_natDegree_le ℓ
    omega
  have ht3 := kw_cfx_t3_repr_Phi t hsep hdeg v
    (kw_cfx_G ℓ ^ (ℓ - 1) * derivative (kw_cfx_G ℓ)) ℓ hdeg'
  rw [ht3]
  show ∑ m ∈ Finset.range ℓ,
      kw_cfx_phiP v ((kw_cfx_G ℓ ^ (ℓ - 1) * derivative (kw_cfx_G ℓ)).coeff
        (ℓ * m + (ℓ - 1))) * kw_cfx_tau (ℓ := ℓ) t ^ m = _

  have hrange : Finset.range ℓ = Finset.range ((ℓ - 1) + 1) := by rw [hℓ1]
  rw [hrange, Finset.sum_range_succ]
  have htop : (kw_cfx_G ℓ ^ (ℓ - 1) * derivative (kw_cfx_G ℓ)).coeff
      (ℓ * (ℓ - 1) + (ℓ - 1)) = 0 :=
    kw_cfx_z3_coeff_zero ℓ (ℓ - 1) (by omega)
  rw [htop, map_zero, zero_mul, add_zero]

  refine Finset.sum_congr rfl fun m hm => ?_
  have hmlt : m + 1 < ℓ := by
    rw [Finset.mem_range] at hm
    omega
  obtain ⟨e, he⟩ := kw_cfx_z2 ℓ m hmlt
  rw [he, map_add, map_mul, map_mul, map_natCast, map_natCast, map_pow, kw_cfx_phiP_X]

  have hl0 : ((ℓ : ℕ) : kw_pke_pthPowers F ℓ) = 0 := by
    have h1 : (((ℓ : ℕ) : kw_pke_pthPowers F ℓ) : F) = ((ℓ : ℕ) : F) := by
      norm_cast
    have hF : ((ℓ : ℕ) : F) = 0 := CharP.cast_eq_zero F ℓ
    exact ZeroMemClass.coe_eq_zero.mp (h1.trans hF)
  rw [hl0, zero_mul, add_zero, kw_cfx_vext_of_lt v hmlt]

theorem kw_cfx_C_dlog_fixed (t : F)
    (hdt : KaehlerDifferential.D K F t ≠ 0)
    (hspan : Submodule.span F {KaehlerDifferential.D K F t} = ⊤)
    (hsep : ∀ x : F, IsSeparable (kw_pke_expansionField (ℓ := ℓ) t).toSubfield x)
    (hdeg : (minpoly (kw_pke_pthPowers F ℓ) t).natDegree = ℓ)
    {f : F} (hf : f ≠ 0) :
    kw_cart_C (K := K) t hdt hspan hsep hdeg (kw_hwcd_dlog K f)
      = kw_hwcd_dlog K f := by
  have _ := kw_cfx_axiomAnchor
  have hpos := hℓ.out.pos
  have hℓ1 : ℓ - 1 + 1 = ℓ := by omega

  set v : Fin ℓ → kw_pke_pthPowers F ℓ := kw_cart_repr t hsep hdeg f with hv

  have hdlog : kw_hwcd_dlog K f
      = (f⁻¹ * kw_cfx_fstarOf t v) • KaehlerDifferential.D K F t := by
    rw [kw_hwcd_dlog, kw_cfx_D_eq t hsep hdeg f, smul_smul]

  have hsplit : f⁻¹ * kw_cfx_fstarOf t v
      = (f⁻¹) ^ ℓ * (f ^ (ℓ - 1) * kw_cfx_fstarOf t v) := by
    have h1 : (f⁻¹) ^ ℓ * f ^ (ℓ - 1) = f⁻¹ := by
      have hfpow : (f⁻¹) ^ ℓ = (f⁻¹) ^ ((ℓ - 1) + 1) := by rw [hℓ1]
      calc (f⁻¹) ^ ℓ * f ^ (ℓ - 1)
          = f⁻¹ * ((f⁻¹) ^ (ℓ - 1) * f ^ (ℓ - 1)) := by
            rw [hfpow, pow_succ]
            ring
        _ = f⁻¹ * ((f⁻¹ * f) ^ (ℓ - 1)) := by rw [mul_pow]
        _ = f⁻¹ := by rw [inv_mul_cancel₀ hf, one_pow, mul_one]
    calc f⁻¹ * kw_cfx_fstarOf t v
        = ((f⁻¹) ^ ℓ * f ^ (ℓ - 1)) * kw_cfx_fstarOf t v := by rw [h1]
      _ = (f⁻¹) ^ ℓ * (f ^ (ℓ - 1) * kw_cfx_fstarOf t v) := by ring

  have hω : kw_hwcd_dlog K f
      = (f⁻¹) ^ ℓ • ((f ^ (ℓ - 1) * kw_cfx_fstarOf t v)
          • KaehlerDifferential.D K F t) := by
    rw [hdlog, hsplit, mul_smul]
  conv_lhs => rw [hω]
  rw [kw_cart_C_semilinear]

  have hcoord : kw_cart_dtCoord t hdt hspan
      ((f ^ (ℓ - 1) * kw_cfx_fstarOf t v) • KaehlerDifferential.D K F t)
      = f ^ (ℓ - 1) * kw_cfx_fstarOf t v :=
    kw_cart_dtCoord_unique t hdt hspan rfl

  have hPhi : f ^ (ℓ - 1) * kw_cfx_fstarOf t v
      = kw_cfx_Phi t v (kw_cfx_G ℓ ^ (ℓ - 1) * derivative (kw_cfx_G ℓ)) := by
    rw [map_mul, map_pow, kw_cfx_t1_Phi_G t hsep hdeg f, kw_cfx_t2_Phi_dG]

  have hroot : kw_cart_root (kw_cart_repr t hsep hdeg
        (f ^ (ℓ - 1) * kw_cfx_fstarOf t v)
        ⟨ℓ - 1, by have := hℓ.out.pos; omega⟩)
      = kw_cfx_fstarOf t v := by
    refine kw_cart_root_unique ?_
    rw [hPhi, kw_cfx_repr_top t hsep hdeg v]
    exact kw_cfx_fstar_pow_char t v

  rw [kw_cart_C, hcoord, hroot, smul_smul]
  exact hdlog.symm

end Assembly

end AlgebraicCurve.KwCfx

end

section Audits

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_axiomAnchor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_axiomAnchor

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_z1_map_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_z1_map_eq

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_z1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_z1

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_z_derivG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_z_derivG

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_z2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_z2

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_z3_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_z3_natDegree_le

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_z3_coeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_z3_coeff_zero

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_tau_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_tau_coe

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_vext_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_vext_of_lt

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_phiP_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_phiP_X

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_phi_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_phi_apply

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_Phi_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_Phi_apply

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_t4_natCast_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_t4_natCast_pow

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_t1_Phi_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_t1_Phi_G

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_t2_Phi_dG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_t2_Phi_dG

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_t3_repr_Phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_t3_repr_Phi

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_D_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_D_eq

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_fstar_pow_char' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_fstar_pow_char

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_repr_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_repr_top

/-- info: 'AlgebraicCurve.KwCfx.kw_cfx_C_dlog_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicCurve.KwCfx.kw_cfx_C_dlog_fixed

end Audits


