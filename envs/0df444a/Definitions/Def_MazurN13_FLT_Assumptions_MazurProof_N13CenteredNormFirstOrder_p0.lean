-- Prove2me | Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CenteredNormFirstOrder_p0
-- name    : MazurN13_FLT_Assumptions_MazurProof_N13CenteredNormFirstOrder_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-08T02:03:22.325324+00:00
-- url     : https://prove2.me/theorems/c5893bef-15ba-450b-9c2d-286fd0573668
-- title:
--   FLT.Assumptions.MazurProof.N13CenteredNormFirstOrder source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Assumptions.MazurProof.N13CenteredNormFirstOrder

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Assumptions.MazurProof.N13CenteredNormFirstOrder
Original leading source comments and nonproject imports are retained below. -/
import Definitions.Def_MazurN13_FLT_Assumptions_MazurProof_N13CenteredHermiteFirstOrder_p0

set_option autoImplicit false




/-!
Source pin: 887d29cd9eb9b60a6e5ec438ff919a74ccda41e5.
FLT-C13-KERNEL r1, K2. Source candidate; Lean and axiom checks NOT RUN.

An exact comparison-numerator norm identity turns the Hermite calculation
into the required centered cross-coefficient congruences. Cancellation is
by monic polynomials over R/I², which can have zero divisors. The scalar in
the norm factorization is retained and its residue is proved to be one.
-/

namespace MazurProof.N13CenteredNormFirstOrder

noncomputable section
open Polynomial N13CenteredHermiteFirstOrder
local instance instFactPrimeOfNatNat_fLT : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem map_zero_of_coeff_mem {R : Type*} [CommRing R]
    (J : Ideal R) (p : R[X]) (h : ∀ n, p.coeff n ∈ J) :
    p.map (Ideal.Quotient.mk J) = 0 := by
  ext n
  simpa using Ideal.Quotient.eq_zero_iff_mem.mpr (h n)

private theorem map_eq_of_coeff_sub_mem {R : Type*} [CommRing R]
    (J : Ideal R) (p q : R[X]) (h : ∀ n, (p - q).coeff n ∈ J) :
    p.map (Ideal.Quotient.mk J) = q.map (Ideal.Quotient.mk J) := by
  apply sub_eq_zero.mp
  simpa only [Polynomial.map_sub] using map_zero_of_coeff_mem J (p - q) h

/-- Squaring a coefficientwise first-order deviation kills it modulo I². -/
theorem mapped_u_square (P : DiskPair) :
    (P.u ^ 2).map (Ideal.Quotient.mk (I P * I P)) =
      (N13AbelChartBase.baseSmoothMumford.u *
        N13MumfordCenteredDoublingJet.centeredSquareU P).map
          (Ideal.Quotient.mk (I P * I P)) := by
  let U := N13AbelChartBase.baseSmoothMumford.u
  let δ := P.u - U
  have hx₀ : P.x₀ ∈ I P := Ideal.subset_span (Set.mem_range_self (0 : Fin 2))
  have hx₁ : P.x₁ + 1 ∈ I P := Ideal.subset_span (Set.mem_range_self (1 : Fin 2))
  have hc₁ : -(P.x₀ + (P.x₁ + 1)) ∈ I P := (I P).neg_mem ((I P).add_mem hx₀ hx₁)
  have hc₀ : P.x₀ * P.x₁ ∈ I P := (I P).mul_mem_right _ hx₀
  have hδ : δ ∈ Ideal.map (C : R₂ →+* R₂[X]) (I P) := by
    rw [show δ = C (-(P.x₀ + (P.x₁ + 1))) * X + C (P.x₀ * P.x₁) from
      N13MumfordFormalTransitionJet.u_sub_base P]
    exact (Ideal.map C (I P)).add_mem
      ((Ideal.map C (I P)).mul_mem_right X (Ideal.mem_map_of_mem C hc₁))
      (Ideal.mem_map_of_mem C hc₀)
  have hδ₂ : δ ^ 2 ∈ Ideal.map (C : R₂ →+* R₂[X]) (I P * I P) := by
    rw [Ideal.map_mul, pow_two]
    exact Ideal.mul_mem_mul hδ hδ
  have hk : RingHom.ker (Ideal.Quotient.mk (I P * I P)) = I P * I P := by
    ext a
    exact Ideal.Quotient.eq_zero_iff_mem
  have hz : (δ ^ 2).map (Ideal.Quotient.mk (I P * I P)) = 0 := by
    have hmem : δ ^ 2 ∈ RingHom.ker (Polynomial.mapRingHom (Ideal.Quotient.mk (I P * I P))) := by
      rw [Polynomial.ker_mapRingHom, hk]
      exact hδ₂
    exact RingHom.mem_ker.mp hmem
  have hid := congrArg (Polynomial.map (Ideal.Quotient.mk (I P * I P)))
    (N13MumfordCenteredDoublingJet.u_sq_sub_base_mul_centeredSquareU P)
  rw [Polynomial.map_sub] at hid
  apply sub_eq_zero.mp
  rw [hid]
  exact hz

/-- All centered cross coefficients, including the required 1 and 3,
follow from a normalized Hermite numerator and its exact norm. -/
theorem cross_coefficients_of_norm
    (P Q : DiskPair) (A b : R₂[X]) (k : R₂) (hA : A.Monic)
    (hcenter : ∀ n, (A - N13MumfordCenteredDoublingJet.centeredSquareU P).coeff n ∈ I P * I P)
    (hb : ∀ n, b.coeff n ∈ I P * I P)
    (hnorm :
      (N13AbelChartBase.baseSmoothMumford.u * A) ^ 2 -
        (N13AbelChartBase.baseSmoothMumford.u * A) * b *
          N13GeneralizedMumfordIntegral.hPoly -
        b ^ 2 * N13GeneralizedMumfordIntegral.rhsPoly =
      C k * P.u ^ 2 * N13AbelChartBase.baseSmoothMumford.u * Q.u) :
    ∀ n, (P.u ^ 2 - N13AbelChartBase.baseSmoothMumford.u * Q.u).coeff n ∈ I P * I P := by
  let J := I P * I P
  let q : R₂ →+* (R₂ ⧸ J) := Ideal.Quotient.mk J
  let U := N13AbelChartBase.baseSmoothMumford.u.map q
  let V := P.u.map q
  let W := Q.u.map q
  let Abar := A.map q
  have hUm : U.Monic := N13AbelChartBase.baseSmoothMumford.u_monic.map q
  have hVm : V.Monic := P.u_monic.map q
  have hWm : W.Monic := Q.u_monic.map q
  have hAm : Abar.Monic := hA.map q
  have hbzero : b.map q = 0 := map_zero_of_coeff_mem J b hb
  have hAc : Abar = (N13MumfordCenteredDoublingJet.centeredSquareU P).map q :=
    map_eq_of_coeff_sub_mem J _ _ hcenter
  have hV : V ^ 2 = U * Abar := by
    rw [hAc]
    simpa only [Polynomial.map_pow, Polynomial.map_mul] using mapped_u_square P
  have he : U ^ 2 * Abar ^ 2 = C (q k) * (V ^ 2 * U * W) := by
    have h := congrArg (Polynomial.mapRingHom q) hnorm
    simp only [Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_mul, Polynomial.map_C, hbzero,
      mul_zero, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] at h
    change (U * Abar) ^ 2 = C (q k) * V ^ 2 * U * W at h
    convert h using 1 <;> ring
  have hk : q k = 1 := by
    have hl := congrArg Polynomial.leadingCoeff he
    rw [((hUm.pow 2).mul (hAm.pow 2)).leadingCoeff,
      (((hVm.pow 2).mul hUm).mul hWm).leadingCoeff_C_mul] at hl
    exact hl.symm
  rw [hk, C_1, one_mul, hV] at he
  have hAW : Abar = W := by
    apply ((hUm.pow 2).mul hAm).isRegular.left
    change (U ^ 2 * Abar) * Abar = (U ^ 2 * Abar) * W
    calc
      _ = U ^ 2 * Abar ^ 2 := by ring
      _ = (U * Abar) * U * W := he
      _ = _ := by ring
  have hzero : (P.u ^ 2 - N13AbelChartBase.baseSmoothMumford.u * Q.u).map q = 0 := by
    have hz : V ^ 2 - U * W = 0 := by rw [hV, hAW, sub_self]
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul] using hz
  intro n
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hc := congrArg (fun p : (R₂ ⧸ J)[X] => p.coeff n) hzero
  simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using hc

end
end MazurProof.N13CenteredNormFirstOrder


