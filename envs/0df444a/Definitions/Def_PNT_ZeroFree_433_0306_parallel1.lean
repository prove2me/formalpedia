-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0306_parallel1
-- name    : PNT_ZeroFree_433_0306_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:14:41.552397+00:00
-- url     : https://prove2.me/theorems/e619f46e-94e0-4de7-863e-2a8d77c6d378
-- title:
--   Zero-free region foundations: Detector.Gauss, Detector.PrimePower, Detector.GaussValuation, Detector.CongruenceScalar, Detector.LiftedFourier, Detector.PhysicalFourier [0306_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Detector.Gauss
--   - OAI.NumberTheory.DirichletL.Detector.PrimePower
--   - OAI.NumberTheory.DirichletL.Detector.GaussValuation
--   - OAI.NumberTheory.DirichletL.Detector.CongruenceScalar
--   - OAI.NumberTheory.DirichletL.Detector.LiftedFourier
--   - OAI.NumberTheory.DirichletL.Detector.PhysicalFourier
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/Gauss.lean#L12-L110
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/PrimePower.lean#L13-L143
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/GaussValuation.lean#L10-L60
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/CongruenceScalar.lean#L11-L74
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/LiftedFourier.lean#L11-L108
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/PhysicalFourier.lean#L12-L112

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.NumberTheory.GaussSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0017
import Definitions.Def_PNT_ZeroFree_433_0145
import Definitions.Def_PNT_ZeroFree_433_0152
import Definitions.Def_PNT_ZeroFree_433_0217_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel2
import Definitions.Def_PNT_ZeroFree_433_0250_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/Gauss.lean#L12-L110
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/PrimePower.lean#L13-L143
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/GaussValuation.lean#L10-L60
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/CongruenceScalar.lean#L11-L74
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/LiftedFourier.lean#L11-L108
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Detector/PhysicalFourier.lean#L12-L112
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Detector.Gauss
section
namespace OAI

namespace SevenEighths.ProbeGauss
open scoped BigOperators Classical
noncomputable section

def frequencyGauss {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) : ℂ :=
  ∑ v : F, ξ v * ψ (h * v)

theorem frequencyGauss_eq_shift {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) :
    frequencyGauss ξ ψ h = gaussSum ξ (ψ.mulShift h) := rfl

theorem frequencyGauss_nonzero {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) {h : F} (hh : h ≠ 0) :
    frequencyGauss ξ ψ h = ξ⁻¹ h * gaussSum ξ ψ := by
  exact gaussSum_mulShift_eq ξ ψ (Units.mk0 h hh)

theorem frequencyGauss_zero_nonprincipal {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (hξ : ξ ≠ 1) :
    frequencyGauss ξ ψ 0 = 0 := by
  simpa [frequencyGauss] using MulChar.sum_eq_zero_of_ne_one hξ

theorem frequencyGauss_nonprincipal {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (hξ : ξ ≠ 1) (h : F) :
    frequencyGauss ξ ψ h = ξ⁻¹ h * gaussSum ξ ψ := by
  by_cases hh : h = 0
  · subst h
    rw [frequencyGauss_zero_nonprincipal ξ ψ hξ, MulChar.map_zero, zero_mul]
  · exact frequencyGauss_nonzero ξ ψ hh

theorem frequencyGauss_principal {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (h : F) :
    frequencyGauss 1 ψ h = if h = 0 then (Nat.card Fˣ : ℂ) else -1 := by
  classical
  by_cases hh : h = 0
  · subst h
    simpa [frequencyGauss, Nat.card_eq_fintype_card] using
      (MulChar.sum_one_eq_card_units (R := F) (R' := ℂ))
  · rw [if_neg hh, frequencyGauss_nonzero _ ψ hh, inv_one,
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hh), one_mul]
    exact gaussSum_one_left hψ

theorem gauss_inverse_pair {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * (Fintype.card F : ℂ) := by
  rw [← mul_gaussSum_inv_eq_gaussSum χ⁻¹, mul_left_comm,
    gaussSum_mul_gaussSum_eq_card hχ hψ, MulChar.inv_apply', inv_neg_one]

def normalizedGauss {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℂ :=
  gaussSum χ ψ / (Real.sqrt (Fintype.card F) : ℂ)

theorem normalizedGauss_inverse_pair {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    normalizedGauss χ ψ * normalizedGauss χ⁻¹ ψ = χ (-1) := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (Real.sqrt (Fintype.card F) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F) : (0 : ℝ) ≤ _)
  unfold normalizedGauss
  rw [div_mul_div_comm, ← pow_two, hs, gauss_inverse_pair χ ψ hχ hψ]
  exact mul_div_cancel_right₀ _ hq

theorem finite_gauss_convolution {F : Type*} [Field F] [Fintype F]
    (χ ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) :
    (∑ d : F, χ d * frequencyGauss ξ ψ (h - d)) =
      χ⁻¹ (-1) * gaussSum χ ψ * frequencyGauss (ξ * χ⁻¹) ψ h := by
  classical
  have hfreq (v : F) :
      ξ v * (∑ d : F, χ d * ψ (-(v * d))) =
        χ⁻¹ (-1) * gaussSum χ ψ * (ξ v * χ⁻¹ v) := by
    by_cases hv : v = 0
    · subst v
      simp [MulChar.map_zero]
    · have hn : -v ≠ 0 := neg_ne_zero.mpr hv
      have he := gaussSum_mulShift_eq χ ψ (Units.mk0 (-v) hn)
      simp only [gaussSum, AddChar.mulShift_apply, Units.val_mk0] at he
      have hinv : χ⁻¹ (-v) = χ⁻¹ (-1) * χ⁻¹ v := by rw [← map_mul]; congr 1; ring
      rw [hinv] at he
      have he' : (∑ d : F, χ d * ψ (-(v * d))) =
          (χ⁻¹ (-1) * χ⁻¹ v) * gaussSum χ ψ := by
        simpa only [neg_mul, gaussSum] using he
      rw [he']
      ring
  unfold frequencyGauss
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ v : F, ∑ d : F, χ d * (ξ v * ψ ((h - d) * v))) =
        ∑ v : F, ψ (h * v) * (ξ v * ∑ d : F, χ d * ψ (-(v * d))) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [show (h - d) * v = h * v + -(v * d) by ring, ψ.map_add_eq_mul]
      ring
    _ = ∑ v : F, ψ (h * v) *
        (χ⁻¹ (-1) * gaussSum χ ψ * (ξ v * χ⁻¹ v)) := by simp_rw [hfreq]
    _ = ∑ v : F, χ⁻¹ (-1) * gaussSum χ ψ * ((ξ * χ⁻¹) v * ψ (h * v)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [MulChar.mul_apply]
      ring

end
end SevenEighths.ProbeGauss

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Detector.PrimePower
section
namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein

local notation "O" => ActualEisensteinCubic.O

def primeGauss (p : O) (hp : p ≠ 0) (χ : MulChar (O ⧸ Ideal.span {p}) ℂ)
    (h : O) : ℂ :=
  ∑' x : O ⧸ Ideal.span {p}, χ x * quotientTrace p hp (Ideal.Quotient.mk _ h * x)

def primePowerGauss (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) : ℂ :=
  conductorFourier p (p ^ n) hp (pow_ne_zero _ hp) χ h

theorem primePowerGauss_support (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O)
    (hG : primePowerGauss p hp χ n h ≠ 0) : p ^ n ∣ h :=
  conductorFourier_support p (p ^ n) hp (pow_ne_zero _ hp) χ h hG

theorem primePowerGauss_zero_off_support (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O)
    (hdiv : ¬p ^ n ∣ h) : primePowerGauss p hp χ n h = 0 := by
  by_contra hG
  exact hdiv (primePowerGauss_support p hp χ n h hG)

theorem primePowerGauss_lift (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) :
    primePowerGauss p hp χ n (p ^ n * h) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n * primeGauss p hp χ h := by
  unfold primePowerGauss primeGauss
  rw [conductorFourier_lift]
  have hn : Ideal.absNorm (Ideal.span {p ^ n}) = Ideal.absNorm (Ideal.span {p}) ^ n := by
    rw [← Ideal.span_singleton_pow, map_pow]
  rw [hn, Nat.cast_pow]

theorem primePowerGauss_nonprincipal_extra_divisibility (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) (n : ℕ) (h : O)
    (hph : p ∣ h) : primePowerGauss p hp χ n (p ^ n * h) = 0 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primePowerGauss_lift]
  have hz : Ideal.Quotient.mk (Ideal.span {p}) h = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hph)
  have hzero : primeGauss p hp χ h = 0 := by
    rw [primeGauss, tsum_fintype]
    simp only [hz, zero_mul, AddChar.map_zero_eq_one, mul_one]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  rw [hzero, mul_zero]

theorem primePowerGauss_principal (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hψ : quotientTrace p hp ≠ 1) (n : ℕ) (h : O) :
    primePowerGauss p hp 1 n (p ^ n * h) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
        (if p ∣ h then (Nat.card (O ⧸ Ideal.span {p})ˣ : ℂ) else -1) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  rw [primePowerGauss_lift]
  congr 1
  have hdiv : Ideal.Quotient.mk (Ideal.span {p}) h = 0 ↔ p ∣ h := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  simpa only [primeGauss, tsum_fintype, ProbeGauss.frequencyGauss, hdiv] using
    ProbeGauss.frequencyGauss_principal (quotientTrace p hp) hψ
      (Ideal.Quotient.mk (Ideal.span {p}) h)

theorem higher_outer_lift_annihilated (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) {n : ℕ} (hn : 0 < n) (m : O) :
    ξ (Ideal.Quotient.mk (Ideal.span {p}) m) * primePowerGauss p hp χ n (-m) = 0 := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  by_cases hG : primePowerGauss p hp χ n (-m) = 0
  · rw [hG, mul_zero]
  · have hdneg := primePowerGauss_support p hp χ n (-m) hG
    have hdpow : p ∣ p ^ n := dvd_pow_self p (Nat.ne_of_gt hn)
    have hdm : p ∣ m := dvd_neg.mp (hdpow.trans hdneg)
    have hz : Ideal.Quotient.mk (Ideal.span {p}) m = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdm)
    rw [hz, MulChar.map_zero, zero_mul]

def scalarKOne (p : O) (hp : p ≠ 0)
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {p}, χ d * primePowerGauss p hp ξ n
    (h - p ^ n * GaussianShiftedPartition.representative p d)

theorem scalarKOne_eq (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ ξ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h : O) :
    scalarKOne p hp χ ξ n h =
      χ⁻¹ (-1) * primeGauss p hp χ 1 * primePowerGauss p hp (ξ * χ⁻¹) n h := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  by_cases hdiv : p ^ n ∣ h
  · obtain ⟨k, rfl⟩ := hdiv
    have hmk (d : O ⧸ Ideal.span {p}) :
        Ideal.Quotient.mk (Ideal.span {p})
          (k - GaussianShiftedPartition.representative p d) =
          Ideal.Quotient.mk (Ideal.span {p}) k - d := by
      rw [map_sub, GaussianShiftedPartition.representative_spec]
    have hscalar : scalarKOne p hp χ ξ n (p ^ n * k) =
        (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n *
          ∑ d : O ⧸ Ideal.span {p}, χ d * ProbeGauss.frequencyGauss ξ
            (quotientTrace p hp) (Ideal.Quotient.mk _ k - d) := by
      unfold scalarKOne
      rw [tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [← mul_sub, primePowerGauss_lift]
      have he : primeGauss p hp ξ (k - GaussianShiftedPartition.representative p d) =
          ProbeGauss.frequencyGauss ξ (quotientTrace p hp) (Ideal.Quotient.mk _ k - d) := by
        rw [primeGauss, tsum_fintype]
        simp only [hmk, ProbeGauss.frequencyGauss]
      rw [he]
      ring
    rw [hscalar, ProbeGauss.finite_gauss_convolution, primePowerGauss_lift]
    have hG : primeGauss p hp χ 1 = gaussSum χ (quotientTrace p hp) := by
      simp [primeGauss, tsum_fintype, gaussSum]
    have hF : primeGauss p hp (ξ * χ⁻¹) k =
        ProbeGauss.frequencyGauss (ξ * χ⁻¹) (quotientTrace p hp) (Ideal.Quotient.mk _ k) := by
      simp only [primeGauss, tsum_fintype, ProbeGauss.frequencyGauss]
    rw [hG, hF]
    ring
  · rw [primePowerGauss_zero_off_support p hp (ξ * χ⁻¹) n h hdiv, mul_zero]
    unfold scalarKOne
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro d _
    have hndiv : ¬p ^ n ∣ h - p ^ n * GaussianShiftedPartition.representative p d := by
      intro hd
      apply hdiv
      have ha := dvd_add hd (dvd_mul_right (p ^ n)
        (GaussianShiftedPartition.representative p d))
      simpa only [sub_add_cancel] using ha
    rw [primePowerGauss_zero_off_support p hp ξ n _ hndiv, mul_zero]

end SevenEighths.ProbePrimePower
end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Detector.GaussValuation
section
namespace OAI

noncomputable section
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem primePowerGauss_at_pow_nonprincipal (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (hχ : χ ≠ 1) (n j : ℕ) :
    primePowerGauss p hp.ne_zero χ n (p ^ j) =
      if j = n then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n * primeGauss p hp.ne_zero χ 1
      else 0 := by
  by_cases he : j = n
  · subst j
    rw [if_pos rfl]
    simpa only [mul_one] using primePowerGauss_lift p hp.ne_zero χ n 1
  rw [if_neg he]
  rcases lt_or_gt_of_ne he with hjn | hnj
  · apply primePowerGauss_zero_off_support
    rw [pow_dvd_pow_iff hp.ne_zero hp.not_isUnit]
    omega
  · have hle : n ≤ j := Nat.le_of_lt hnj
    have heq : p ^ j = p ^ n * p ^ (j - n) := by rw [← pow_add, Nat.add_sub_of_le hle]
    rw [heq]
    apply primePowerGauss_nonprincipal_extra_divisibility p hp.ne_zero χ hχ
    exact dvd_pow_self p (by omega)

theorem primePowerGauss_at_pow_principal (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (hψ : quotientTrace p hp.ne_zero ≠ 1) (n j : ℕ) :
    primePowerGauss p hp.ne_zero 1 n (p ^ j) =
      (if n + 1 ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (n + 1) else 0) -
      (if n ≤ j then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ n else 0) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := ConcreteTraceCRT.finite_quotient_span hp.ne_zero
  have hcard : (Nat.card (O ⧸ Ideal.span {p})ˣ : ℂ) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1 := by
    rw [Nat.card_units, Nat.cast_sub (Nat.card_pos : 0 < Nat.card (O ⧸ Ideal.span {p})),
      Nat.cast_one]
    rfl
  rcases lt_trichotomy j n with hjn | he | hnj
  · rw [if_neg (by omega), if_neg (by omega), sub_self]
    apply primePowerGauss_zero_off_support
    rw [pow_dvd_pow_iff hp.ne_zero hp.not_isUnit]
    omega
  · subst j
    have hnot : ¬p ∣ (1 : O) := by simpa only [isUnit_iff_dvd_one] using hp.not_isUnit
    simpa only [mul_one, if_neg hnot, if_neg (Nat.not_succ_le_self n),
      if_pos (le_refl n), zero_sub, mul_neg_one] using
      primePowerGauss_principal p hp.ne_zero hψ n 1
  · have hle : n ≤ j := by omega
    have heq : p ^ j = p ^ n * p ^ (j - n) := by rw [← pow_add, Nat.add_sub_of_le hle]
    have hd : p ∣ p ^ (j - n) := dvd_pow_self p (by omega)
    rw [heq, primePowerGauss_principal, if_pos hd, if_pos (by omega : n + 1 ≤ j),
      if_pos hle, hcard, pow_succ]
    ring
    exact hψ

end SevenEighths.ProbePrimePower
end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Detector.CongruenceScalar
section
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition
local notation "O" => ActualEisensteinCubic.O

def exactQuotient (a b : O) (h : b ∣ a) : O := Classical.choose h

lemma exactQuotient_spec (a b : O) (h : b ∣ a) : a = b * exactQuotient a b h :=
  Classical.choose_spec h

lemma exactQuotient_eq (a b c : O) (h : b ∣ a) (hb : b ≠ 0) (he : a = b*c) :
    exactQuotient a b h = c := by
  apply mul_left_cancel₀ hb
  exact (exactQuotient_spec a b h).symm.trans he

def positiveScalar (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k j : ℕ) : ℂ :=
  if k = 0 then primePowerGauss p hp (χ^(n+1)) n (p^j)
  else ∑' d : O ⧸ Ideal.span {p^k},
    if h : p^k ∣ p^j-p^(n+1)*representative (p^k) d then
      (χ^k) (Ideal.Quotient.mk (Ideal.span {p}) (representative (p^k) d)) *
        primePowerGauss p hp (χ^(n+1)) n
          (exactQuotient (p^j-p^(n+1)*representative (p^k) d) (p^k) h)
    else 0

@[simp] theorem positiveScalar_kzero (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 0 j = primePowerGauss p hp (χ^(n+1)) n (p^j) := by
  simp only [positiveScalar, ite_true]

theorem positiveScalar_kone_jzero (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) :
    positiveScalar p hp.ne_zero χ n 1 0 = 0 := by
  simp only [positiveScalar, Nat.one_ne_zero, ite_false]
  rw [pow_one]
  simp only [pow_zero, pow_one]
  refine (tsum_congr (g := fun _ => (0:ℂ)) ?_).trans tsum_zero
  intro d
  rw [dif_neg]
  intro hd
  have hd2 : p ∣ p^(n+1)*representative p d :=
    (dvd_pow_self p (by omega : n+1 ≠ 0)).mul_right _
  have hunit : p ∣ (1:O) := by
    have := dvd_add hd hd2
    simpa only [sub_add_cancel] using this
  exact hp.not_isUnit (isUnit_iff_dvd_one.mpr hunit)

theorem positiveScalar_kone_convolution (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 1 (j+1) = scalarKOne p hp χ (χ^(n+1)) n (p^j) := by
  simp only [positiveScalar, Nat.one_ne_zero, ite_false, scalarKOne]
  rw [pow_one]
  simp only [pow_one]
  apply tsum_congr
  intro d
  have he : p^(j+1)-p^(n+1)*representative p d = p*(p^j-p^n*representative p d) := by
    simp only [pow_succ]
    ring
  have hd : p ∣ p^(j+1)-p^(n+1)*representative p d := ⟨_,he⟩
  rw [dif_pos hd, exactQuotient_eq _ _ _ hd hp he, representative_spec]

theorem positiveScalar_kone (p : O) (hp : p ≠ 0)
    [(Ideal.span {p} : Ideal O).IsMaximal]
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n j : ℕ) :
    positiveScalar p hp χ n 1 (j+1) =
      χ⁻¹ (-1) * primeGauss p hp χ 1 * primePowerGauss p hp (χ^n) n (p^j) := by
  rw [positiveScalar_kone_convolution, scalarKOne_eq]
  have he : χ^(n+1)*χ⁻¹ = χ^n := by rw [pow_succ, mul_assoc, mul_inv_cancel, mul_one]
  rw [he]

end SevenEighths.ProbePrimePower
end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Detector.LiftedFourier
section
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePrimePower
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition
local notation "O" => ActualEisensteinCubic.O

theorem primePowerGauss_lift_add (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k : ℕ) (h : O) :
    primePowerGauss p hp.ne_zero χ (n+k) (p^k*h) =
      (Ideal.absNorm (Ideal.span {p}):ℂ)^k * primePowerGauss p hp.ne_zero χ n h := by
  by_cases hd : p^n ∣ h
  · obtain ⟨a, rfl⟩ := hd
    have he : p^k*(p^n*a) = p^(n+k)*a := by rw [pow_add]; ring
    rw [he, primePowerGauss_lift, primePowerGauss_lift, pow_add]
    ring
  · have hbig : ¬p^(n+k) ∣ p^k*h := by
      rw [pow_add, mul_comm (p^n) (p^k), mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)]
      exact hd
    rw [primePowerGauss_zero_off_support _ _ _ _ _ hbig,
      primePowerGauss_zero_off_support _ _ _ _ _ hd, mul_zero]

theorem primePowerGauss_add_period (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (h a : O) :
    primePowerGauss p hp χ n (h+p^(n+1)*a) = primePowerGauss p hp χ n h := by
  unfold primePowerGauss conductorFourier
  apply tsum_congr
  intro x
  have hz : Ideal.Quotient.mk (Ideal.span {p*p^n}) (p^(n+1)*a) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_singleton.mpr
    refine ⟨a, ?_⟩
    rw [pow_succ']
  simp only [map_add, hz, add_zero]

theorem gauss_exactQuotient_lift (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k : ℕ) (h : O) :
    (if hd : p^k ∣ h then primePowerGauss p hp.ne_zero χ n (exactQuotient h (p^k) hd) else 0) =
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^k)⁻¹ * primePowerGauss p hp.ne_zero χ (n+k) h := by
  have hq : (Ideal.absNorm (Ideal.span {p}):ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero)
  by_cases hd : p^k ∣ h
  · rw [dif_pos hd]
    conv_rhs => rw [exactQuotient_spec h (p^k) hd]
    rw [primePowerGauss_lift_add p hp, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hq), one_mul]
  · rw [dif_neg hd]
    have hnd : ¬p^(n+k) ∣ h := by
      intro he
      exact hd ((show p^k ∣ p^(n+k) from ⟨p^n, by rw [pow_add]; ring⟩).trans he)
    rw [primePowerGauss_zero_off_support _ _ _ _ _ hnd, mul_zero]

theorem positiveScalar_full_lift (p : O) (hp : Prime p)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n k j : ℕ) (hk : k ≠ 0) :
    positiveScalar p hp.ne_zero χ n k j =
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^k)⁻¹ *
        ∑' d : O ⧸ Ideal.span {p^k},
          (χ^k) (Ideal.Quotient.mk _ (representative (p^k) d)) *
            primePowerGauss p hp.ne_zero (χ^(n+1)) (n+k)
              (p^j-p^(n+1)*representative (p^k) d) := by
  rw [positiveScalar, if_neg hk, ← tsum_mul_left]
  apply tsum_congr
  intro d
  have he := gauss_exactQuotient_lift p hp (χ^(n+1)) n k
    (p^j-p^(n+1)*representative (p^k) d)
  by_cases hd : p^k ∣ p^j-p^(n+1)*representative (p^k) d
  · rw [dif_pos hd] at he ⊢
    rw [he]
    ring
  · rw [dif_neg hd] at he ⊢
    linear_combination (χ^k) (Ideal.Quotient.mk _ (representative (p^k) d)) * he

lemma quotientTrace_split_frequency (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (H d v : O) :
    quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ ((H-b*d)*v)) =
      quotientTrace (a*b) (mul_ne_zero ha hb) (Ideal.Quotient.mk _ (H*v)) *
        quotientTrace a ha (Ideal.Quotient.mk _ ((-v)*d)) := by
  have hs := quotientTrace_conductor_scale a b ((-v)*d) ha hb 1
  simp only [mul_one, map_one] at hs
  rw [show (H-b*d)*v = H*v+b*((-v)*d) by ring, map_add, AddChar.map_add_eq_mul, hs]

def quotientFourier (p c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (H : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {c}, χ (Ideal.Quotient.mk _ (representative c d)) *
    quotientTrace c hc (Ideal.Quotient.mk _ (H*representative c d))

lemma quotientFourier_congr (p a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (H : O) (he : a=b) :
    quotientFourier p a ha χ H = quotientFourier p b hb χ H := by
  subst b
  rfl

lemma primePowerGauss_eq_quotientFourier (p : O) (hp : p ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {p}) ℂ) (n : ℕ) (H : O) :
    primePowerGauss p hp χ n H =
      quotientFourier p (p*p^n) (mul_ne_zero hp (pow_ne_zero _ hp)) χ H := by
  unfold primePowerGauss conductorFourier quotientFourier
  apply tsum_congr
  intro d
  have hr : conductorReduction p (p^n) d =
      Ideal.Quotient.mk (Ideal.span {p}) (representative (p*p^n) d) := by
    conv_lhs => rw [← representative_spec (p*p^n) d]
    rfl
  have hm : Ideal.Quotient.mk (Ideal.span {p*p^n}) (H*representative (p*p^n) d) =
      Ideal.Quotient.mk _ H*d := by rw [map_mul, representative_spec]
  rw [hr, hm]

end SevenEighths.ProbePrimePower
end

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Detector.PhysicalFourier
section
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein GaussianShiftedPartition ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

def rawFourier (a : O) (ha : a≠0) (F : (O ⧸ Ideal.span {a}) → ℂ) (H : O) : ℂ :=
  ∑' m : O ⧸ Ideal.span {a}, F m * quotientTrace a ha (Ideal.Quotient.mk _ H * m)

theorem rawFourier_exactQuotient (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (H : O) :
    conductorFourier a s ha hs F H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) *
        (if h : s∣H then rawFourier a ha F (exactQuotient H s h) else 0) := by
  by_cases h : s∣H
  · rw [dif_pos h]
    conv_lhs => rw [exactQuotient_spec H s h]
    exact conductorFourier_lift a s ha hs F _
  · rw [dif_neg h, mul_zero]
    by_contra hn
    exact h (conductorFourier_support a s ha hs F H hn)

def congruenceCoefficient (a s : O) (ha : a≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ) (H : O) : ℂ :=
  ∑' d : O ⧸ Ideal.span {s}, χ d *
    (if h : s ∣ H-a*representative s d then
      rawFourier a ha F (exactQuotient (H-a*representative s d) s h) else 0)

lemma trace_split_product (a s : O) (ha : a≠0) (hs : s≠0) (H m d : O) :
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ (H*m)) *
      quotientTrace s hs (Ideal.Quotient.mk _ ((-m)*d)) =
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ ((H-a*d)*m)) := by
  have he := quotientTrace_split_frequency s a hs ha H d m
  simp only [quotientTrace_mk] at he ⊢
  simpa only [mul_comm s a] using he.symm

def fullFourier (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ) (H : O) : ℂ :=
  ∑' m : O ⧸ Ideal.span {a*s}, F (conductorReduction a s m) *
    rawFourier s hs χ (-representative (a*s) m) *
    quotientTrace (a*s) (mul_ne_zero ha hs) (Ideal.Quotient.mk _ H*m)

theorem fullFourier_eq_congruence (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ) (H : O) :
    fullFourier a s ha hs F χ H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) * congruenceCoefficient a s ha F χ H := by
  let : Finite (O ⧸ Ideal.span {a*s}) := finite_quotient_span (mul_ne_zero ha hs)
  let : Finite (O ⧸ Ideal.span {s}) := finite_quotient_span hs
  let : Fintype (O ⧸ Ideal.span {a*s}) := Fintype.ofFinite _
  let : Fintype (O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  unfold fullFourier rawFourier
  simp_rw [tsum_fintype, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold congruenceCoefficient
  rw [tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    _ = χ d * conductorFourier a s ha hs F (H-a*representative s d) := by
      rw [conductorFourier, tsum_fintype, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have ht := trace_split_product a s ha hs H (representative (a*s) m) (representative s d)
      simp only [map_mul, representative_spec] at ht
      rw [← ht]
      ring
    _ = _ := by rw [rawFourier_exactQuotient]; ring

theorem rawFourier_norm_le (a : O) (ha : a≠0) (F : (O ⧸ Ideal.span {a}) → ℂ)
    (hF : ∀ m, ‖F m‖≤1) (H : O) :
    ‖rawFourier a ha F H‖ ≤ (Ideal.absNorm (Ideal.span {a}):ℝ) := by
  let := finite_quotient_span ha
  let : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  rw [rawFourier, tsum_fintype]
  calc
    _ ≤ ∑ m : O ⧸ Ideal.span {a}, ‖F m * quotientTrace a ha (Ideal.Quotient.mk _ H*m)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m : O ⧸ Ideal.span {a}, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [norm_mul, AddChar.norm_apply, mul_one]
      exact hF m
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem congruenceCoefficient_norm_le (a s : O) (ha : a≠0) (hs : s≠0)
    (F : (O ⧸ Ideal.span {a}) → ℂ) (χ : (O ⧸ Ideal.span {s}) → ℂ)
    (hF : ∀ m, ‖F m‖≤1) (hχ : ∀ d, ‖χ d‖≤1) (H : O) :
    ‖congruenceCoefficient a s ha F χ H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ) * (Ideal.absNorm (Ideal.span {a}):ℝ) := by
  let := finite_quotient_span hs
  let : Fintype (O ⧸ Ideal.span {s}) := Fintype.ofFinite _
  unfold congruenceCoefficient
  rw [tsum_fintype]
  calc
    _ ≤ ∑ d : O ⧸ Ideal.span {s}, ‖χ d *
        (if h : s ∣ H-a*representative s d then
          rawFourier a ha F (exactQuotient (H-a*representative s d) s h) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _d : O ⧸ Ideal.span {s}, (Ideal.absNorm (Ideal.span {a}):ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      · rw [norm_mul]
        exact (mul_le_mul (hχ d) (rawFourier_norm_le a ha F hF _)
          (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      · simp only [mul_zero, norm_zero]
        positivity
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

end SevenEighths.ProbePhysical
end

end OAI

end


