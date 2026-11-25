-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocE
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_NDLocE
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T16:18:54.154886+00:00
-- url     : https://prove2.me/theorems/c96da877-d7e6-415e-af5e-80d897bd20bc
-- title:
--   NDLoc E
-- statement:
--   Definitions and structural lemmas for NDLoc E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocE.lean

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime]
theorem norm_eq_spectralValue (x : PadicAlgCl l) : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
theorem isIntegral_iff_norm_le (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have halg : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hmon := minpoly.monic halg
  rw [norm_eq_spectralValue, spectralValue_le_one_iff hmon]
  constructor
  · intro hx n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hx, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      exact ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hmon
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]
variable (LL : FinExt l)
theorem mem_OL (x : ↥LL.1) : x ∈ OL LL ↔ ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  unfold OL
  rw [mem_integralClosure_iff, ← isIntegral_iff_norm_le]
  exact (isIntegral_algHom_iff ((IntermediateField.val LL.1).restrictScalars ℤ_[l])
    Subtype.val_injective).symm
def nrm (a : ↥(OL LL)) : ℝ := ‖((a : ↥LL.1) : PadicAlgCl l)‖
theorem nrm_le (a : ↥(OL LL)) : nrm LL a ≤ 1 := by
  exact (mem_OL LL a.1).mp a.2
theorem nrm_mul (a b : ↥(OL LL)) : nrm LL (a * b) = nrm LL a * nrm LL b := by
  simp only [nrm, MulMemClass.coe_mul, norm_mul]
theorem nrm_eq_zero (a : ↥(OL LL)) : nrm LL a = 0 ↔ a = 0 := by
  simp [nrm]
theorem dvd_iff (a b : ↥(OL LL)) : a ∣ b ↔ nrm LL b ≤ nrm LL a := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [nrm_mul]
    have h1 := nrm_le LL c
    have h0 : 0 ≤ nrm LL a := norm_nonneg _
    nlinarith
  · intro h
    by_cases ha : a = 0
    · subst ha
      have h0 : nrm LL b = 0 := le_antisymm (by simpa [nrm] using h) (norm_nonneg _)
      rw [(nrm_eq_zero LL b).mp h0]
    · have ha' : ((a : ↥LL.1) : PadicAlgCl l) ≠ 0 := by
        intro h0
        apply ha
        exact (nrm_eq_zero LL a).mp (by simp [nrm, h0])
      have ha'' : (a : ↥LL.1) ≠ 0 := fun h0 => ha' (by simp [h0])
      have hc : (b : ↥LL.1) / (a : ↥LL.1) ∈ OL LL := by
        rw [mem_OL]
        have hpos : 0 < ‖((a : ↥LL.1) : PadicAlgCl l)‖ := norm_pos_iff.mpr ha'
        simp only [IntermediateField.coe_div, norm_div]
        rw [div_le_one hpos]
        exact h
      refine ⟨⟨_, hc⟩, ?_⟩
      apply Subtype.ext
      simp only [MulMemClass.coe_mul]
      field_simp
theorem isUnit_iff (a : ↥(OL LL)) : IsUnit a ↔ nrm LL a = 1 := by
  rw [isUnit_iff_dvd_one, dvd_iff]
  have h1 : nrm LL 1 = 1 := by simp [nrm]
  rw [h1]
  constructor
  · intro h
    exact le_antisymm (nrm_le LL a) h
  · intro h
    rw [h]
instance : IsLocalRing ↥(OL LL) := .of_nonunits_add fun a b ha hb => by
  rw [mem_nonunits_iff, isUnit_iff] at *
  have h1 := lt_of_le_of_ne (nrm_le LL a) ha
  have h2 := lt_of_le_of_ne (nrm_le LL b) hb
  exact ((PadicAlgCl.isNonarchimedean l _ _).trans_lt (max_lt h1 h2)).ne
theorem mem_max (a : ↥(OL LL)) : a ∈ maximalIdeal ↥(OL LL) ↔ nrm LL a < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff]
  constructor
  · intro h
    exact lt_of_le_of_ne (nrm_le LL a) h
  · intro h h'
    rw [h'] at h
    exact lt_irrefl _ h
instance : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
instance OL_finite : Module.Finite ℤ_[l] ↥(OL LL) :=
  IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
theorem l_mem_max : ((l : ℕ) : ↥(OL LL)) ∈ maximalIdeal ↥(OL LL) := by
  rw [mem_max]
  show ‖(((l : ↥(OL LL)) : ↥LL.1) : PadicAlgCl l)‖ < 1
  have h1 : (((l : ↥(OL LL)) : ↥LL.1) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by
    simp
  rw [h1, norm_eq_spectralValue, minpoly.eq_X_sub_C (PadicAlgCl l) (l : ℚ_[l]), spectralValue_X_sub_C]
  exact Padic.norm_p_lt_one
instance OL_dvr : IsDiscreteValuationRing ↥(OL LL) := by
  have hded : IsDedekindDomain ↥(OL LL) :=
    IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
  have hnf : ¬ IsField ↥(OL LL) := fun hf => by
    have hm := l_mem_max LL
    rw [isField_iff_maximalIdeal_eq.mp hf, Ideal.mem_bot] at hm
    exact hl.out.ne_zero (Nat.cast_injective (R := ↥(OL LL)) (by simpa using hm))
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 0 2).mpr hded
instance OL_frac : IsFractionRing ↥(OL LL) ↥LL.1 :=
  integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
end Formalism.BasicNotions.Examples₂.LB


