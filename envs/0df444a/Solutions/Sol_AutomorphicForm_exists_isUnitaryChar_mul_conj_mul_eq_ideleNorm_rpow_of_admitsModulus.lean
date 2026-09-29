-- Prove2me | solution 1 for AutomorphicForm.exists_isUnitaryChar_mul_conj_mul_eq_ideleNorm_rpow_of_admitsModulus
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/f816bf1b-6690-5ef6-8c0e-ce258f8ae56a

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_NumberField_IdeleBox
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isUnitaryChar_mul_conj_mul_eq_ideleNorm_rpow_of_admitsModulus
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.TateGlobal AutomorphicForm IsDedekindDomain HeckeCharacter
open scoped NNReal

theorem solution
    (K : Type) [Field K] [NumberField K]
    (ω₁ ω₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
    (hω₁ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ω₁ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
    (hω₂ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ω₂ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
    (hω₁c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ω₁ z : ℂˣ) : ℂ))
    (hω₂c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ω₂ z : ℂˣ) : ℂ))
    (hω₁F : IsIdeleClassChar (𝓞 K) K ω₁) (hω₂F : IsIdeleClassChar (𝓞 K) K ω₂)
    (N₁ N₂ : Ideal (𝓞 K)) (hN₁ : N₁ ≠ ⊥) (hN₂ : N₂ ≠ ⊥)
    (hmod₁ : HeckeCharacter.AdmitsModulus K ω₁ N₁) (hmod₂ : HeckeCharacter.AdmitsModulus K ω₂ N₂) :
    ∃ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
      IsUnitaryChar (𝓞 K) K ν ∧ IsIdeleClassChar (𝓞 K) K ν ∧
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((ω₁ z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ω₂ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ)) ∧
      (∀ (v : HeightOneSpectrum (𝓞 K)) (n : ℕ), HeckeCharacter.idealMultiplicity K v N₁ ≤ n →
        HeckeCharacter.idealMultiplicity K v N₂ ≤ n → 1 ≤ n →
        ∀ t : (v.adicCompletion K)ˣ, Valued.v ((t : v.adicCompletion K) - 1) ≤
            ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
          NumberField.TateGlobal.localChar ν v t = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), ¬ v.asIdeal ∣ N₁ → ¬ v.asIdeal ∣ N₂ →
        NumberField.TateGlobal.IsUnramifiedCharAt ν v) := by

  let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
    ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
  have hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ) := fun t => NumberField.TateGlobal.ideleNorm_pos (F := K) t
  have hα_eq : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ((α z : ℝˣ) : ℝ) = NumberField.TateGlobal.ideleNorm K z := fun z => rfl
  set ω₂c : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := (Units.map ((starRingEnd ℂ : ℂ →+* ℂ) : ℂ →* ℂ)).comp ω₂ with hω₂cdef
  have hω₂c_apply : ∀ z, ((ω₂c z : ℂˣ) : ℂ) = (starRingEnd ℂ) ((ω₂ z : ℂˣ) : ℂ) := fun z => rfl
  set nrm : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := cpowChar α hα ((2 * w : ℝ) : ℂ) with hnrmdef
  have hnrm_apply : ∀ z, ((nrm z : ℂˣ) : ℂ) = ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ) := by
    intro z
    rw [hnrmdef, cpowChar_apply_val, hα_eq, Complex.ofReal_cpow (NumberField.TateGlobal.ideleNorm_pos z).le,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
  set ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := nrm * (ω₁ * ω₂c)⁻¹ with hνdef
  have hPne : ∀ z, ((ω₁ z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ω₂ z : ℂˣ) : ℂ) ≠ 0 := fun z =>
    mul_ne_zero (Units.ne_zero _) ((map_ne_zero _).mpr (Units.ne_zero _))
  have hν_apply : ∀ z, ((ν z : ℂˣ) : ℂ) = ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ) *
      (((ω₁ z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ω₂ z : ℂˣ) : ℂ))⁻¹ := by
    intro z
    rw [hνdef, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_mul, hnrm_apply, hω₂c_apply]
  have htot : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ((ω₁ z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ω₂ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
        ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ) := by
    intro z
    rw [hν_apply, mul_left_comm, mul_inv_cancel₀ (hPne z), mul_one]
  have hνu : IsUnitaryChar (𝓞 K) K ν := by
    intro z
    have h0 := NumberField.TateGlobal.ideleNorm_pos (F := K) z
    rw [hν_apply, norm_mul, norm_inv, norm_mul, RCLike.norm_conj, hω₁ z, hω₂ z, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg h0.le _), two_mul, Real.rpow_add h0,
      mul_inv_cancel₀ (mul_pos (Real.rpow_pos_of_pos h0 _) (Real.rpow_pos_of_pos h0 _)).ne']
  have hprin : IsPrincipalTrivial (R := 𝓞 K) (K := K) α := by
    intro uu
    apply Units.ext
    letI : MeasurableSpace (AdeleRing (𝓞 K) K) := borel _
    haveI : BorelSpace (AdeleRing (𝓞 K) K) := ⟨rfl⟩
    have h : distribHaarChar (AdeleRing (𝓞 K) K)
        (Units.map ((algebraMap K (AdeleRing (𝓞 K) K) : K →+* AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) uu) = 1 :=
      NumberField.AdeleRing.distribHaarChar_algebraMap K uu
    change ((NNReal.toRealHom : ℝ≥0 →+* ℝ) (distribHaarChar (AdeleRing (𝓞 K) K) _) : ℝ) = _
    rw [h]
    rfl
  have hνF : IsIdeleClassChar (𝓞 K) K ν := by
    intro uu
    have h1 := hω₁F uu
    have h2 := hω₂F uu
    have h3 := cpowChar_isIdeleClassChar (hα := hα) hprin ((2 * w : ℝ) : ℂ) uu
    rw [hνdef, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.mul_apply, h3, h1, hω₂cdef, MonoidHom.comp_apply, h2,
      map_one]
    simp
  have hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ) := by
    have hn : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp
        ((NumberField.TateGlobal.continuous_ideleNorm K).rpow_const fun z =>
          Or.inl (NumberField.TateGlobal.ideleNorm_pos (F := K) z).ne')
    simp_rw [hν_apply]
    exact hn.mul ((hω₁c.mul (Complex.continuous_conj.comp hω₂c)).inv₀ hPne)

  have hνcore : ∀ (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ), Valued.v (t : v.adicCompletion K) = 1 →
      Valued.v ((t : v.adicCompletion K) - 1) ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity K v N₁ : ℤ)) →
      Valued.v ((t : v.adicCompletion K) - 1) ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity K v N₂ : ℤ)) →
      NumberField.TateGlobal.localChar ν v t = 1 := by
    intro v t ht1 hτ hσ
    set ι : (AdeleRing (𝓞 K) K)ˣ := Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t) with hιdef
    have hι1 : ((ι : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 = 1 := rfl
    have hιv : ((ι : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v = t := localUnit_apply_self (𝓞 K) K v t
    have hιw : ∀ w' : HeightOneSpectrum (𝓞 K), w' ≠ v → ((ι : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w' = 1 :=
      fun w' hw => localUnit_apply_of_ne (𝓞 K) K v t hw
    have hcond : ∀ N : Ideal (𝓞 K),
        Valued.v ((t : v.adicCompletion K) - 1) ≤ WithZero.exp (-(HeckeCharacter.idealMultiplicity K v N : ℤ)) →
        ∀ w' : HeightOneSpectrum (𝓞 K),
          Valued.v (((ι : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w') = 1 ∧
          Valued.v (((ι : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w' - 1) ≤
            WithZero.exp (-(HeckeCharacter.idealMultiplicity K w' N : ℤ)) := by
      intro N hN w'
      by_cases hw : w' = v
      · subst hw; rw [hιv]; exact ⟨ht1, hN⟩
      · rw [hιw w' hw, sub_self, map_one, map_zero]; exact ⟨rfl, zero_le'⟩
    have hτ1 : ω₁ ι = 1 := hmod₁ ι hι1 (hcond _ hτ)
    have hσ1 : ω₂ ι = 1 := hmod₂ ι hι1 (hcond _ hσ)
    have hιint : NumberField.AdeleRing.finitePartUnits (𝓞 K) K ι ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 K) K := by
      rw [IsDedekindDomain.FiniteAdeleRing.mem_unitIdeles_iff]
      have hinv : ((NumberField.AdeleRing.finitePartUnits (𝓞 K) K ι)⁻¹ : (FiniteAdeleRing (𝓞 K) K)ˣ) =
          NumberField.AdeleRing.finitePartUnits (𝓞 K) K (Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t⁻¹)) := by
        rw [← map_inv, hιdef, ← map_inv, ← map_inv]
      refine ⟨fun w' => ?_, fun w' => ?_⟩
      · rw [NumberField.AdeleRing.val_finitePartUnits, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
        by_cases hw : w' = v
        · subst hw; rw [hιv, ht1]
        · rw [hιw w' hw, map_one]
      · rw [hinv, NumberField.AdeleRing.val_finitePartUnits, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
        by_cases hw : w' = v
        · subst hw
          rw [show ((Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K w' t⁻¹) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w' =
              ((t⁻¹ : (w'.adicCompletion K)ˣ) : w'.adicCompletion K) from localUnit_apply_self (𝓞 K) K w' t⁻¹,
            Units.val_inv_eq_inv_val, map_inv₀, ht1, inv_one]
        · rw [show ((Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t⁻¹) : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w' = 1
              from localUnit_apply_of_ne (𝓞 K) K v t⁻¹ hw, map_one]
    have hn1 : NumberField.TateGlobal.ideleNorm K ι = 1 :=
      NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles K ι hι1 hιint
    show ν ι = 1
    apply Units.ext
    rw [hν_apply, hn1, Real.one_rpow, hτ1, hσ1, Units.val_one, map_one, Complex.ofReal_one, mul_one, inv_one, mul_one]
  refine ⟨ν, hνu, hνF, hνc, htot, ?_, ?_⟩
  · intro v n h1 h2 hn t ht
    have hlt1 : ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
      rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
      omega
    have ht1 : Valued.v (t : v.adicCompletion K) = 1 := by
      have h := Valuation.map_one_add_of_lt (Valued.v) (lt_of_le_of_lt ht hlt1)
      rwa [add_sub_cancel] at h
    have hexp : ∀ {e : ℕ}, e ≤ n → ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤
        WithZero.exp (-(e : ℤ)) := by
      intro e he
      show WithZero.exp (-(n : ℤ)) ≤ WithZero.exp (-(e : ℤ))
      rw [WithZero.exp_le_exp]
      omega
    exact hνcore v t ht1 (ht.trans (hexp h1)) (ht.trans (hexp h2))
  · intro v hv1 hv2 t ht hti
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at ht hti
    have ht1 : Valued.v (t : v.adicCompletion K) = 1 := by
      refine le_antisymm ht ?_
      rw [Units.val_inv_eq_inv_val, map_inv₀] at hti
      have h0 : Valued.v (t : v.adicCompletion K) ≠ 0 := (Valuation.ne_zero_iff _).mpr (Units.ne_zero t)
      exact (inv_le_one₀ (zero_lt_iff.mpr h0)).mp hti
    have hsub : Valued.v ((t : v.adicCompletion K) - 1) ≤ 1 := by
      refine (Valuation.map_sub _ _ _).trans ?_
      rw [ht1, map_one, max_self]
    have hmult0 : ∀ {N : Ideal (𝓞 K)}, N ≠ ⊥ → ¬ v.asIdeal ∣ N → HeckeCharacter.idealMultiplicity K v N = 0 := by
      intro N hN hdvd
      by_contra hne
      exact hdvd ((Associates.count_ne_zero_iff_dvd hN v.irreducible).mp hne)
    refine hνcore v t ht1 ?_ ?_
    · rw [hmult0 hN₁ hv1, Nat.cast_zero, neg_zero, WithZero.exp_zero]; exact hsub
    · rw [hmult0 hN₂ hv2, Nat.cast_zero, neg_zero, WithZero.exp_zero]; exact hsub

end S_AutomorphicForm_exists_isUnitaryChar_mul_conj_mul_eq_ideleNorm_rpow_of_admitsModulus
end P2MW
export P2MW.S_AutomorphicForm_exists_isUnitaryChar_mul_conj_mul_eq_ideleNorm_rpow_of_admitsModulus (solution)
