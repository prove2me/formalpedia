-- Prove2me | solution 1 for AutomorphicForm.IdeleChar.exists_finiteOrderHeckeChar_chiNegThree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/da81c2d6-0b0c-5225-9cbf-59bd1366b606

import Definitions.Def_HeckeCharacter_FiniteOrder
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_ModularForm_EisensteinChiNegThree
import Definitions.Def_LanglandsTunnell_RealizationDictionary
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.NumberField.Units.Basic
import Theorems.Thm_NumberField_AdelicLevel_finiteIdeleClassNumberOne_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_IdeleChar_exists_finiteOrderHeckeChar_chiNegThree

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
p2m_open "Rat.HeightOneSpectrum NumberField.AdelicLevel AutomorphicForm P2MW.S_AutomorphicForm_IdeleChar_exists_finiteOrderHeckeChar_chiNegThree.AutomorphicForm"

namespace AutomorphicForm
p2m_export "AutomorphicForm" "AdelicGL2 IsIdeleClassChar IsUnitaryChar chiDet uniformizerIdele ratPrime finiteAdelicGL2Subgroup IsKfSmooth isKfSmooth_iff"
namespace IdeleChar
p2m_open "AutomorphicForm"

local notation "𝔸ℚ" => AdeleRing (𝓞 ℚ) ℚ
local notation "𝔸ℚf" => FiniteAdeleRing (𝓞 ℚ) ℚ

section Primes

private theorem natCast_mem_asIdeal_iff (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : 𝓞 ℚ)) ∈ v.asIdeal ↔ natGenerator v ∣ n := by
  rw [natGenerator_dvd_iff,
    show ((n : ℕ) : ℤ) = Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) ((n : 𝓞 ℚ)) from (map_natCast _ n).symm]
  exact Ideal.apply_mem_of_equiv_iff.symm

private theorem natCast_natGenerator_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) : ((natGenerator v : ℕ) : 𝓞 ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (prime_natGenerator v).ne_zero

private theorem prime_natCast_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) : Prime ((natGenerator v : ℕ) : 𝓞 ℚ) := by
  have hcast : ((natGenerator v : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((natGenerator v : ℕ) : ℤ) :=
    (map_natCast (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) _).symm
  rw [hcast]
  exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr
    (Nat.prime_iff_prime_int.mp (prime_natGenerator v))

private theorem asIdeal_eq_span_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.asIdeal = Ideal.span {((natGenerator v : ℕ) : 𝓞 ℚ)} := by
  have hmax : (Ideal.span {((natGenerator v : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (natCast_natGenerator_ne_zero v)).mpr
      (prime_natCast_natGenerator v)).isMaximal
      ((Ideal.span_singleton_eq_bot (α := 𝓞 ℚ)).not.mpr (natCast_natGenerator_ne_zero v))
  exact (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr
    ((natCast_mem_asIdeal_iff v _).mpr dvd_rfl))).symm

private theorem valuation_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.valuation ℚ ((natGenerator v : ℕ) : ℚ) = exp (-1 : ℤ) := by
  rw [show ((natGenerator v : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((natGenerator v : ℕ) : 𝓞 ℚ) from
      (map_natCast (algebraMap (𝓞 ℚ) ℚ) _).symm, valuation_of_algebraMap]
  exact intValuation_singleton v (natCast_natGenerator_ne_zero v) (asIdeal_eq_span_natGenerator v)

private theorem valuation_natCast_of_not_dvd (v : HeightOneSpectrum (𝓞 ℚ)) {n : ℕ} (h : ¬ natGenerator v ∣ n) :
    v.valuation ℚ ((n : ℕ) : ℚ) = 1 := by
  rw [show ((n : ℕ) : ℚ) = algebraMap (𝓞 ℚ) ℚ ((n : ℕ) : 𝓞 ℚ) from (map_natCast (algebraMap (𝓞 ℚ) ℚ) _).symm,
    valuation_of_algebraMap]
  exact intValuation_eq_one_iff.mpr fun hmem => h ((natCast_mem_asIdeal_iff v n).mp hmem)

private theorem primesEquiv_ratPrime (p : Nat.Primes) : primesEquiv (R := 𝓞 ℚ) (ratPrime p) = p :=
  Equiv.apply_symm_apply _ p

private theorem natGenerator_ratPrime (p : Nat.Primes) : natGenerator (ratPrime p) = (p : ℕ) :=
  congrArg Subtype.val (primesEquiv_ratPrime p)

private theorem eq_ratPrime_of_natGenerator_eq {v : HeightOneSpectrum (𝓞 ℚ)} {p : Nat.Primes}
    (h : natGenerator v = (p : ℕ)) : v = ratPrime p := by
  have h' : primesEquiv (R := 𝓞 ℚ) v = p := Subtype.ext h
  rw [← h']
  exact (Equiv.symm_apply_apply _ v).symm

private theorem natGenerator_ne_of_ne_ratPrime {v : HeightOneSpectrum (𝓞 ℚ)} {p : Nat.Primes} (h : v ≠ ratPrime p) :
    natGenerator v ≠ (p : ℕ) := fun h' => h (eq_ratPrime_of_natGenerator_eq h')

private theorem valuation_prime_of_ne (p : Nat.Primes) {v : HeightOneSpectrum (𝓞 ℚ)} (h : v ≠ ratPrime p) :
    v.valuation ℚ ((p : ℕ) : ℚ) = 1 :=
  valuation_natCast_of_not_dvd v fun hd =>
    natGenerator_ne_of_ne_ratPrime h (((Nat.prime_dvd_prime_iff_eq (prime_natGenerator v) p.2).mp hd))

private theorem valuation_prime_self (p : Nat.Primes) : (ratPrime p).valuation ℚ ((p : ℕ) : ℚ) = exp (-1 : ℤ) := by
  rw [← natGenerator_ratPrime p]
  exact valuation_natGenerator _

private theorem valued_algebraMap_rat (v : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) :
    Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) = v.valuation ℚ q := by
  rw [algebraMap_adicCompletion]
  exact valuedAdicCompletion_eq_valuation' v q

private theorem algebraMap_adeleRing_snd (q : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (algebraMap ℚ 𝔸ℚ q).2 v = algebraMap ℚ (v.adicCompletion ℚ) q := by
  rw [AdeleRing.algebraMap_snd_apply, algebraMap_adicCompletion]
  rfl

end Primes

section Arch

private def archCoord (x : (𝔸ℚ)ˣ) : ℝ :=
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace ((x : 𝔸ℚ).1 Rat.infinitePlace)

private theorem archCoord_mul (x y : (𝔸ℚ)ˣ) : archCoord (x * y) = archCoord x * archCoord y := by
  unfold archCoord
  rw [← map_mul]
  rfl

private theorem archCoord_one : archCoord 1 = 1 := by
  unfold archCoord
  rw [show ((1 : (𝔸ℚ)ˣ) : 𝔸ℚ).1 Rat.infinitePlace = 1 from rfl, map_one]

private theorem archCoord_ne_zero (x : (𝔸ℚ)ˣ) : archCoord x ≠ 0 := by
  intro h
  have h1 := archCoord_mul x x⁻¹
  rw [mul_inv_cancel, archCoord_one, h, zero_mul] at h1
  exact one_ne_zero h1

private theorem archCoord_principal (q : ℚˣ) :
    archCoord (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q) = ((q : ℚ) : ℝ) :=
  eq_ratCast ((InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace :
      Rat.infinitePlace.Completion ≃+* ℝ).toRingHom.comp
    ((Pi.evalRingHom (fun w : InfinitePlace ℚ => w.Completion) Rat.infinitePlace).comp
      ((RingHom.fst _ _).comp (algebraMap ℚ 𝔸ℚ)))) (q : ℚ)

private theorem archCoord_finIncl (y : (𝔸ℚf)ˣ) : archCoord (Units.map (finIncl (𝓞 ℚ) ℚ) y) = 1 := by
  unfold archCoord
  rw [Units.coe_map, finIncl_apply_fst, show (1 : InfiniteAdeleRing ℚ) Rat.infinitePlace = 1 from rfl, map_one]

end Arch

section Normalizer

private def finPart : (𝔸ℚ)ˣ →* (𝔸ℚf)ˣ := Units.map (RingHom.snd (InfiniteAdeleRing ℚ) 𝔸ℚf).toMonoidHom

private theorem finPart_apply (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((finPart x : (𝔸ℚf)ˣ) : 𝔸ℚf) v = (x : 𝔸ℚ).2 v := rfl

private def IsNormalizer (x : (𝔸ℚ)ˣ) (r : ℚ) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((x : 𝔸ℚ).2 v) = v.valuation ℚ r) ∧ 0 < archCoord x * (r : ℝ)

private theorem valued_snd_mul (x y : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((((x * y : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v) = Valued.v ((x : 𝔸ℚ).2 v) * Valued.v ((y : 𝔸ℚ).2 v) := by
  rw [← map_mul]
  rfl

private theorem valued_snd_inv_mul (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v ((((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v) * Valued.v ((x : 𝔸ℚ).2 v) = 1 := by
  rw [← valued_snd_mul, inv_mul_cancel]
  show Valued.v ((1 : 𝔸ℚf) v) = 1
  rw [show ((1 : 𝔸ℚf)) v = 1 from rfl, map_one]

private theorem valued_snd_ne_zero (x : (𝔸ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) : Valued.v ((x : 𝔸ℚ).2 v) ≠ 0 := by
  intro h0
  have h := valued_snd_inv_mul x v
  rw [h0, mul_zero] at h
  exact zero_ne_one h

private theorem IsNormalizer.ne_zero {x : (𝔸ℚ)ˣ} {r : ℚ} (h : IsNormalizer x r) : r ≠ 0 := by
  rintro rfl
  have := h.2
  rw [Rat.cast_zero, mul_zero] at this
  exact lt_irrefl _ this

private theorem exists_isNormalizer (x : (𝔸ℚ)ˣ) : ∃ r : ℚ, IsNormalizer x r := by
  obtain ⟨α, hα, hα'⟩ := NumberField.AdelicLevel.finiteIdeleClassNumberOne_rat (finPart x)
  have hA0 : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ (α : ℚ) ≠ 0 := fun v h0 =>
    α.ne_zero ((Valuation.zero_iff _).mp h0)

  have hval : ∀ v : HeightOneSpectrum (𝓞 ℚ), Valued.v ((x : 𝔸ℚ).2 v) = v.valuation ℚ (α : ℚ) := by
    intro v
    have h1 : (v.valuation ℚ (α : ℚ))⁻¹ * Valued.v ((x : 𝔸ℚ).2 v) ≤ 1 := by
      have := (mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp (hα v)
      rw [show (algebraMap ℚ 𝔸ℚf ((α⁻¹ : ℚˣ) : ℚ) * (finPart x : 𝔸ℚf)) v
          = algebraMap ℚ (v.adicCompletion ℚ) ((α⁻¹ : ℚˣ) : ℚ) * (x : 𝔸ℚ).2 v from rfl, map_mul,
        valued_algebraMap_rat, Units.val_inv_eq_inv_val, map_inv₀] at this
      exact this
    have h2 : v.valuation ℚ (α : ℚ) * Valued.v ((((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v) ≤ 1 := by
      have := (mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp (hα' v)
      rw [show (algebraMap ℚ 𝔸ℚf ((α : ℚˣ) : ℚ) * ((finPart x)⁻¹ : (𝔸ℚf)ˣ)) v
          = algebraMap ℚ (v.adicCompletion ℚ) ((α : ℚˣ) : ℚ) * (((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v from rfl, map_mul,
        valued_algebraMap_rat] at this
      exact this
    apply le_antisymm
    · calc Valued.v ((x : 𝔸ℚ).2 v)
          = v.valuation ℚ (α : ℚ) * ((v.valuation ℚ (α : ℚ))⁻¹ * Valued.v ((x : 𝔸ℚ).2 v)) := by
            rw [← mul_assoc, mul_inv_cancel₀ (hA0 v), one_mul]
        _ ≤ v.valuation ℚ (α : ℚ) * 1 := mul_le_mul_right h1 _
        _ = v.valuation ℚ (α : ℚ) := mul_one _
    · calc v.valuation ℚ (α : ℚ)
          = (v.valuation ℚ (α : ℚ) * Valued.v ((((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v)) * Valued.v ((x : 𝔸ℚ).2 v) := by
            rw [mul_assoc, valued_snd_inv_mul, mul_one]
        _ ≤ 1 * Valued.v ((x : 𝔸ℚ).2 v) := mul_le_mul_left h2 _
        _ = Valued.v ((x : 𝔸ℚ).2 v) := one_mul _

  by_cases hs : 0 < archCoord x * ((α : ℚ) : ℝ)
  · exact ⟨α, hval, hs⟩
  · refine ⟨-(α : ℚ), fun v => by rw [Valuation.map_neg]; exact hval v, ?_⟩
    have hne : archCoord x * ((α : ℚ) : ℝ) ≠ 0 :=
      mul_ne_zero (archCoord_ne_zero x) (by exact_mod_cast α.ne_zero)
    rw [Rat.cast_neg, mul_neg]
    exact neg_pos.mpr (lt_of_le_of_ne (not_lt.mp hs) hne)

private theorem rat_eq_one_of_valuation_eq_one {q : ℚ} (hq : 0 < q)
    (h : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ q = 1) : q = 1 := by
  have hq0 : q ≠ 0 := hq.ne'
  obtain ⟨z, hz⟩ := mem_integers_of_valuation_le_one ℚ q fun v => (h v).le
  obtain ⟨z', hz'⟩ := mem_integers_of_valuation_le_one ℚ q⁻¹ fun v => by rw [map_inv₀, h v, inv_one]
  have hzz' : z * z' = 1 :=
    IsFractionRing.injective (𝓞 ℚ) ℚ (by rw [map_mul, hz, hz', map_one, mul_inv_cancel₀ hq0])
  have hu : IsUnit z := isUnit_iff_exists_inv.mpr ⟨z', hzz'⟩
  have hzq : (z : ℚ) = q := by rw [RingOfIntegers.coe_eq_algebraMap]; exact hz
  rcases Rat.RingOfIntegers.isUnit_iff.mp hu with h1 | h1
  · rw [← hzq]; exact h1
  · exfalso
    rw [hzq] at h1
    rw [h1] at hq
    exact absurd hq (by norm_num)

private theorem IsNormalizer.unique {x : (𝔸ℚ)ˣ} {r r' : ℚ} (h : IsNormalizer x r) (h' : IsNormalizer x r') : r = r' := by
  have hr' := h'.ne_zero
  have hq : 0 < r / r' := by
    have h3 : (0 : ℝ) < (archCoord x * r) / (archCoord x * r') := div_pos h.2 h'.2
    rw [mul_div_mul_left _ _ (archCoord_ne_zero x)] at h3
    exact_mod_cast h3
  have hval : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.valuation ℚ (r / r') = 1 := fun v => by
    rw [map_div₀, ← h.1 v, ← h'.1 v, div_self (valued_snd_ne_zero x v)]
  have := rat_eq_one_of_valuation_eq_one hq hval
  rwa [div_eq_one_iff_eq hr'] at this

private def ρ (x : (𝔸ℚ)ˣ) : ℚ := Classical.choose (exists_isNormalizer x)

private theorem ρ_spec (x : (𝔸ℚ)ˣ) : IsNormalizer x (ρ x) := Classical.choose_spec (exists_isNormalizer x)

private theorem ρ_ne_zero (x : (𝔸ℚ)ˣ) : ρ x ≠ 0 := (ρ_spec x).ne_zero

private theorem ρ_eq_of_isNormalizer {x : (𝔸ℚ)ˣ} {r : ℚ} (h : IsNormalizer x r) : ρ x = r := (ρ_spec x).unique h

private theorem ρ_mul (x y : (𝔸ℚ)ˣ) : ρ (x * y) = ρ x * ρ y := by
  refine ρ_eq_of_isNormalizer ⟨fun v => ?_, ?_⟩
  · rw [valued_snd_mul, (ρ_spec x).1 v, (ρ_spec y).1 v, map_mul]
  · rw [archCoord_mul, Rat.cast_mul, show archCoord x * archCoord y * (((ρ x : ℚ) : ℝ) * ((ρ y : ℚ) : ℝ))
        = (archCoord x * ((ρ x : ℚ) : ℝ)) * (archCoord y * ((ρ y : ℚ) : ℝ)) by ring]
    exact mul_pos (ρ_spec x).2 (ρ_spec y).2

private theorem ρ_principal (q : ℚˣ) : ρ (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q) = (q : ℚ) := by
  refine ρ_eq_of_isNormalizer ⟨fun v => ?_, ?_⟩
  · rw [Units.coe_map, MonoidHom.coe_coe, algebraMap_adeleRing_snd, valued_algebraMap_rat]
  · rw [archCoord_principal]
    exact mul_self_pos.mpr (by exact_mod_cast q.ne_zero)

private theorem ρ_one : ρ 1 = 1 := by
  have := ρ_principal 1
  rwa [map_one, Units.val_one] at this

private theorem ρ_finIncl_localUnit (p : Nat.Primes) (t : ((ratPrime p).adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : (ratPrime p).adicCompletion ℚ) = exp (-1 : ℤ)) :
    ρ (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ (ratPrime p) t)) = ((p : ℕ) : ℚ) := by
  refine ρ_eq_of_isNormalizer ⟨fun v => ?_, ?_⟩
  · rw [Units.coe_map, finIncl_apply_snd]
    by_cases hv : v = ratPrime p
    · subst hv
      rw [localUnit_apply_self, ht, valuation_prime_self]
    · rw [localUnit_apply_of_ne (𝓞 ℚ) ℚ (ratPrime p) t hv, map_one, valuation_prime_of_ne p hv]
  · rw [archCoord_finIncl, one_mul]
    exact_mod_cast p.2.pos

private theorem ρ_finIncl_localUnit_of_valued_one (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : v.adicCompletion ℚ) = 1) :
    ρ (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t)) = 1 := by
  refine ρ_eq_of_isNormalizer ⟨fun w => ?_, ?_⟩
  · rw [Units.coe_map, finIncl_apply_snd, map_one]
    by_cases hw : w = v
    · subst hw
      rw [localUnit_apply_self, ht]
    · rw [localUnit_apply_of_ne (𝓞 ℚ) ℚ v t hw, map_one]
  · rw [archCoord_finIncl, one_mul, Rat.cast_one]
    exact one_pos

end Normalizer

section Character

private def p3 : Nat.Primes := ⟨3, Nat.prime_three⟩

private def v3 : HeightOneSpectrum (𝓞 ℚ) := ratPrime p3

private theorem natGenerator_v3 : natGenerator v3 = 3 := natGenerator_ratPrime p3

private def unitAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : v.adicCompletion ℚ :=
  (x : 𝔸ℚ).2 v * (algebraMap ℚ (v.adicCompletion ℚ) (ρ x))⁻¹

private theorem valued_unitAt (v : HeightOneSpectrum (𝓞 ℚ)) (x : (𝔸ℚ)ˣ) : Valued.v (unitAt v x) = 1 := by
  unfold unitAt
  rw [map_mul, map_inv₀, valued_algebraMap_rat, ← (ρ_spec x).1 v, mul_inv_cancel₀ (valued_snd_ne_zero x v)]

private theorem unitAt_mul (v : HeightOneSpectrum (𝓞 ℚ)) (x y : (𝔸ℚ)ˣ) : unitAt v (x * y) = unitAt v x * unitAt v y := by
  unfold unitAt
  rw [ρ_mul, map_mul, mul_inv, show (((x * y : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v = (x : 𝔸ℚ).2 v * (y : 𝔸ℚ).2 v from rfl]
  ring

private theorem unitAt_one (v : HeightOneSpectrum (𝓞 ℚ)) : unitAt v 1 = 1 := by
  unfold unitAt
  rw [ρ_one, map_one, inv_one, mul_one]
  rfl

private def unitInt3 (x : (𝔸ℚ)ˣ) : v3.adicCompletionIntegers ℚ :=
  ⟨unitAt v3 x, (mem_adicCompletionIntegers (𝓞 ℚ) ℚ v3).mpr (valued_unitAt v3 x).le⟩

private theorem unitInt3_mul (x y : (𝔸ℚ)ˣ) : unitInt3 (x * y) = unitInt3 x * unitInt3 y :=
  Subtype.ext (unitAt_mul v3 x y)

private theorem unitInt3_one : unitInt3 1 = 1 := Subtype.ext (unitAt_one v3)

private theorem isUnit_unitInt3 (x : (𝔸ℚ)ˣ) : IsUnit (unitInt3 x) :=
  isUnit_iff_exists_inv.mpr ⟨unitInt3 x⁻¹, by rw [← unitInt3_mul, mul_inv_cancel, unitInt3_one]⟩

private def E3 : v3.adicCompletionIntegers ℚ ≃+* ℤ_[3] :=
  (PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) p3).symm.toAlgEquiv.toRingEquiv

private def res3 : v3.adicCompletionIntegers ℚ →+* ZMod 3 := (PadicInt.toZMod : ℤ_[3] →+* ZMod 3).comp E3.toRingHom

private theorem res3_apply (y : v3.adicCompletionIntegers ℚ) : res3 y = PadicInt.toZMod (E3 y) := rfl

private theorem res3_eq_one_of_valued_sub_one_lt {y : v3.adicCompletionIntegers ℚ}
    (hy : Valued.v ((y : v3.adicCompletion ℚ) - 1) < 1) : res3 y = 1 := by
  have hnu : ¬ IsUnit (y - 1) := by
    intro hunit
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hunit
    have hprod : Valued.v (((y - 1 : v3.adicCompletionIntegers ℚ)) : v3.adicCompletion ℚ)
        * Valued.v ((w : v3.adicCompletion ℚ)) = 1 := by
      rw [← map_mul, show (((y - 1 : v3.adicCompletionIntegers ℚ)) : v3.adicCompletion ℚ) * (w : v3.adicCompletion ℚ)
          = (((y - 1) * w : v3.adicCompletionIntegers ℚ) : v3.adicCompletion ℚ) from rfl, hw]
      exact map_one _
    have hwle : Valued.v ((w : v3.adicCompletion ℚ)) ≤ 1 := (mem_adicCompletionIntegers (𝓞 ℚ) ℚ v3).mp w.2
    have hlt : Valued.v (((y - 1 : v3.adicCompletionIntegers ℚ)) : v3.adicCompletion ℚ) < 1 := hy
    have hlt' : Valued.v (((y - 1 : v3.adicCompletionIntegers ℚ)) : v3.adicCompletion ℚ)
        * Valued.v ((w : v3.adicCompletion ℚ)) < 1 :=
      calc Valued.v (((y - 1 : v3.adicCompletionIntegers ℚ)) : v3.adicCompletion ℚ)
              * Valued.v ((w : v3.adicCompletion ℚ))
          ≤ Valued.v (((y - 1 : v3.adicCompletionIntegers ℚ)) : v3.adicCompletion ℚ) * 1 := mul_le_mul_right hwle _
        _ = Valued.v (((y - 1 : v3.adicCompletionIntegers ℚ)) : v3.adicCompletion ℚ) := mul_one _
        _ < 1 := hlt
    exact absurd hprod (ne_of_lt hlt')
  have hker : res3 (y - 1) = 0 := by
    rw [res3_apply, ← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => hnu ((isUnit_map_iff E3 _).mp h)
  rwa [map_sub, map_one, sub_eq_zero] at hker

private theorem res3_unitInt3_ne_zero (x : (𝔸ℚ)ˣ) : res3 (unitInt3 x) ≠ 0 :=
  ((isUnit_unitInt3 x).map res3).ne_zero

private def psi3 (r : ZMod 3) : ℤˣ := if r = 2 then -1 else 1

private theorem psi3_mul : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 → psi3 (a * b) = psi3 a * psi3 b := by decide

private theorem psi3_one : psi3 1 = 1 := by decide

private theorem psi3_eq_one_or (r : ZMod 3) : psi3 r = 1 ∨ psi3 r = -1 := by
  unfold psi3; split_ifs <;> simp

private def chi3IdeleInt : (𝔸ℚ)ˣ →* ℤˣ where
  toFun x := psi3 (res3 (unitInt3 x))
  map_one' := by
    show psi3 (res3 (unitInt3 1)) = 1
    rw [unitInt3_one, map_one, psi3_one]
  map_mul' x y := by
    show psi3 (res3 (unitInt3 (x * y))) = psi3 (res3 (unitInt3 x)) * psi3 (res3 (unitInt3 y))
    rw [unitInt3_mul, map_mul, psi3_mul _ _ (res3_unitInt3_ne_zero x) (res3_unitInt3_ne_zero y)]

private theorem chi3IdeleInt_apply (x : (𝔸ℚ)ˣ) : chi3IdeleInt x = psi3 (res3 (unitInt3 x)) := rfl

private theorem chi3IdeleInt_eq_one_or (x : (𝔸ℚ)ˣ) : chi3IdeleInt x = 1 ∨ chi3IdeleInt x = -1 :=
  psi3_eq_one_or _

private theorem chi3IdeleInt_sq (x : (𝔸ℚ)ˣ) : chi3IdeleInt x ^ 2 = 1 := by
  rcases chi3IdeleInt_eq_one_or x with h | h <;> rw [h] <;> decide

private def chi3IdeleChar : (𝔸ℚ)ˣ →* ℂˣ := (Units.map (Int.castRingHom ℂ : ℤ →* ℂ)).comp chi3IdeleInt

private theorem chi3IdeleChar_apply (x : (𝔸ℚ)ˣ) :
    ((chi3IdeleChar x : ℂˣ) : ℂ) = (((chi3IdeleInt x : ℤˣ) : ℤ) : ℂ) := rfl

end Character

section Block

private theorem isIdeleClassChar_chi3IdeleChar : IsIdeleClassChar (𝓞 ℚ) ℚ chi3IdeleChar := by
  intro q
  show (Units.map (Int.castRingHom ℂ : ℤ →* ℂ)) (chi3IdeleInt (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q)) = 1
  have h1 : unitInt3 (Units.map (algebraMap ℚ 𝔸ℚ : ℚ →* 𝔸ℚ) q) = 1 := by
    refine Subtype.ext ?_
    show unitAt v3 _ = 1
    unfold unitAt
    rw [ρ_principal, Units.coe_map, MonoidHom.coe_coe, algebraMap_adeleRing_snd,
      mul_inv_cancel₀ ((map_ne_zero _).mpr q.ne_zero)]
  rw [chi3IdeleInt_apply, h1, map_one, psi3_one, map_one]

private theorem chi3IdeleChar_apply_eq_one_or (x : (𝔸ℚ)ˣ) :
    ((chi3IdeleChar x : ℂˣ) : ℂ) = 1 ∨ ((chi3IdeleChar x : ℂˣ) : ℂ) = -1 := by
  rw [chi3IdeleChar_apply]
  rcases chi3IdeleInt_eq_one_or x with h | h <;> rw [h] <;> simp

private theorem isUnitaryChar_chi3IdeleChar : IsUnitaryChar (𝓞 ℚ) ℚ chi3IdeleChar := fun x => by
  rcases chi3IdeleChar_apply_eq_one_or x with h | h <;> rw [h] <;> simp

private theorem chi3IdeleChar_sq : chi3IdeleChar ^ 2 = 1 := by
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  show (Units.map (Int.castRingHom ℂ : ℤ →* ℂ)) (chi3IdeleInt x) ^ 2 = 1
  rw [← map_pow, chi3IdeleInt_sq, map_one]

private theorem isOfFinOrder_chi3IdeleChar : IsOfFinOrder chi3IdeleChar :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨2, two_pos, chi3IdeleChar_sq⟩

private theorem isFiniteOrderHeckeChar_of_continuous (hc : Continuous chi3IdeleChar) :
    HeckeCharacter.IsFiniteOrderHeckeChar ℚ chi3IdeleChar :=
  ⟨isIdeleClassChar_chi3IdeleChar, hc, isOfFinOrder_chi3IdeleChar⟩

private theorem idealMultiplicity_v3_self : HeckeCharacter.idealMultiplicity ℚ v3 v3.asIdeal = 1 := by
  unfold HeckeCharacter.idealMultiplicity
  exact Associates.count_self v3.associates_irreducible

private theorem v3_asIdeal : v3.asIdeal = Ideal.span {(3 : 𝓞 ℚ)} := by
  rw [asIdeal_eq_span_natGenerator, natGenerator_v3, Nat.cast_ofNat]

private theorem admitsModulus_chi3IdeleChar : HeckeCharacter.AdmitsModulus ℚ chi3IdeleChar v3.asIdeal := by
  intro u hu1 hu
  have hρ : ρ u = 1 := ρ_eq_of_isNormalizer ⟨fun v => by rw [(hu v).1, map_one], by
    unfold archCoord
    rw [hu1, show (1 : InfiniteAdeleRing ℚ) Rat.infinitePlace = 1 from rfl, map_one, one_mul, Rat.cast_one]
    exact one_pos⟩
  have hcoord : ((unitInt3 u : v3.adicCompletionIntegers ℚ) : v3.adicCompletion ℚ) = (u : 𝔸ℚ).2 v3 := by
    show unitAt v3 u = _
    unfold unitAt
    rw [hρ, map_one, inv_one, mul_one]
  have hlt : Valued.v (((unitInt3 u : v3.adicCompletionIntegers ℚ) : v3.adicCompletion ℚ) - 1) < 1 := by
    rw [hcoord]
    refine lt_of_le_of_lt (hu v3).2 ?_
    rw [idealMultiplicity_v3_self, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by norm_num)
  show (Units.map (Int.castRingHom ℂ : ℤ →* ℂ)) (chi3IdeleInt u) = 1
  rw [chi3IdeleInt_apply, res3_eq_one_of_valued_sub_one_lt hlt, psi3_one, map_one]

end Block

section Values

private def primeUnit (p : Nat.Primes) : ((ratPrime p).adicCompletion ℚ)ˣ :=
  Units.mk0 (algebraMap ℚ ((ratPrime p).adicCompletion ℚ) ((p : ℕ) : ℚ))
    ((map_ne_zero _).mpr (by exact_mod_cast p.2.ne_zero))

private theorem valued_primeUnit (p : Nat.Primes) :
    Valued.v (primeUnit p : (ratPrime p).adicCompletion ℚ) = exp (-1 : ℤ) := by
  show Valued.v (algebraMap ℚ ((ratPrime p).adicCompletion ℚ) ((p : ℕ) : ℚ)) = _
  rw [valued_algebraMap_rat, valuation_prime_self]

private def idealeAt (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) : (𝔸ℚ)ˣ :=
  Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v t)

private theorem idealeAt_snd_self (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) :
    ((idealeAt v t : (𝔸ℚ)ˣ) : 𝔸ℚ).2 v = t := by
  unfold idealeAt
  rw [Units.coe_map, finIncl_apply_snd, localUnit_apply_self]

private theorem idealeAt_snd_of_ne (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) {w : HeightOneSpectrum (𝓞 ℚ)}
    (hw : w ≠ v) : ((idealeAt v t : (𝔸ℚ)ˣ) : 𝔸ℚ).2 w = 1 := by
  unfold idealeAt
  rw [Units.coe_map, finIncl_apply_snd, localUnit_apply_of_ne (𝓞 ℚ) ℚ v t hw]

private theorem ratPrime_ne_v3 {p : Nat.Primes} (hp : (p : ℕ) ≠ 3) : ratPrime p ≠ v3 := fun h =>
  hp (by have h' := congrArg natGenerator h; rwa [natGenerator_ratPrime, natGenerator_v3] at h')

private theorem chi3IdeleInt_idealeAt_of_valued_one {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ≠ v3) (t : (v.adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : v.adicCompletion ℚ) = 1) : chi3IdeleInt (idealeAt v t) = 1 := by
  have h1 : unitInt3 (idealeAt v t) = 1 := by
    refine Subtype.ext ?_
    show unitAt v3 _ = 1
    unfold unitAt
    rw [show ρ (idealeAt v t) = 1 from ρ_finIncl_localUnit_of_valued_one v t ht, map_one, inv_one, mul_one,
      idealeAt_snd_of_ne v t (Ne.symm hv)]
  rw [chi3IdeleInt_apply, h1, map_one, psi3_one]

private theorem res3_unitInt3_idealeAt (p : Nat.Primes) (hp : (p : ℕ) ≠ 3) (t : ((ratPrime p).adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : (ratPrime p).adicCompletion ℚ) = exp (-1 : ℤ)) :
    res3 (unitInt3 (idealeAt (ratPrime p) t)) * ((p : ℕ) : ZMod 3) = 1 := by

  have hρ : ρ (idealeAt (ratPrime p) t) = ((p : ℕ) : ℚ) := ρ_finIncl_localUnit p t ht
  have hp0 : (algebraMap ℚ (v3.adicCompletion ℚ) ((p : ℕ) : ℚ)) ≠ 0 :=
    (map_ne_zero _).mpr (by exact_mod_cast p.2.ne_zero)
  let P : v3.adicCompletionIntegers ℚ := ((p : ℕ) : v3.adicCompletionIntegers ℚ)
  have hP : ((P : v3.adicCompletionIntegers ℚ) : v3.adicCompletion ℚ)
      = algebraMap ℚ (v3.adicCompletion ℚ) ((p : ℕ) : ℚ) := by
    rw [map_natCast]
    rfl
  have hmul : unitInt3 (idealeAt (ratPrime p) t) * P = 1 := by
    refine Subtype.ext ?_
    show unitAt v3 (idealeAt (ratPrime p) t) * (P : v3.adicCompletion ℚ) = 1
    unfold unitAt
    rw [hρ, idealeAt_snd_of_ne (ratPrime p) t (Ne.symm (ratPrime_ne_v3 hp)), one_mul, hP, inv_mul_cancel₀ hp0]
  have := congrArg res3 hmul
  rwa [map_mul, map_one, map_natCast] at this

private theorem chi3IdeleInt_idealeAt (p : Nat.Primes) (hp : (p : ℕ) ≠ 3) (t : ((ratPrime p).adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : (ratPrime p).adicCompletion ℚ) = exp (-1 : ℤ)) :
    ((chi3IdeleInt (idealeAt (ratPrime p) t) : ℤˣ) : ℤ) = EisensteinWeightOne.chiNegThree (p : ℕ) := by
  have hres := res3_unitInt3_idealeAt p hp t ht
  rw [chi3IdeleInt_apply]

  have h3 : ¬ 3 ∣ (p : ℕ) := fun hd => hp ((Nat.prime_dvd_prime_iff_eq Nat.prime_three p.2).mp hd).symm
  have hm : (p : ℕ) % 3 = 1 ∨ (p : ℕ) % 3 = 2 := by omega
  have hcast : ((p : ℕ) : ZMod 3) = (((p : ℕ) % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod (p : ℕ) 3).symm
  rw [hcast] at hres
  unfold EisensteinWeightOne.chiNegThree
  rcases hm with hm | hm <;> rw [hm] at hres ⊢
  ·
    rw [Nat.cast_one, mul_one] at hres
    rw [hres]
    decide
  ·
    have hr : res3 (unitInt3 (idealeAt (ratPrime p) t)) = 2 := by
      have key : ∀ r : ZMod 3, r * 2 = 1 → r = 2 := by decide
      exact key _ (by exact_mod_cast hres)
    rw [hr]
    decide

private theorem chi3IdeleChar_idealeAt (p : Nat.Primes) (hp : (p : ℕ) ≠ 3) (t : ((ratPrime p).adicCompletion ℚ)ˣ)
    (ht : Valued.v (t : (ratPrime p).adicCompletion ℚ) = exp (-1 : ℤ)) :
    ((chi3IdeleChar (idealeAt (ratPrime p) t) : ℂˣ) : ℂ) = ((EisensteinWeightOne.chiNegThree (p : ℕ) : ℤ) : ℂ) := by
  rw [chi3IdeleChar_apply, chi3IdeleInt_idealeAt p hp t ht]

private theorem chi3IdeleInt_idealeAt_three : chi3IdeleInt (idealeAt v3 (primeUnit p3)) = 1 := by
  have hρ : ρ (idealeAt v3 (primeUnit p3)) = ((3 : ℕ) : ℚ) := ρ_finIncl_localUnit p3 _ (valued_primeUnit p3)
  have h1 : unitInt3 (idealeAt v3 (primeUnit p3)) = 1 := by
    refine Subtype.ext ?_
    show unitAt v3 _ = 1
    unfold unitAt
    rw [hρ, idealeAt_snd_self]
    exact mul_inv_cancel₀ ((map_ne_zero _).mpr (Nat.cast_ne_zero.mpr p3.2.ne_zero))
  rw [chi3IdeleInt_apply, h1, map_one, psi3_one]

private theorem det_diagOne {A : Type*} [CommRing A] (a : Aˣ) : Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (Matrix.diagonal ![(a : A), 1]) = (a : A)
  rw [Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

private theorem det_heckeGenAt (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) :
    Matrix.GeneralLinearGroup.det (heckeGenAt (𝓞 ℚ) ℚ v t) = idealeAt v t :=
  det_diagOne _

private theorem chi3IdeleChar_det_heckeGen (p : Nat.Primes) (hp : (p : ℕ) ≠ 3) :
    ((chi3IdeleChar (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 ℚ) ℚ (ratPrime p))) : ℂˣ) : ℂ)
      = ((EisensteinWeightOne.chiNegThree (p : ℕ) : ℤ) : ℂ) := by
  rw [show heckeGen (𝓞 ℚ) ℚ (ratPrime p) = heckeGenAt (𝓞 ℚ) ℚ (ratPrime p) (uniformizerUnit ℚ (ratPrime p)) from rfl,
    det_heckeGenAt]
  exact chi3IdeleChar_idealeAt p hp _ (valued_uniformizerUnit ℚ (ratPrime p))

example :
    ((chi3IdeleInt (idealeAt (ratPrime ⟨2, Nat.prime_two⟩) (primeUnit ⟨2, Nat.prime_two⟩)) : ℤˣ) : ℤ) = -1 := by
  rw [chi3IdeleInt_idealeAt ⟨2, Nat.prime_two⟩ (by decide) _ (valued_primeUnit _)]; decide

example :
    ((chi3IdeleInt (idealeAt (ratPrime ⟨5, Nat.prime_five⟩) (primeUnit ⟨5, Nat.prime_five⟩)) : ℤˣ) : ℤ) = -1 := by
  rw [chi3IdeleInt_idealeAt ⟨5, Nat.prime_five⟩ (by decide) _ (valued_primeUnit _)]; decide

example :
    ((chi3IdeleInt (idealeAt (ratPrime ⟨7, by norm_num⟩) (primeUnit ⟨7, by norm_num⟩)) : ℤˣ) : ℤ) = 1 := by
  rw [chi3IdeleInt_idealeAt ⟨7, by norm_num⟩ (by decide) _ (valued_primeUnit _)]; decide

end Values

section Neighbourhood

private def integralSet : Set 𝔸ℚ := {a | ∀ v : HeightOneSpectrum (𝓞 ℚ), a.2 v ∈ v.adicCompletionIntegers ℚ}

private theorem isOpen_integralSet : IsOpen integralSet := by
  have hA : ∀ v : HeightOneSpectrum (𝓞 ℚ), IsOpen ((v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) :=
    fun v => Valued.isOpen_valuationSubring _
  have h := RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 ℚ) => v.adicCompletion ℚ)
    (A := fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) hA
  exact h.preimage continuous_snd

private def congSet : Set 𝔸ℚ := {a | Valued.v (a.2 v3 - 1) < 1}

private theorem isOpen_congSet : IsOpen congSet := by
  have hball : IsOpen {y : v3.adicCompletion ℚ | Valued.v (y - 1) < 1} := by
    refine isOpen_iff_mem_nhds.mpr fun y hy => Valued.mem_nhds.mpr ⟨1, fun z hz => ?_⟩
    have hz1 : Valued.v.restrict (z - y) < 1 := hz
    have hz' : Valued.v (z - y) < 1 := (Valuation.restrict_lt_one_iff _).mp hz1
    have : z - 1 = (z - y) + (y - 1) := by ring
    show Valued.v (z - 1) < 1
    rw [this]
    exact Valuation.map_add_lt _ hz' hy
  exact hball.preimage ((RestrictedProduct.continuous_eval v3).comp continuous_snd)

private def posSet : Set 𝔸ℚ :=
  {a | 0 < InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace (a.1 Rat.infinitePlace)}

private theorem isOpen_posSet : IsOpen posSet := by
  have hc : Continuous fun a : 𝔸ℚ =>
      InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace (a.1 Rat.infinitePlace) := by
    have h1 : Continuous fun a : 𝔸ℚ => a.1 Rat.infinitePlace :=
      (continuous_apply Rat.infinitePlace).comp continuous_fst
    have h2 : Continuous (InfinitePlace.Completion.ringEquivRealOfIsReal (K := ℚ) Rat.isReal_infinitePlace) :=
      (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).continuous
    exact h2.comp h1
  exact isOpen_Ioi.preimage hc

private def goodSet : Set ((𝔸ℚ)ˣ) :=
  {x | (x : 𝔸ℚ) ∈ integralSet ∧ (((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ) ∈ integralSet ∧ (x : 𝔸ℚ) ∈ congSet ∧ (x : 𝔸ℚ) ∈ posSet}

private theorem isOpen_goodSet : IsOpen goodSet :=
  (isOpen_integralSet.preimage Units.continuous_val).inter
    ((isOpen_integralSet.preimage Units.continuous_coe_inv).inter
      ((isOpen_congSet.preimage Units.continuous_val).inter (isOpen_posSet.preimage Units.continuous_val)))

private theorem one_mem_goodSet : (1 : (𝔸ℚ)ˣ) ∈ goodSet := by
  refine ⟨fun v => ?_, fun v => ?_, ?_, ?_⟩
  · rw [Units.val_one]; exact one_mem _
  · rw [inv_one, Units.val_one]; exact one_mem _
  · show Valued.v (((1 : (𝔸ℚ)ˣ) : 𝔸ℚ).2 v3 - 1) < 1
    rw [show ((1 : (𝔸ℚ)ˣ) : 𝔸ℚ).2 v3 = 1 from rfl, sub_self, map_zero]
    exact zero_lt_one
  · show 0 < archCoord 1
    rw [archCoord_one]
    exact one_pos

private theorem ρ_eq_one_of_mem_goodSet {x : (𝔸ℚ)ˣ} (hx : x ∈ goodSet) : ρ x = 1 := by
  obtain ⟨hint, hinv, -, hpos⟩ := hx
  refine ρ_eq_of_isNormalizer ⟨fun v => ?_, ?_⟩
  · rw [map_one]
    have h1 : Valued.v ((x : 𝔸ℚ).2 v) ≤ 1 := (mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp (hint v)
    have h2 : Valued.v ((((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v) ≤ 1 := (mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp (hinv v)
    have h3 := valued_snd_inv_mul x v
    apply le_antisymm h1
    calc (1 : ℤᵐ⁰) = Valued.v ((((x⁻¹ : (𝔸ℚ)ˣ)) : 𝔸ℚ).2 v) * Valued.v ((x : 𝔸ℚ).2 v) := h3.symm
      _ ≤ 1 * Valued.v ((x : 𝔸ℚ).2 v) := mul_le_mul_left h2 _
      _ = Valued.v ((x : 𝔸ℚ).2 v) := one_mul _
  · rw [Rat.cast_one, mul_one]
    exact hpos

private theorem chi3IdeleInt_eq_one_of_mem_goodSet {x : (𝔸ℚ)ˣ} (hx : x ∈ goodSet) : chi3IdeleInt x = 1 := by
  have hρ := ρ_eq_one_of_mem_goodSet hx
  have hcoord : ((unitInt3 x : v3.adicCompletionIntegers ℚ) : v3.adicCompletion ℚ) = (x : 𝔸ℚ).2 v3 := by
    show unitAt v3 x = _
    unfold unitAt
    rw [hρ, map_one, inv_one, mul_one]
  have hlt : Valued.v (((unitInt3 x : v3.adicCompletionIntegers ℚ) : v3.adicCompletion ℚ) - 1) < 1 := by
    rw [hcoord]
    exact hx.2.2.1
  rw [chi3IdeleInt_apply, res3_eq_one_of_valued_sub_one_lt hlt, psi3_one]

end Neighbourhood

section Continuity

private theorem isLocallyConstant_chi3IdeleInt : IsLocallyConstant (chi3IdeleInt : (𝔸ℚ)ˣ → ℤˣ) := by
  refine (IsLocallyConstant.iff_exists_open _).mpr fun x => ⟨{y | x⁻¹ * y ∈ goodSet}, ?_, ?_, ?_⟩
  · exact isOpen_goodSet.preimage (continuous_const_mul x⁻¹)
  · show x⁻¹ * x ∈ goodSet
    rw [inv_mul_cancel]
    exact one_mem_goodSet
  · intro y hy
    have h := chi3IdeleInt_eq_one_of_mem_goodSet hy
    rw [map_mul, map_inv, inv_mul_eq_one] at h
    exact h.symm

private theorem isLocallyConstant_chi3IdeleChar : IsLocallyConstant (chi3IdeleChar : (𝔸ℚ)ˣ → ℂˣ) :=
  isLocallyConstant_chi3IdeleInt.comp (Units.map (Int.castRingHom ℂ : ℤ →* ℂ))

private theorem continuous_chi3IdeleChar : Continuous chi3IdeleChar :=
  isLocallyConstant_chi3IdeleChar.continuous

private theorem isFiniteOrderHeckeChar_chi3IdeleChar : HeckeCharacter.IsFiniteOrderHeckeChar ℚ chi3IdeleChar :=
  isFiniteOrderHeckeChar_of_continuous continuous_chi3IdeleChar

end Continuity

section Bridges

private theorem isLocallyConstant_chi3IdeleChar_det :
    IsLocallyConstant (fun g : AdelicGL2 (𝓞 ℚ) ℚ => chi3IdeleChar (Matrix.GeneralLinearGroup.det g)) :=
  isLocallyConstant_chi3IdeleChar.comp_continuous Matrix.GeneralLinearGroup.continuous_det

private theorem isLocallyConstant_chiDet : IsLocallyConstant (chiDet (𝓞 ℚ) ℚ chi3IdeleChar) :=
  isLocallyConstant_chi3IdeleChar_det.comp _

private theorem continuous_chiDet : Continuous (chiDet (𝓞 ℚ) ℚ chi3IdeleChar) :=
  isLocallyConstant_chiDet.continuous

private def detKer : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ) := (chi3IdeleChar.comp Matrix.GeneralLinearGroup.det).ker

private theorem mem_detKer_iff (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    g ∈ detKer ↔ chi3IdeleChar (Matrix.GeneralLinearGroup.det g) = 1 := Iff.rfl

private theorem isOpen_detKer : IsOpen (detKer : Set (AdelicGL2 (𝓞 ℚ) ℚ)) :=
  isLocallyConstant_chi3IdeleChar_det.isOpen_fiber 1

private theorem isClosed_detKer : IsClosed (detKer : Set (AdelicGL2 (𝓞 ℚ) ℚ)) :=
  isLocallyConstant_chi3IdeleChar_det.isClosed_fiber 1

private theorem isKfSmooth_chiDet : IsKfSmooth ℚ (chiDet (𝓞 ℚ) ℚ chi3IdeleChar) := by
  rw [isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_exists_isOpen_subgroup]
  refine ⟨detKer.comap (finiteAdelicGL2Subgroup ℚ).subtype, isOpen_detKer.preimage continuous_subtype_val,
    fun u hu => ?_⟩
  refine FLT.SmoothVectors.RightTranslationFn.ext fun g => ?_
  rw [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul]
  show chiDet (𝓞 ℚ) ℚ chi3IdeleChar (g * (u : AdelicGL2 (𝓞 ℚ) ℚ)) = chiDet (𝓞 ℚ) ℚ chi3IdeleChar g
  have hu' : chi3IdeleChar (Matrix.GeneralLinearGroup.det (u : AdelicGL2 (𝓞 ℚ) ℚ)) = 1 := hu
  unfold chiDet
  rw [map_mul, map_mul, hu', mul_one]

private theorem measurable_chiDet :
    @Measurable _ _ (NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 ℚ) ℚ) _ (chiDet (𝓞 ℚ) ℚ chi3IdeleChar) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 ℚ) ℚ
  exact continuous_chiDet.measurable

end Bridges

section Refined

private def refine (U : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ) := U ⊓ detKer

private theorem refine_le (U : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)) : refine U ≤ U := inf_le_left

private theorem chi3IdeleChar_det_eq_one_of_mem_refine (U : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (u : AdelicGL2 (𝓞 ℚ) ℚ) (hu : u ∈ refine U) : chi3IdeleChar (Matrix.GeneralLinearGroup.det u) = 1 :=
  hu.2

private theorem isOpen_refine {U : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)} (hU : IsOpen (U : Set (AdelicGL2 (𝓞 ℚ) ℚ))) :
    IsOpen (refine U : Set (AdelicGL2 (𝓞 ℚ) ℚ)) :=
  hU.inter isOpen_detKer

private theorem isCompact_refine {U : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)} (hU : IsCompact (U : Set (AdelicGL2 (𝓞 ℚ) ℚ))) :
    IsCompact (refine U : Set (AdelicGL2 (𝓞 ℚ) ℚ)) :=
  hU.inter_right isClosed_detKer

private theorem isClosed_refine {U : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)} (hU : IsClosed (U : Set (AdelicGL2 (𝓞 ℚ) ℚ))) :
    IsClosed (refine U : Set (AdelicGL2 (𝓞 ℚ) ℚ)) :=
  hU.inter isClosed_detKer

private theorem sq_mem_refine {U : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ)} {u : AdelicGL2 (𝓞 ℚ) ℚ} (hu : u ∈ U) :
    u ^ 2 ∈ refine U := by
  refine ⟨U.pow_mem hu 2, ?_⟩
  show chi3IdeleChar (Matrix.GeneralLinearGroup.det (u ^ 2)) = 1
  rw [map_pow, map_pow, ← MonoidHom.pow_apply, chi3IdeleChar_sq, MonoidHom.one_apply]

end Refined

section Parity

private def archIdele (t : (InfiniteAdeleRing ℚ)ˣ) : (𝔸ℚ)ˣ :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing ℚ) 𝔸ℚf : InfiniteAdeleRing ℚ →* 𝔸ℚ) t

private theorem archIdele_fst (t : (InfiniteAdeleRing ℚ)ˣ) : ((archIdele t : (𝔸ℚ)ˣ) : 𝔸ℚ).1 = (t : InfiniteAdeleRing ℚ) :=
  rfl

private theorem archIdele_snd (t : (InfiniteAdeleRing ℚ)ˣ) : ((archIdele t : (𝔸ℚ)ˣ) : 𝔸ℚ).2 = 1 := rfl

private theorem ρ_archIdele_neg_one : ρ (archIdele (-1)) = -1 := by
  refine ρ_eq_of_isNormalizer ⟨fun v => ?_, ?_⟩
  · rw [archIdele_snd, Valuation.map_neg, map_one, show ((1 : 𝔸ℚf)) v = 1 from rfl, map_one]
  · show 0 < archCoord (archIdele (-1)) * (((-1 : ℚ)) : ℝ)
    unfold archCoord
    rw [archIdele_fst, Units.val_neg, Units.val_one, show ((-1 : InfiniteAdeleRing ℚ)) Rat.infinitePlace = -1
      from rfl, map_neg, map_one, Rat.cast_neg, Rat.cast_one]
    norm_num

private theorem chi3IdeleInt_archIdele_neg_one : chi3IdeleInt (archIdele (-1)) = -1 := by
  have h1 : unitInt3 (archIdele (-1)) = -1 := by
    refine Subtype.ext ?_
    show unitAt v3 _ = ((-1 : v3.adicCompletionIntegers ℚ) : v3.adicCompletion ℚ)
    unfold unitAt
    rw [ρ_archIdele_neg_one, archIdele_snd, show ((1 : 𝔸ℚf)) v3 = 1 from rfl, one_mul, map_neg, map_one,
      inv_neg, inv_one]
    rfl
  rw [chi3IdeleInt_apply, h1, map_neg, map_one]
  decide

private theorem chi3IdeleChar_archIdele_neg_one : ((chi3IdeleChar (archIdele (-1)) : ℂˣ) : ℂ) = -1 := by
  rw [chi3IdeleChar_apply, chi3IdeleInt_archIdele_neg_one]
  simp

end Parity

private theorem ne_v3_of_asIdeal_ne (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : v.asIdeal ≠ Ideal.span {(3 : 𝓞 ℚ)}) : v ≠ v3 := fun h => hv (h ▸ v3_asIdeal)

private theorem asIdeal_ne_of_ne_v3 {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v3) :
    w.asIdeal ≠ Ideal.span {(3 : 𝓞 ℚ)} := fun h =>
  hw (HeightOneSpectrum.ext (h.trans v3_asIdeal.symm))

private theorem absNorm_asIdeal (v : HeightOneSpectrum (𝓞 ℚ)) :
    Ideal.absNorm v.asIdeal = natGenerator v := by
  rw [asIdeal_eq_span_natGenerator, show ((natGenerator v : ℕ) : 𝓞 ℚ)
      = algebraMap ℤ (𝓞 ℚ) ((natGenerator v : ℕ) : ℤ) by push_cast; rfl,
    Ideal.absNorm_span_singleton, Algebra.norm_algebraMap,
    show Module.finrank ℤ (𝓞 ℚ) = 1 by
      rw [NumberField.RingOfIntegers.rank, Module.finrank_self],
    pow_one, Int.natAbs_natCast]

private theorem uniformizerIdele_eq_idealeAt (v : HeightOneSpectrum (𝓞 ℚ)) :
    AutomorphicForm.uniformizerIdele ℚ v = idealeAt v (NumberField.AdelicLevel.uniformizerUnit ℚ v) := rfl

private theorem solution_values (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : v.asIdeal ≠ Ideal.span {(3 : 𝓞 ℚ)}) :
    ((chi3IdeleChar (AutomorphicForm.uniformizerIdele ℚ v) : ℂˣ) : ℂ)
      = ((EisensteinWeightOne.chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℂ) := by
  have hvne : v ≠ v3 := ne_v3_of_asIdeal_ne v hv
  have hp : Nat.Prime (natGenerator v) := prime_natGenerator v
  set p : Nat.Primes := ⟨natGenerator v, hp⟩ with hpdef
  have hvp : v = ratPrime p := eq_ratPrime_of_natGenerator_eq rfl
  have hp3 : (p : ℕ) ≠ 3 := by
    intro h3
    apply hvne
    rw [hvp, show v3 = ratPrime p3 from rfl]
    exact congrArg ratPrime (Subtype.ext h3)
  have hval : ((chi3IdeleInt (idealeAt (ratPrime p) (NumberField.AdelicLevel.uniformizerUnit ℚ (ratPrime p))) : ℤˣ) : ℤ)
      = EisensteinWeightOne.chiNegThree (p : ℕ) :=
    chi3IdeleInt_idealeAt p hp3 _ (NumberField.AdelicLevel.valued_uniformizerUnit ℚ (ratPrime p))
  rw [uniformizerIdele_eq_idealeAt, chi3IdeleChar_apply, absNorm_asIdeal, hvp,
    natGenerator_ratPrime, hval]

private theorem solution_parity (u : (𝔸ℚ)ˣ)
    (h1 : (u : 𝔸ℚ).1 = -1) (h2 : (u : 𝔸ℚ).2 = 1) :
    ((chi3IdeleChar u : ℂˣ) : ℂ) = -1 := by
  have hu : u = archIdele (-1) := by
    refine Units.ext (Prod.ext ?_ ?_)
    · rw [h1, archIdele_fst]
      simp
    · rw [h2, archIdele_snd]
  rw [hu]
  exact chi3IdeleChar_archIdele_neg_one

private theorem solution_normalization (u : (𝔸ℚ)ˣ)
    (h1 : (u : 𝔸ℚ).1 = 1)
    (hoff : ∀ w : HeightOneSpectrum (𝓞 ℚ), w.asIdeal ≠ Ideal.span {(3 : 𝓞 ℚ)} → ((u : 𝔸ℚ).2 : 𝔸ℚf) w = 1)
    (hat : ∀ w : HeightOneSpectrum (𝓞 ℚ), w.asIdeal = Ideal.span {(3 : 𝓞 ℚ)} → ((u : 𝔸ℚ).2 : 𝔸ℚf) w = (3 : w.adicCompletion ℚ)) :
    ((chi3IdeleChar u : ℂˣ) : ℂ) = 1 := by
  have hu : u = idealeAt v3 (primeUnit p3) := by
    refine Units.ext (Prod.ext ?_ ?_)
    · rw [h1]
      rfl
    · apply IsDedekindDomain.FiniteAdeleRing.ext
      intro w
      by_cases hw : w = v3
      · subst hw
        rw [idealeAt_snd_self, hat v3 v3_asIdeal]
        show (3 : v3.adicCompletion ℚ) = algebraMap ℚ (v3.adicCompletion ℚ) ((3 : ℕ) : ℚ)
        push_cast
        rw [map_ofNat]
      · rw [idealeAt_snd_of_ne v3 (primeUnit p3) hw, hoff w (asIdeal_ne_of_ne_v3 hw)]
  have hval : chi3IdeleInt u = 1 := hu ▸ chi3IdeleInt_idealeAt_three
  rw [chi3IdeleChar_apply, hval]
  norm_num

end AutomorphicForm.IdeleChar

open AutomorphicForm.IdeleChar in
theorem solution :
    ∃ ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ,
      HeckeCharacter.IsFiniteOrderHeckeChar ℚ ω ∧
      HeckeCharacter.AdmitsModulus ℚ ω (Ideal.span {(3 : 𝓞 ℚ)}) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal ≠ Ideal.span {(3 : 𝓞 ℚ)} →
        ((ω (AutomorphicForm.uniformizerIdele ℚ v) : ℂˣ) : ℂ)
          = ((EisensteinWeightOne.chiNegThree (Ideal.absNorm v.asIdeal) : ℤ) : ℂ)) ∧
      (∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
        (u : AdeleRing (𝓞 ℚ) ℚ).1 = -1 → (u : AdeleRing (𝓞 ℚ) ℚ).2 = 1 →
        ((ω u : ℂˣ) : ℂ) = -1) ∧
      (∀ u : (AdeleRing (𝓞 ℚ) ℚ)ˣ,
        (u : AdeleRing (𝓞 ℚ) ℚ).1 = 1 →
        (∀ w : HeightOneSpectrum (𝓞 ℚ), w.asIdeal ≠ Ideal.span {(3 : 𝓞 ℚ)} →
          ((u : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ) w = 1) →
        (∀ w : HeightOneSpectrum (𝓞 ℚ), w.asIdeal = Ideal.span {(3 : 𝓞 ℚ)} →
          ((u : AdeleRing (𝓞 ℚ) ℚ).2 : FiniteAdeleRing (𝓞 ℚ) ℚ) w = (3 : w.adicCompletion ℚ)) →
        ((ω u : ℂˣ) : ℂ) = 1) :=
  ⟨chi3IdeleChar, isFiniteOrderHeckeChar_chi3IdeleChar,
   v3_asIdeal ▸ admitsModulus_chi3IdeleChar,
   solution_values, solution_parity, solution_normalization⟩

end

end S_AutomorphicForm_IdeleChar_exists_finiteOrderHeckeChar_chiNegThree
end P2MW
export P2MW.S_AutomorphicForm_IdeleChar_exists_finiteOrderHeckeChar_chiNegThree (solution)
