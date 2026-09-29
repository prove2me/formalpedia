-- Prove2me | solution 1 for AutomorphicForm.isInducedSection_mul_cpowChar_and_continuous_and_maximalCompactAway_of_isInducedSection_of_principalLevel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d2ec7aa1-4e06-5a7c-ac86-64d8224a6638

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isInducedSection_mul_cpowChar_and_continuous_and_maximalCompactAway_of_isInducedSection_of_principalLevel
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"

set_option autoImplicit false

noncomputable section

namespace TwistSection

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.TateGlobal
open IsDedekindDomain AutomorphicForm
open scoped NNReal

variable {K : Type} [Field K] [NumberField K]

private theorem _root_.TwistSection.exists_notMem_finset (K : Type) [Field K] [NumberField K] (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ T := by
  have hinj : ∀ p : Nat.Primes, ∃ v : HeightOneSpectrum (𝓞 K), v.asIdeal.under ℤ = Ideal.span {(p.1 : ℤ)} := by
    intro p
    haveI hpr : (Ideal.span {(p.1 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr (Nat.prime_iff_prime_int.mp p.2)
    have hp0 : Ideal.span {(p.1 : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero
    obtain ⟨⟨Q, hQ⟩⟩ := (inferInstance : Nonempty ((Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K)))
    exact ⟨⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver hp0 hQ⟩, hQ.2.over.symm⟩
  choose g hg using hinj
  have hginj : Function.Injective g := by
    intro p q hpq
    have h := hg p
    rw [hpq, hg q] at h
    have h' := Int.associated_iff_natAbs.mp (Ideal.span_singleton_eq_span_singleton.mp h)
    simp only [Int.natAbs_natCast] at h'
    exact Subtype.ext h'.symm
  haveI : Infinite (HeightOneSpectrum (𝓞 K)) := Infinite.of_injective g hginj
  exact Infinite.exists_notMem_finset T

p2m_export "TwistSection" "exists_notMem_finset"

theorem ne_bot_of_forall_dvd_mem {SK : Finset (HeightOneSpectrum (𝓞 K))} {N : Ideal (𝓞 K)}
    (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK) : N ≠ ⊥ := by
  rintro rfl
  obtain ⟨v, hv⟩ := exists_notMem_finset K SK
  exact hv (hN v ((Ideal.dvd_iff_le).mpr bot_le))

section Level

variable {SK : Finset (HeightOneSpectrum (𝓞 K))} {N : Ideal (𝓞 K)}

theorem isLevelOneMatrix_of_integral_of_eq_one (hNbot : N ≠ ⊥)
    (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    {m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hint : ∀ i j, m i j ∈ integralFiniteAdeles (𝓞 K) K)
    (hS : ∀ v ∈ SK, ∀ i j, m i j v = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j) :
    IsLevelOneMatrix (𝓞 K) K N m := by
  have hbd : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → idealBound (𝓞 K) N v = 1 := fun v hv =>
    idealBound_eq_one_of_not_dvd hNbot fun h => hv (hN v h)
  refine ⟨⟨hint, fun v => ?_⟩, fun v => ?_⟩
  · by_cases hv : v ∈ SK
    · rw [hS v hv 1 0, Matrix.one_apply_ne (by decide), map_zero]
      exact zero_le'
    · rw [hbd v hv]
      exact valued_apply_le_one (hint 1 0) v
  · by_cases hv : v ∈ SK
    · rw [coe_sub_apply, coe_one_apply, hS v hv 1 1, Matrix.one_apply_eq, sub_self, map_zero]
      exact zero_le'
    · rw [hbd v hv]
      exact valued_apply_le_one (sub_mem_integralFiniteAdeles (hint 1 1) one_mem_integralFiniteAdeles) v

theorem mem_finiteLevelOne_of_mem (hNbot : N ≠ ⊥)
    (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    {a : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)} (ha : a ∈ finiteIntegralGL2 (𝓞 K) K)
    (haS : ∀ v ∈ SK, finComponent (𝓞 K) K v a = 1) :
    a ∈ finiteLevelOne (𝓞 K) K N := by
  rw [mem_finiteIntegralGL2_iff] at ha
  have hS : ∀ v ∈ SK, ∀ i j, (a : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j v =
      (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
    intro v hv i j
    rw [← finComponent_apply, haS v hv, Units.val_one]
  have hS' : ∀ v ∈ SK, ∀ i j, ((a⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j v = (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j := by
    intro v hv i j
    rw [← finComponent_apply, map_inv, haS v hv, inv_one, Units.val_one]
  exact ⟨isLevelOneMatrix_of_integral_of_eq_one hNbot hN ha.1 hS,
    isLevelOneMatrix_of_integral_of_eq_one hNbot hN ha.2 hS'⟩

theorem glFin_weyl_mem_finiteIntegralGL2 :
    glFin (𝓞 K) K (weyl (𝓞 K) K) ∈ finiteIntegralGL2 (𝓞 K) K := by
  rw [mem_finiteIntegralGL2_iff]
  have hw : ∀ i j : Fin 2,
      ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 ∈ integralFiniteAdeles (𝓞 K) K := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact zero_mem_integralFiniteAdeles
    · exact one_mem_integralFiniteAdeles
    · exact one_mem_integralFiniteAdeles
    · exact zero_mem_integralFiniteAdeles
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [glFin_apply]
    exact hw i j
  · rw [← map_inv, glFin_apply]
    exact hw i j

theorem mem_principalLevel_inf (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ maximalCompactAway K SK) :
    k ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K := by
  have hNbot : N ≠ ⊥ := ne_bot_of_forall_dvd_mem hN
  rw [mem_maximalCompactAway_iff] at hk
  obtain ⟨hk1, hk2, hk3⟩ := hk

  have h1 : k ∈ levelOne (𝓞 K) K N := by
    rw [mem_levelOne_iff]
    exact mem_finiteLevelOne_of_mem hNbot hN hk1.1 hk3

  have h2 : k ∈ (levelOne (𝓞 K) K N).map (MulAut.conj (weyl (𝓞 K) K)).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨(weyl (𝓞 K) K)⁻¹ * k * weyl (𝓞 K) K, ?_, ?_⟩
    · rw [mem_levelOne_iff, map_mul, map_mul, map_inv]
      refine mem_finiteLevelOne_of_mem hNbot hN ?_ fun v hv => ?_
      · exact mul_mem (mul_mem (inv_mem glFin_weyl_mem_finiteIntegralGL2) hk1.1)
          glFin_weyl_mem_finiteIntegralGL2
      · rw [map_mul, map_mul, map_inv, hk3 v hv, mul_one, inv_mul_cancel]
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

  have h3 : k ∈ finiteAdelicGL2Subgroup K := by
    rw [mem_finiteAdelicGL2Subgroup_iff]
    exact hk2
  exact Subgroup.mem_inf.mpr ⟨(mem_principalLevel_iff (𝓞 K) K N).mpr ⟨h1, h2⟩, h3⟩

end Level

def piArch (K : Type) [Field K] [NumberField K] (w : InfinitePlace K) : AdeleRing (𝓞 K) K →+* w.Completion :=
  (archEval K w).comp (adeleArch (𝓞 K) K)

def piFin (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    AdeleRing (𝓞 K) K →+* v.adicCompletion K :=
  (finAdeleEval (𝓞 K) K v).comp (adeleFin (𝓞 K) K)

theorem piArch_apply (w : InfinitePlace K) (x : AdeleRing (𝓞 K) K) : piArch K w x = x.1 w := rfl

theorem piFin_apply (v : HeightOneSpectrum (𝓞 K)) (x : AdeleRing (𝓞 K) K) : piFin K v x = x.2 v := rfl

theorem map_piArch (w : InfinitePlace K) (k : AdelicGL2 (𝓞 K) K) :
    (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).map (piArch K w) =
      (archComponent K w (glArch (𝓞 K) K k) : Matrix (Fin 2) (Fin 2) w.Completion) := by
  ext i j
  rfl

theorem map_piFin (v : HeightOneSpectrum (𝓞 K)) (k : AdelicGL2 (𝓞 K) K) :
    (k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).map (piFin K v) =
      (finComponent (𝓞 K) K v (glFin (𝓞 K) K k) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
  ext i j
  rfl

theorem det_fst_apply_eq_one {k : AdelicGL2 (𝓞 K) K} (hk : glArch (𝓞 K) K k = 1) (w : InfinitePlace K) :
    ((Matrix.GeneralLinearGroup.det k : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, ← piArch_apply, RingHom.map_det, RingHom.mapMatrix_apply,
    map_piArch, hk, map_one, Units.val_one, Matrix.det_one]

theorem norm_det_snd_apply_eq_one {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K)
    (v : HeightOneSpectrum (𝓞 K)) :
    ‖((Matrix.GeneralLinearGroup.det k : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v‖ = 1 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, ← piFin_apply, RingHom.map_det, RingHom.mapMatrix_apply,
    map_piFin, NumberField.FinitePlace.norm_def, valued_det_finComponent_eq_one hk v, map_one, NNReal.coe_one]

theorem ideleNorm_det_eq_one {SK : Finset (HeightOneSpectrum (𝓞 K))} {k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ maximalCompactAway K SK) :
    ideleNorm K (Matrix.GeneralLinearGroup.det k) = 1 := by
  rw [mem_maximalCompactAway_iff] at hk
  obtain ⟨hk1, hk2, -⟩ := hk
  show ((distribHaarChar (AdeleRing (𝓞 K) K) (Matrix.GeneralLinearGroup.det k) : ℝ≥0) : ℝ) = 1
  rw [NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm K]
  have h1 : ∏ w : InfinitePlace K,
      ‖((Matrix.GeneralLinearGroup.det k : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w‖ ^ w.mult = 1 := by
    refine Finset.prod_eq_one fun w _ => ?_
    rw [det_fst_apply_eq_one hk2 w, norm_one, one_pow]
  have h2 : ∏ᶠ u : HeightOneSpectrum (𝓞 K),
      ‖((Matrix.GeneralLinearGroup.det k : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 u‖ = 1 :=
    finprod_eq_one_of_forall_eq_one fun u => norm_det_snd_apply_eq_one hk1 u
  rw [h1, h2, one_mul]

theorem etaFst_mul (μ c : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing (𝓞 K) K)ˣ) :
    etaFst (μ * c) α hα s x = etaFst μ α hα s x * c x := by
  rw [etaFst_apply, etaFst_apply, MonoidHom.mul_apply, mul_right_comm]

theorem etaSnd_mul (ν c : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ)
    (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ) (x : (AdeleRing (𝓞 K) K)ˣ) :
    etaSnd (ν * c) α hα s x = etaSnd ν α hα s x * c x := by
  rw [etaSnd_apply, etaSnd_apply, MonoidHom.mul_apply, mul_right_comm]

end TwistSection

end

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open NumberField.TateGlobal AutomorphicForm TwistSection
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (w : ℝ) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ)
      (φ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ)
      (_hφlev : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g),
    IsInducedSection (𝓞 K) K
        (etaFst (μ * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) αm hαm s)
        (etaSnd (ν * cpowChar αm hαm (((w / 2 : ℝ) : ℂ))) αm hαm s)
        (fun g : AdelicGL2 (𝓞 K) K => φ g *
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) ∧
      Continuous (fun g : AdelicGL2 (𝓞 K) K => φ g *
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) ∧
      ∀ k ∈ AutomorphicForm.maximalCompactAway K SK, ∀ g : AdelicGL2 (𝓞 K) K,
        (fun g : AdelicGL2 (𝓞 K) K => φ g *
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) (g * k) =
        (fun g : AdelicGL2 (𝓞 K) K => φ g *
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) g := by
  intro αm hαm μ ν s φ hφ hφc hφlev

  have hαI : ∀ x : (AdeleRing (𝓞 K) K)ˣ, ((αm x : ℝˣ) : ℝ) = ideleNorm K x := fun _ => rfl
  set c : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := cpowChar αm hαm (((w / 2 : ℝ) : ℂ)) with hc_def
  have hc : ∀ x : (AdeleRing (𝓞 K) K)ˣ, ((c x : ℂˣ) : ℂ) = ((ideleNorm K x ^ (w / 2) : ℝ) : ℂ) := by
    intro x
    rw [hc_def, cpowChar_apply_val, hαI x, Complex.ofReal_cpow (ideleNorm_pos x).le]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro b hb g
    set b₁ : (AdeleRing (𝓞 K) K)ˣ := borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K)) with hb₁
    set b₂ : (AdeleRing (𝓞 K) K)ˣ := borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K)) with hb₂
    have hdet : Matrix.GeneralLinearGroup.det (b * g) = b₁ * b₂ * Matrix.GeneralLinearGroup.det g := by
      rw [map_mul, det_borel_eq_diag_mul hb]
    show φ (b * g) * ((ideleNorm K (Matrix.GeneralLinearGroup.det (b * g)) ^ (w / 2) : ℝ) : ℂ) =
      ((etaFst (μ * c) αm hαm s b₁ : ℂˣ) : ℂ) * ((etaSnd (ν * c) αm hαm s b₂ : ℂˣ) : ℂ) *
        (φ g * ((ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w / 2) : ℝ) : ℂ))
    rw [hφ b hb g, hdet, ideleNorm_mul, ideleNorm_mul,
      Real.mul_rpow (mul_pos (ideleNorm_pos _) (ideleNorm_pos _)).le (ideleNorm_pos _).le,
      Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le,
      Complex.ofReal_mul, Complex.ofReal_mul, etaFst_mul, etaSnd_mul, Units.val_mul, Units.val_mul, hc, hc]
    ring
  ·
    exact hφc.mul (Complex.continuous_ofReal.comp
      ((NumberField.TateGlobal.continuous_ideleNorm_det K).rpow_const fun g => Or.inl (ideleNorm_pos _).ne'))
  ·
    intro k hk g
    show φ (g * k) * ((ideleNorm K (Matrix.GeneralLinearGroup.det (g * k)) ^ (w / 2) : ℝ) : ℂ) =
      φ g * ((ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w / 2) : ℝ) : ℂ)
    rw [hφlev g k (mem_principalLevel_inf hN hk), map_mul, ideleNorm_mul, ideleNorm_det_eq_one hk, mul_one]

end S_AutomorphicForm_isInducedSection_mul_cpowChar_and_continuous_and_maximalCompactAway_of_isInducedSection_of_principalLevel
end P2MW
export P2MW.S_AutomorphicForm_isInducedSection_mul_cpowChar_and_continuous_and_maximalCompactAway_of_isInducedSection_of_principalLevel (solution)
