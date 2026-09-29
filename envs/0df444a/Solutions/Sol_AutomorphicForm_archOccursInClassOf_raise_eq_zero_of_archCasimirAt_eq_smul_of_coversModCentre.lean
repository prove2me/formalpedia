-- Prove2me | solution 1 for AutomorphicForm.archOccursInClassOf_raise_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/17ebaf10-c6fb-59af-aec3-7f9c60766efb

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt
import Theorems.Thm_AutomorphicForm_iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_archOccursInClassOf_raise_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

section RPOS_main

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped ComplexConjugate Pointwise

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws49
namespace RPOS

scoped instance : Finite ArchDir :=
  Finite.of_injective (fun d : ArchDir => (match d with | .H => 0 | .E => 1 | .Fm => 2 : Fin 3))
    (by intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide))

theorem ideleNorm_mul' (F : Type) [Field F] [NumberField F] (a b : (AdeleRing (𝓞 F) F)ˣ) :
    ideleNorm F (a * b) = ideleNorm F a * ideleNorm F b := by
  simp [NumberField.TateGlobal.ideleNorm, map_mul, NNReal.coe_mul]

theorem exists_measurableSet_isFundamentalDomain (F : Type) [Field F] [NumberField F] (e₁ e₂ : ℝ) :
    ∃ 𝓕 : Set (AdelicGL2 (𝓞 F) F), MeasurableSet 𝓕 ∧
      𝓕 ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂} ∧
      IsFundamentalDomain (globalPoints (𝓞 F) F).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
          {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂}) := by
  obtain ⟨S, hSsub, hS⟩ :=
    AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc F e₁ e₂
  set slab : Set (AdelicGL2 (𝓞 F) F) :=
    {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂} with hslab
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  have hslabm : MeasurableSet slab := NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F e₁ e₂
  obtain ⟨t₀, hSt₀, ht₀m, ht₀ae⟩ := hS.nullMeasurableSet.exists_measurable_superset_ae_eq
  have hSt : S ⊆ t₀ ∩ slab := Set.subset_inter hSt₀ hSsub
  have hdiff : μ.restrict slab ((t₀ ∩ slab) \ S) = 0 :=
    measure_mono_null (Set.diff_subset_diff_left Set.inter_subset_left) (ae_le_set.1 ht₀ae.le)
  haveI := NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

  have hqi : ∀ (γ : (globalPoints (𝓞 F) F).range) (N : Set (AdelicGL2 (𝓞 F) F)),
      μ.restrict slab N = 0 → μ.restrict slab (γ • N) = 0 := by
    rintro ⟨γ', γ, rfl⟩ N hN
    have hsm : ((⟨globalPoints (𝓞 F) F γ, γ, rfl⟩ : (globalPoints (𝓞 F) F).range) • N) =
        (globalPoints (𝓞 F) F γ) • N := rfl
    rw [hsm]
    rw [Measure.restrict_apply' hslabm] at hN ⊢
    have hsub : globalPoints (𝓞 F) F γ • N ∩ slab ⊆ globalPoints (𝓞 F) F γ • (N ∩ slab) := by
      rintro x ⟨⟨n, hn, rfl⟩, hx⟩
      refine ⟨n, ⟨hn, ?_⟩, rfl⟩
      simp only [hslab, Set.mem_setOf_eq, smul_eq_mul, map_mul, ideleNorm_mul',
        AutomorphicForm.ideleNorm_det_globalPoints, one_mul] at hx ⊢
      exact hx
    refine measure_mono_null hsub ?_
    rw [measure_smul]
    exact hN
  refine ⟨t₀ ∩ slab, ht₀m.inter hslabm, Set.inter_subset_right, ?_, ?_, ?_⟩
  · exact (ht₀m.inter hslabm).nullMeasurableSet
  · filter_upwards [hS.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    exact ⟨g, hSt hg⟩
  · intro g₁ g₂ hne
    have h0 : μ.restrict slab (g₁ • S ∩ g₂ • S) = 0 := hS.aedisjoint hne
    have hdec : ∀ g : (globalPoints (𝓞 F) F).range,
        g • (t₀ ∩ slab) ⊆ g • S ∪ g • ((t₀ ∩ slab) \ S) := by
      intro g
      rw [← Set.smul_set_union, Set.union_diff_cancel hSt]
    change μ.restrict slab (g₁ • (t₀ ∩ slab) ∩ g₂ • (t₀ ∩ slab)) = 0
    refine measure_mono_null (Set.inter_subset_inter (hdec g₁) (hdec g₂)) ?_
    refine measure_mono_null (fun x hx => ?_)
      (measure_union_null (measure_union_null h0 (hqi g₁ _ hdiff)) (hqi g₂ _ hdiff))
    rcases hx with ⟨h1 | h1, h2 | h2⟩
    · exact Or.inl (Or.inl ⟨h1, h2⟩)
    · exact Or.inr h2
    · exact Or.inl (Or.inr h1)
    · exact Or.inr h2

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

theorem archDerivAt_sub' {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsArchSmoothAt hw φ) (hψ : IsArchSmoothAt hw ψ) (d : ArchDir) :
    archDerivAt hw d (φ - ψ) = archDerivAt hw d φ - archDerivAt hw d ψ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ ψ, archDerivAt_add hφ (hψ.smul _) d, archDerivAt_smul,
    neg_one_smul, ← sub_eq_add_neg]

theorem archDerivAt_left_inv {φ : AdelicGL2 (𝓞 F) F → ℂ} {h : AdelicGL2 (𝓞 F) F}
    (hφ : ∀ g, φ (h * g) = φ g) (d : ArchDir) (g : AdelicGL2 (𝓞 F) F) :
    archDerivAt hw d φ (h * g) = archDerivAt hw d φ g := by
  have hfun : (fun g => φ (h * g)) = φ := funext hφ
  have h1 := archDerivAt_comp_mul_left hw d φ h
  rw [hfun] at h1
  exact (congrFun h1 g).symm

theorem norm_comb_le {a b c : ℂ} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : ‖c‖ ≤ M) :
    ‖a + Complex.I * (b + c)‖ ≤ 3 * M := by
  calc ‖a + Complex.I * (b + c)‖ ≤ ‖a‖ + ‖Complex.I * (b + c)‖ := norm_add_le _ _
    _ ≤ ‖a‖ + (‖b‖ + ‖c‖) := by
        rw [norm_mul, Complex.norm_I, one_mul]; linarith [norm_add_le b c]
    _ ≤ 3 * M := by linarith

theorem raise_eq_zero (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hG : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (k : ℤ)
    (htype : HasArchCharacterAt₀ F w ((archWeightCharℝ k).comp
      (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ)
    (hsm : IsArchSmoothAt hw φ)
    (hreg : ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) φ) ∧
      ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
          ‖l.foldr (archDerivAt hw) φ g‖ ≤ B)
    (hcas : archCasimirAt hw φ = ((-(k : ℂ) / 2) * (1 + (k : ℂ) / 2)) • φ) :
    archDerivAt hw .H φ + Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0 := by

  have hW : archDerivAt hw .E φ - archDerivAt hw .Fm φ = (Complex.I * k) • φ :=
    AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt F w hw k φ hsm htype
  have hRL := (AutomorphicForm.iterate_raise_iterate_lower_eq_smul_of_archCasimirAt_eq_smul F w hw φ hsm
    (Complex.I * k) _ hW hcas).2.2.2 1
  simp only [Function.iterate_one, Finset.prod_range_one, Nat.cast_zero, mul_zero, add_zero] at hRL
  have hc0 : (-4 * (-(k : ℂ) / 2 * (1 + (k : ℂ) / 2)) + (Complex.I * (k : ℂ)) ^ 2
      + 2 * Complex.I * (Complex.I * (k : ℂ))) = 0 := by
    linear_combination ((k : ℂ) ^ 2 + 2 * (k : ℂ)) * Complex.I_sq
  rw [hc0, zero_smul] at hRL
  set L := archDerivAt hw .H φ + Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) with hLdef

  have hLsm : IsArchSmoothAt hw L :=
    (hsm.archDerivAt _).add (((hsm.archDerivAt _).add (hsm.archDerivAt _)).smul _)
  have hDL : ∀ d, archDerivAt hw d L = archDerivAt hw d (archDerivAt hw .H φ) +
      Complex.I • (archDerivAt hw d (archDerivAt hw .E φ) + archDerivAt hw d (archDerivAt hw .Fm φ)) := by
    intro d
    rw [hLdef, archDerivAt_add (hsm.archDerivAt _) (((hsm.archDerivAt _).add (hsm.archDerivAt _)).smul _),
      archDerivAt_smul, archDerivAt_add (hsm.archDerivAt _) (hsm.archDerivAt _)]
  have hDDL : ∀ d d', archDerivAt hw d (archDerivAt hw d' L) =
      archDerivAt hw d (archDerivAt hw d' (archDerivAt hw .H φ)) +
      Complex.I • (archDerivAt hw d (archDerivAt hw d' (archDerivAt hw .E φ)) +
        archDerivAt hw d (archDerivAt hw d' (archDerivAt hw .Fm φ))) := by
    intro d d'
    rw [hDL d', archDerivAt_add ((hsm.archDerivAt _).archDerivAt _)
      ((((hsm.archDerivAt _).archDerivAt _).add ((hsm.archDerivAt _).archDerivAt _)).smul _),
      archDerivAt_smul, archDerivAt_add ((hsm.archDerivAt _).archDerivAt _) ((hsm.archDerivAt _).archDerivAt _)]
  have hφc : Continuous φ := (hreg []).1
  have hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d φ) := fun d => (hreg [d]).1
  have hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' φ)) := fun d d' => (hreg [d, d']).1
  have hD3 : ∀ d d' d'' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' (archDerivAt hw d'' φ))) :=
    fun d d' d'' => (hreg [d, d', d'']).1
  have hLc : Continuous L := (hD1 .H).add (((hD1 .E).add (hD1 .Fm)).const_smul Complex.I)
  have hD1' : ∀ d : ArchDir, Continuous (archDerivAt hw d L) := fun d => by
    rw [hDL d]; exact (hD2 d .H).add (((hD2 d .E).add (hD2 d .Fm)).const_smul Complex.I)
  have hD2' : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' L)) := fun d d' => by
    rw [hDDL d d']; exact (hD3 d d' .H).add (((hD3 d d' .E).add (hD3 d d' .Fm)).const_smul Complex.I)
  have hLG : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), L (globalPoints (𝓞 F) F γ * g) = L g := by
    intro γ g
    have h1 := fun d => archDerivAt_left_inv hw (hG γ) d g
    show archDerivAt hw .H φ _ + Complex.I * (archDerivAt hw .E φ _ + archDerivAt hw .Fm φ _) =
      archDerivAt hw .H φ g + Complex.I * (archDerivAt hw .E φ g + archDerivAt hw .Fm φ g)
    rw [h1, h1, h1]

  by_contra hne
  obtain ⟨g₀, hg₀⟩ : ∃ g, L g ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  set r := ideleNorm F (Matrix.GeneralLinearGroup.det g₀) with hr
  have hrpos : 0 < r := ideleNorm_pos _
  have he₁ : (0 : ℝ) < r / 2 := by positivity
  have he : r / 2 < 2 * r := by linarith
  obtain ⟨𝓕, h𝓕m, h𝓕s, h𝓕⟩ := exists_measurableSet_isFundamentalDomain F (r / 2) (2 * r)

  choose Bf hBf using fun l : List ArchDir => (hreg l).2 (r / 2) (2 * r) he₁ he
  have hfinL : Set.Finite {l : List ArchDir | l.length ≤ 3} := List.finite_length_le ArchDir 3
  have hBs : ∀ l : List ArchDir, l.length ≤ 3 → ∀ g : AdelicGL2 (𝓞 F) F,
      ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (r / 2) (2 * r) →
        ‖l.foldr (archDerivAt hw) φ g‖ ≤ ∑ l ∈ hfinL.toFinset, |Bf l| := by
    intro l hl g hg
    calc ‖l.foldr (archDerivAt hw) φ g‖ ≤ Bf l := hBf l g hg
      _ ≤ |Bf l| := le_abs_self _
      _ ≤ ∑ l ∈ hfinL.toFinset, |Bf l| :=
        Finset.single_le_sum (f := fun l => |Bf l|) (fun _ _ => abs_nonneg _) (hfinL.mem_toFinset.2 hl)
  set Bs : ℝ := ∑ l ∈ hfinL.toFinset, |Bf l| with hBsdef
  have hBs0 : 0 ≤ Bs := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hBsB : Bs ≤ 3 * Bs := by linarith
  have hB : ∀ g : AdelicGL2 (𝓞 F) F, ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc (r / 2) (2 * r) →
      ‖φ g‖ ≤ 3 * Bs ∧ ‖L g‖ ≤ 3 * Bs ∧
      (∀ d : ArchDir, ‖archDerivAt hw d φ g‖ ≤ 3 * Bs ∧ ‖archDerivAt hw d L g‖ ≤ 3 * Bs) ∧
      (∀ d d' : ArchDir, ‖archDerivAt hw d (archDerivAt hw d' φ) g‖ ≤ 3 * Bs ∧
        ‖archDerivAt hw d (archDerivAt hw d' L) g‖ ≤ 3 * Bs) := by
    intro g hg
    have h0 : ∀ l : List ArchDir, l.length ≤ 3 → ‖l.foldr (archDerivAt hw) φ g‖ ≤ Bs := fun l hl => hBs l hl g hg
    refine ⟨(h0 [] (by simp)).trans hBsB, ?_, fun d => ⟨(h0 [d] (by simp)).trans hBsB, ?_⟩,
      fun d d' => ⟨(h0 [d, d'] (by simp)).trans hBsB, ?_⟩⟩
    · exact norm_comb_le (h0 [.H] (by simp)) (h0 [.E] (by simp)) (h0 [.Fm] (by simp))
    · rw [hDL d]
      exact norm_comb_le (h0 [d, .H] (by simp)) (h0 [d, .E] (by simp)) (h0 [d, .Fm] (by simp))
    · rw [hDDL d d']
      exact norm_comb_le (h0 [d, d', .H] (by simp)) (h0 [d, d', .E] (by simp)) (h0 [d, d', .Fm] (by simp))

  have h47 := AutomorphicForm.setIntegral_archCasimirAt_mul_conj_eq_and_lower_adjoint_of_isFundamentalDomain
    F w hw (r / 2) (2 * r) he₁ he 𝓕 h𝓕m h𝓕s h𝓕 φ L hG hLG hφc hLc hsm hLsm hD1 hD1' hD2 hD2' (3 * Bs) hB
  obtain ⟨-, -, h2⟩ := h47
  dsimp only at h2
  rw [← hLdef, hRL] at h2
  simp only [Pi.zero_apply, map_zero, mul_zero, integral_zero, neg_zero] at h2

  have hfin : adelicGLHaar (Fin 2) (𝓞 F) F 𝓕 < ⊤ := by
    have h6 := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
      F (r / 2) (2 * r) he₁ he 𝓕 h𝓕
    rwa [Set.inter_eq_left.2 h𝓕s] at h6
  have hint : IntegrableOn (fun g => ‖L g‖ ^ 2 * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-(0 : ℝ))) 𝓕
      (adelicGLHaar (Fin 2) (𝓞 F) F) := by
    simp only [neg_zero, Real.rpow_zero, mul_one]
    refine Measure.integrableOn_of_bounded (M := (3 * Bs) ^ 2) hfin.ne
      ((hLc.norm.pow 2).aestronglyMeasurable) ?_
    rw [ae_restrict_iff' h𝓕m]
    refine Filter.Eventually.of_forall fun g hg => ?_
    have h1 : ‖L g‖ ≤ 3 * Bs := (hB g (h𝓕s hg)).2.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h109 := AutomorphicForm.peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous
    F 0 (r / 2) (2 * r) he₁ he 𝓕 h𝓕m h𝓕s h𝓕 L hLc hLG ⟨g₀, ⟨by linarith, by linarith⟩, hg₀⟩ hint
  apply h109
  unfold AutomorphicForm.peterssonIntegral
  simp only [neg_zero, Real.rpow_zero, Complex.ofReal_one, mul_one]
  exact h2

theorem main (D : Set (AdelicGL2 (𝓞 F) F)) (Θ : HeckeEigensystem F ℂ) (k : ℤ)
    (P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop)
    (h : ArchOccursInClassOf F D Θ
          (fun φ => P φ ∧ HasArchCharacterAt₀ F w ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧
            (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) φ) ∧
              ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
                NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
                  ‖l.foldr (archDerivAt hw) φ g‖ ≤ B) ∧
            archCasimirAt hw φ = ((-(k : ℂ) / 2) * (1 + (k : ℂ) / 2)) • φ)) :
    ArchOccursInClassOf F D Θ
      (fun φ => P φ ∧ archDerivAt hw .H φ + Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0) := by
  obtain ⟨Θ', hΘ', R', hR', hP, htype, hsm, hreg, hcas⟩ := h
  exact ⟨Θ', hΘ', R', hR', hP, raise_eq_zero hw R'.toFun R'.left_invariant k htype hsm hreg hcas⟩

end Ws49.RPOS
p2m_reactivate "P2MW.S_AutomorphicForm_archOccursInClassOf_raise_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre.Ws49 P2MW.S_AutomorphicForm_archOccursInClassOf_raise_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre.Ws49.RPOS"
p2m_reactivate "P2MW.S_AutomorphicForm_archOccursInClassOf_raise_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre.Ws49"

end RPOS_main
p2m_reactivate "P2MW.S_AutomorphicForm_archOccursInClassOf_raise_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre.Ws49 P2MW.S_AutomorphicForm_archOccursInClassOf_raise_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre.Ws49.RPOS"

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion in

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal) :
    ∀ (k : ℤ) (P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop),
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => P φ ∧ HasArchCharacterAt₀ F w ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧
            (∀ l : List ArchDir, Continuous (l.foldr (archDerivAt hw) φ) ∧
              ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 F) F,
                NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
                  ‖l.foldr (archDerivAt hw) φ g‖ ≤ B) ∧
            archCasimirAt hw φ = ((-(k : ℂ) / 2) * (1 + (k : ℂ) / 2)) • φ) →
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
          (fun φ => P φ ∧
            archDerivAt hw .H φ + Complex.I • (archDerivAt hw .E φ + archDerivAt hw .Fm φ) = 0) :=
  fun k P h => Ws49.RPOS.main hw _ Θ k P h

end S_AutomorphicForm_archOccursInClassOf_raise_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_archOccursInClassOf_raise_eq_zero_of_archCasimirAt_eq_smul_of_coversModCentre (solution)
