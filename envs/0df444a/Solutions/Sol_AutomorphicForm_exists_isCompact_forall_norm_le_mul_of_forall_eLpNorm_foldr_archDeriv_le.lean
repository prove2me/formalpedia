-- Prove2me | solution 1 for AutomorphicForm.exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/965d73e0-953c-5ff0-bb7b-9d678a03e7cc

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar

import Theorems.Thm_AutomorphicForm_foldr_archDeriv_mul_eq_of_forall_mul_eq
import Theorems.Thm_AutomorphicForm_exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq
import Theorems.Thm_AutomorphicForm_exists_forall_contDiff_norm_iteratedFDeriv_comp_flowChart_le_sum_foldr_archDeriv
import Theorems.Thm_Sobolev_exists_forall_norm_le_mul_sum_sqrt_integral_norm_iteratedFDeriv_sq_of_contDiff_box
import Theorems.Thm_AutomorphicForm_continuous_archFlowAt_and_continuous_archFlowAtComplex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv"
p2m_attr_erase "simp" "RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped Classical

noncomputable section

namespace SN2Reduce

variable (K : Type) [Field K] [NumberField K]

abbrev Letter : Type :=
  (Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕ (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)

def realBlock (w : {w : InfinitePlace K // w.IsReal}) : List (Letter K) :=
  [Sum.inl ⟨w.1, w.2, ArchDir.H⟩, Sum.inl ⟨w.1, w.2, ArchDir.E⟩, Sum.inl ⟨w.1, w.2, ArchDir.Fm⟩]

def complexBlock (w : {w : InfinitePlace K // w.IsComplex}) : List (Letter K) :=
  [Sum.inr ⟨w.1, w.2, ArchDirComplex.H⟩, Sum.inr ⟨w.1, w.2, ArchDirComplex.E⟩, Sum.inr ⟨w.1, w.2, ArchDirComplex.Fm⟩,
   Sum.inr ⟨w.1, w.2, ArchDirComplex.iH⟩, Sum.inr ⟨w.1, w.2, ArchDirComplex.iE⟩, Sum.inr ⟨w.1, w.2, ArchDirComplex.iFm⟩]

def letters : List (Letter K) :=
  ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).toList.flatMap (realBlock K)) ++
    ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).toList.flatMap (complexBlock K))

def Letter.place : Letter K → InfinitePlace K := fun d => Sum.elim (fun d => d.1) (fun d => d.1) d

theorem length_realBlock (w : {w : InfinitePlace K // w.IsReal}) : (realBlock K w).length = 3 := rfl

theorem length_complexBlock (w : {w : InfinitePlace K // w.IsComplex}) : (complexBlock K w).length = 6 := rfl

theorem length_letters : (letters K).length = 3 * nrRealPlaces K + 6 * nrComplexPlaces K := by
  rw [letters, List.length_append, List.length_flatMap, List.length_flatMap]
  have h1 : (Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).toList.map (fun a => (realBlock K a).length) =
      (Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).toList.map (fun _ => 3) :=
    List.map_congr_left fun w _ => length_realBlock K w
  have h2 : (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).toList.map (fun a => (complexBlock K a).length) =
      (Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).toList.map (fun _ => 6) :=
    List.map_congr_left fun w _ => length_complexBlock K w
  show ((Finset.univ : Finset {w : InfinitePlace K // w.IsReal}).toList.map (fun a => (realBlock K a).length)).sum +
      ((Finset.univ : Finset {w : InfinitePlace K // w.IsComplex}).toList.map (fun a => (complexBlock K a).length)).sum = _
  rw [h1, h2, List.map_const', List.map_const', List.sum_replicate, List.sum_replicate, Finset.length_toList,
    Finset.length_toList, Finset.card_univ, Finset.card_univ, smul_eq_mul, smul_eq_mul, nrRealPlaces, nrComplexPlaces]
  ring

theorem length_letters_le : (letters K).length ≤ 4 * nrRealPlaces K + 8 * nrComplexPlaces K := by
  rw [length_letters]; omega

theorem mem_letters (d : Letter K) : d ∈ letters K := by
  classical
  rcases d with ⟨w, hw, dir⟩ | ⟨w, hw, dir⟩
  · refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨⟨w, hw⟩, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩)
    cases dir
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨⟨w, hw⟩, Finset.mem_toList.mpr (Finset.mem_univ _), ?_⟩)
    cases dir
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))))

theorem place_of_mem_realBlock {w : {w : InfinitePlace K // w.IsReal}} {d : Letter K} (h : d ∈ realBlock K w) :
    Letter.place K d = w.1 ∧ d.isLeft = true := by
  simp only [realBlock, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

theorem place_of_mem_complexBlock {w : {w : InfinitePlace K // w.IsComplex}} {d : Letter K} (h : d ∈ complexBlock K w) :
    Letter.place K d = w.1 ∧ d.isLeft = false := by
  simp only [complexBlock, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl⟩

def Letter.code : Letter K → ℕ := fun d =>
  Sum.elim (fun d => match d.2.2 with | .H => 0 | .E => 1 | .Fm => 2)
    (fun d => match d.2.2 with | .H => 0 | .E => 1 | .Fm => 2 | .iH => 3 | .iE => 4 | .iFm => 5) d

theorem nodup_realBlock (w : {w : InfinitePlace K // w.IsReal}) : (realBlock K w).Nodup := by
  refine List.Nodup.of_map (Letter.code K) ?_
  show [0, 1, 2].Nodup
  decide

theorem nodup_complexBlock (w : {w : InfinitePlace K // w.IsComplex}) : (complexBlock K w).Nodup := by
  refine List.Nodup.of_map (Letter.code K) ?_
  show [0, 1, 2, 3, 4, 5].Nodup
  decide

theorem nodup_letters : (letters K).Nodup := by
  rw [letters, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun w _ => nodup_realBlock K w, ?_⟩
    refine (Finset.nodup_toList _).imp fun {a b} hab => ?_
    refine List.disjoint_left.mpr fun d hda hdb => hab ?_
    exact Subtype.ext ((place_of_mem_realBlock K hda).1.symm.trans (place_of_mem_realBlock K hdb).1)
  · rw [List.nodup_flatMap]
    refine ⟨fun w _ => nodup_complexBlock K w, ?_⟩
    refine (Finset.nodup_toList _).imp fun {a b} hab => ?_
    refine List.disjoint_left.mpr fun d hda hdb => hab ?_
    exact Subtype.ext ((place_of_mem_complexBlock K hda).1.symm.trans (place_of_mem_complexBlock K hdb).1)
  · intro d hda d' hdb hdd
    subst hdd
    obtain ⟨w, -, hw⟩ := List.mem_flatMap.mp hda
    obtain ⟨w', -, hw'⟩ := List.mem_flatMap.mp hdb
    have h1 := (place_of_mem_realBlock K hw).2
    have h2 := (place_of_mem_complexBlock K hw').2
    rw [h1] at h2; exact absurd h2 (by decide)

end SN2Reduce

namespace SN2Reduce

theorem exists_pos_le_norm_real (ω : ℝˣ →* ℂˣ) (hω : Continuous fun t : ℝˣ => ((ω t : ℂˣ) : ℂ)) :
    ∃ m : ℝ, 0 < m ∧ ∀ t : ℝˣ, (t : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 2 → m ≤ ‖((ω t : ℂˣ) : ℂ)‖ := by

  let u : ℝ → ℝˣ := fun s => Units.mk0 (Real.exp s) (Real.exp_pos s).ne'
  have hu : Continuous u := by
    refine Units.continuous_iff.mpr ⟨Real.continuous_exp, ?_⟩
    have : (fun s => ((u s)⁻¹ : ℝˣ).val) = fun s => Real.exp (-s) := by
      funext s; rw [Units.val_inv_eq_inv_val, Real.exp_neg]; rfl
    rw [this]; exact Real.continuous_exp.comp continuous_neg
  have hcont : Continuous fun s => ‖((ω (u s) : ℂˣ) : ℂ)‖ := continuous_norm.comp (hω.comp hu)
  obtain ⟨s₀, hs₀, hmin⟩ := (isCompact_Icc (a := -Real.log 2) (b := Real.log 2)).exists_isMinOn
    (Set.nonempty_Icc.mpr (by have := Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num); linarith)) hcont.continuousOn
  refine ⟨‖((ω (u s₀) : ℂˣ) : ℂ)‖, norm_pos_iff.mpr (Units.ne_zero _), fun t ht => ?_⟩
  have htpos : 0 < (t : ℝ) := lt_of_lt_of_le (by norm_num) ht.1
  have htu : t = u (Real.log t) := by
    apply Units.ext; show (t : ℝ) = Real.exp (Real.log t); rw [Real.exp_log htpos]
  have hmem : Real.log t ∈ Set.Icc (-Real.log 2) (Real.log 2) := by
    constructor
    · rw [← Real.log_inv]; exact Real.log_le_log (by norm_num) (by rw [inv_eq_one_div]; exact ht.1)
    · exact Real.log_le_log htpos ht.2
  have := hmin hmem
  rw [htu]; exact this

theorem exists_pos_le_norm_complex (ω : ℂˣ →* ℂˣ) (hω : Continuous fun z : ℂˣ => ((ω z : ℂˣ) : ℂ)) :
    ∃ m : ℝ, 0 < m ∧ ∀ z : ℂˣ, ‖(z : ℂ) - 1‖ ≤ 1 / 2 → m ≤ ‖((ω z : ℂˣ) : ℂ)‖ := by
  set D : Set ℂ := Metric.closedBall (1 : ℂ) (1 / 2) with hD
  have hD0 : ∀ z ∈ D, z ≠ 0 := by
    intro z hz h0; subst h0
    have : ‖(0 : ℂ) - 1‖ ≤ 1 / 2 := mem_closedBall_iff_norm.mp hz
    norm_num at this
  haveI : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let v : D → ℂˣ := fun p => Units.mk0 (p : ℂ) (hD0 p p.2)
  have hv : Continuous v := by
    refine Units.continuous_iff.mpr ⟨continuous_subtype_val, ?_⟩
    have : (fun p : D => ((v p)⁻¹ : ℂˣ).val) = fun p : D => ((p : ℂ))⁻¹ := by
      funext p; rw [Units.val_inv_eq_inv_val]; rfl
    rw [this]; exact continuous_subtype_val.inv₀ fun p => hD0 p p.2
  have hcont : Continuous fun p : D => ‖((ω (v p) : ℂˣ) : ℂ)‖ := continuous_norm.comp (hω.comp hv)
  have hne : (Set.univ : Set D).Nonempty := ⟨⟨1, Metric.mem_closedBall_self (by norm_num)⟩, trivial⟩
  obtain ⟨p₀, -, hmin⟩ := isCompact_univ.exists_isMinOn hne hcont.continuousOn
  refine ⟨‖((ω (v p₀) : ℂˣ) : ℂ)‖, norm_pos_iff.mpr (Units.ne_zero _), fun z hz => ?_⟩
  have hzD : (z : ℂ) ∈ D := mem_closedBall_iff_norm.mpr hz
  have hzv : z = v ⟨z, hzD⟩ := Units.ext rfl
  have := hmin (Set.mem_univ ⟨(z : ℂ), hzD⟩)
  rw [hzv]; exact this

theorem exists_pos_le_norm_all {K : Type} [Field K] [NumberField K]
    (ωR : ∀ w : InfinitePlace K, w.IsReal → (ℝˣ →* ℂˣ))
    (hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal), Continuous fun t : ℝˣ => ((ωR w hw t : ℂˣ) : ℂ))
    (ωC : ∀ w : InfinitePlace K, w.IsComplex → (ℂˣ →* ℂˣ))
    (hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), Continuous fun z : ℂˣ => ((ωC w hw z : ℂˣ) : ℂ)) :
    ∃ m : ℝ, 0 < m ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal) (t : ℝˣ), (t : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 2 → m ≤ ‖((ωR w hw t : ℂˣ) : ℂ)‖) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex) (z : ℂˣ), ‖(z : ℂ) - 1‖ ≤ 1 / 2 → m ≤ ‖((ωC w hw z : ℂˣ) : ℂ)‖) := by
  classical
  have hR : ∀ w : InfinitePlace K, ∀ hw : w.IsReal, ∃ m : ℝ, 0 < m ∧
      ∀ t : ℝˣ, (t : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 2 → m ≤ ‖((ωR w hw t : ℂˣ) : ℂ)‖ :=
    fun w hw => exists_pos_le_norm_real (ωR w hw) (hωR w hw)
  have hC : ∀ w : InfinitePlace K, ∀ hw : w.IsComplex, ∃ m : ℝ, 0 < m ∧
      ∀ z : ℂˣ, ‖(z : ℂ) - 1‖ ≤ 1 / 2 → m ≤ ‖((ωC w hw z : ℂˣ) : ℂ)‖ :=
    fun w hw => exists_pos_le_norm_complex (ωC w hw) (hωC w hw)
  choose mR hmR using hR
  choose mC hmC using hC
  let f : InfinitePlace K → ℝ := fun w => if hw : w.IsReal then mR w hw else mC w (not_isReal_iff_isComplex.mp hw)
  have hfpos : ∀ w, 0 < f w := by
    intro w; by_cases hw : w.IsReal
    · simp only [f, dif_pos hw]; exact (hmR w hw).1
    · simp only [f, dif_neg hw]; exact (hmC w _).1
  obtain ⟨w₀, -, hw₀⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  refine ⟨f w₀, hfpos w₀, fun w hw t ht => ?_, fun w hw z hz => ?_⟩
  · refine (hw₀ w (Finset.mem_univ w)).trans ?_
    simp only [f, dif_pos hw]; exact (hmR w hw).2 t ht
  · have hw' : ¬ w.IsReal := not_isReal_iff_isComplex.mpr hw
    refine (hw₀ w (Finset.mem_univ w)).trans ?_
    simp only [f, dif_neg hw']; exact (hmC w _).2 z hz

end SN2Reduce

namespace SN2Reduce

theorem sq_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, f i ^ 2 := by
  classical
  have := sq_sum_le_card_mul_sum_sq (s := s) (f := f)
  simpa using this

theorem lintegral_enorm_sq_le_of_eLpNorm_le {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℂ} {M : ℝ}
    (hM : 0 ≤ M) (h : eLpNorm f 2 ν ≤ ENNReal.ofReal M) : ∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (M ^ 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top] at h
  have h2r : (2 : ENNReal).toReal = 2 := by norm_num
  rw [h2r] at h
  have h2 := ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ 2 by norm_num)
  rw [← ENNReal.rpow_mul, show (1 / (2 : ℝ)) * 2 = 1 by norm_num, ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hM (by norm_num), Real.rpow_two] at h2
  simp only [← ENNReal.rpow_two]
  exact h2

theorem le_ofReal_div_of_mul_le {κ₀ : ℝ} (hκ₀ : 0 < κ₀) (r : ℕ) {J I : ENNReal} (c₂ : NNReal) {M : ℝ}
    (h : ENNReal.ofReal κ₀ ^ r * J ≤ (c₂ : ENNReal) * I) (hI : I ≤ ENNReal.ofReal (M ^ 2)) :
    J ≤ ENNReal.ofReal ((c₂ : ℝ) * M ^ 2 / κ₀ ^ r) := by
  have h3 : ENNReal.ofReal κ₀ ^ r * J ≤ (c₂ : ENNReal) * ENNReal.ofReal (M ^ 2) :=
    h.trans (mul_le_mul_right hI _)
  have hκr : ENNReal.ofReal κ₀ ^ r ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_pos.mpr hκ₀).ne'
  have hκr' : ENNReal.ofReal κ₀ ^ r ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have h4 : J ≤ ((c₂ : ENNReal) * ENNReal.ofReal (M ^ 2)) / ENNReal.ofReal κ₀ ^ r := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hκr) (Or.inl hκr'), mul_comm]; exact h3
  refine h4.trans (le_of_eq ?_)
  rw [ENNReal.ofReal_div_of_pos (pow_pos hκ₀ r), ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_pow hκ₀.le,
    ENNReal.ofReal_coe_nnreal]

theorem ofReal_sq_le_mul_sum_enorm_sq {ι : Type*} (Λ : Finset ι) (c₃ : ℝ) (D : ℝ) (hD0 : 0 ≤ D) (a : ι → ℂ)
    (h : D ≤ c₃ * ∑ l ∈ Λ, ‖a l‖) :
    ENNReal.ofReal (D ^ 2) ≤ ENNReal.ofReal (c₃ ^ 2 * Λ.card) * ∑ l ∈ Λ, ‖a l‖ₑ ^ 2 := by
  have h2 : D ^ 2 ≤ c₃ ^ 2 * Λ.card * ∑ l ∈ Λ, ‖a l‖ ^ 2 := by
    calc D ^ 2 ≤ (c₃ * ∑ l ∈ Λ, ‖a l‖) ^ 2 := pow_le_pow_left₀ hD0 h 2
      _ = c₃ ^ 2 * (∑ l ∈ Λ, ‖a l‖) ^ 2 := by ring
      _ ≤ c₃ ^ 2 * (Λ.card * ∑ l ∈ Λ, ‖a l‖ ^ 2) := mul_le_mul_of_nonneg_left (sq_sum_le Λ _) (sq_nonneg _)
      _ = c₃ ^ 2 * Λ.card * ∑ l ∈ Λ, ‖a l‖ ^ 2 := by ring
  calc ENNReal.ofReal (D ^ 2) ≤ ENNReal.ofReal (c₃ ^ 2 * Λ.card * ∑ l ∈ Λ, ‖a l‖ ^ 2) := ENNReal.ofReal_le_ofReal h2
    _ = ENNReal.ofReal (c₃ ^ 2 * Λ.card) * ∑ l ∈ Λ, ‖a l‖ₑ ^ 2 := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun l _ => sq_nonneg _)]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem setIntegral_sq_le_of_pointwise {X : Type*} [MeasurableSpace X] (ν : Measure X) (box : Set X)
    (hbox : MeasurableSet box) {ι : Type*} (Λ : Finset ι) (c₃ : ℝ) (φ : X → ℝ) (hφ : ∀ y, 0 ≤ φ y)
    (g : ι → X → ℂ) (hg : ∀ l ∈ Λ, Measurable fun y => ‖g l y‖ₑ ^ 2)
    (hpt : ∀ y ∈ box, φ y ≤ c₃ * ∑ l ∈ Λ, ‖g l y‖) (B : ℝ) (hB : 0 ≤ B)
    (hint : ∀ l ∈ Λ, ∫⁻ y in box, ‖g l y‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal B) :
    ∫ y in box, φ y ^ 2 ∂ν ≤ c₃ ^ 2 * Λ.card * Λ.card * B := by
  have hA0 : 0 ≤ c₃ ^ 2 * Λ.card * Λ.card * B := by positivity
  by_cases hi : Integrable (fun y => φ y ^ 2) (ν.restrict box)
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => sq_nonneg _) hi.aestronglyMeasurable]
    have hlin : ∫⁻ y in box, ENNReal.ofReal (φ y ^ 2) ∂ν ≤ ENNReal.ofReal (c₃ ^ 2 * Λ.card * Λ.card * B) := by
      calc ∫⁻ y in box, ENNReal.ofReal (φ y ^ 2) ∂ν
          ≤ ∫⁻ y in box, ENNReal.ofReal (c₃ ^ 2 * Λ.card) * ∑ l ∈ Λ, ‖g l y‖ₑ ^ 2 ∂ν :=
            setLIntegral_mono' hbox fun y hy => ofReal_sq_le_mul_sum_enorm_sq Λ c₃ (φ y) (hφ y) (fun l => g l y) (hpt y hy)
        _ = ENNReal.ofReal (c₃ ^ 2 * Λ.card) * ∑ l ∈ Λ, ∫⁻ y in box, ‖g l y‖ₑ ^ 2 ∂ν := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_finsetSum' _ (fun l hl => (hg l hl).aemeasurable)]
        _ ≤ ENNReal.ofReal (c₃ ^ 2 * Λ.card) * ∑ l ∈ Λ, ENNReal.ofReal B := by
            gcongr with l hl
            exact hint l hl
        _ = ENNReal.ofReal (c₃ ^ 2 * Λ.card * Λ.card * B) := by
            rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring
    calc (∫⁻ y in box, ENNReal.ofReal (φ y ^ 2) ∂ν).toReal ≤ (ENNReal.ofReal (c₃ ^ 2 * Λ.card * Λ.card * B)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
      _ = c₃ ^ 2 * Λ.card * Λ.card * B := ENNReal.toReal_ofReal hA0
  · rw [integral_undef hi]; exact hA0

theorem final_bound {n : ℕ} {cS A M : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M) (hcS : 0 ≤ cS) (I : ℕ → ℝ) (v : ℝ) (hv0 : 0 ≤ v)
    (hS : v ≤ cS * ∑ k ∈ Finset.range (n + 1), Real.sqrt (I k)) (hI : ∀ k, k ≤ n → I k ≤ A * M ^ 2) :
    v ≤ cS * (n + 1) * Real.sqrt A * M := by
  calc v ≤ cS * ∑ k ∈ Finset.range (n + 1), Real.sqrt (I k) := hS
    _ ≤ cS * ∑ k ∈ Finset.range (n + 1), Real.sqrt (A * M ^ 2) := by
        gcongr with k hk
        exact hI k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    _ = cS * (n + 1) * Real.sqrt A * M := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Real.sqrt_mul hA, Real.sqrt_sq hM]
        push_cast
        ring

end SN2Reduce

namespace SN2Reduce

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

end SN2Reduce

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

open SN2Reduce in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (ωR : ∀ w : InfinitePlace K, w.IsReal → (ℝˣ →* ℂˣ))
    (hωR : ∀ (w : InfinitePlace K) (hw : w.IsReal), Continuous fun t : ℝˣ => ((ωR w hw t : ℂˣ) : ℂ))
    (ωC : ∀ w : InfinitePlace K, w.IsComplex → (ℂˣ →* ℂˣ))
    (hωC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), Continuous fun z : ℂˣ => ((ωC w hw z : ℂˣ) : ℂ))
    (C : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    ∃ C' : Set (AdelicGL2 (𝓞 K) K), IsCompact C' ∧ C ⊆ C' ∧ ∃ c : ℝ, 0 ≤ c ∧
      ∀ b : AdelicGL2 (𝓞 K) K → ℂ,
        (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, b (g * u) = b g) →
        (∀ (w : InfinitePlace K) (hw : w.IsReal) (t : ℝˣ) (g : AdelicGL2 (𝓞 K) K),
            b (g * archRealGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom t)) =
              ((ωR w hw t : ℂˣ) : ℂ) * b g) →
        (∀ (w : InfinitePlace K) (hw : w.IsComplex) (z : ℂˣ) (g : AdelicGL2 (𝓞 K) K),
            b (g * archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom z)) =
              ((ωC w hw z : ℂˣ) : ℂ) * b g) →
        (∀ l, l.length ≤ 4 * nrRealPlaces K + 8 * nrComplexPlaces K →
          Continuous (W l b) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (W l b)) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (W l b))) →
        ∀ M : ℝ, 0 ≤ M →
          (∀ l, l.length ≤ 4 * nrRealPlaces K + 8 * nrComplexPlaces K →
            eLpNorm (W l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict C') ≤ ENNReal.ofReal M) →
          ∀ x ∈ C, ‖b x‖ ≤ c * M := by
  intro W
  classical

  have hL₀n := nodup_letters K
  have hL₀c := mem_letters K
  have hlen := length_letters_le K

  obtain ⟨hflR, hflC⟩ := AutomorphicForm.continuous_archFlowAt_and_continuous_archFlowAtComplex K

  obtain ⟨ℓ, hℓ, Θ, hΘ, c₂, hC2⟩ :=
    AutomorphicForm.exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq K N hN (letters K) hL₀n hL₀c
  obtain ⟨Λ, c₃, hΛ, hc₃, hC3⟩ :=
    AutomorphicForm.exists_forall_contDiff_norm_iteratedFDeriv_comp_flowChart_le_sum_foldr_archDeriv K (letters K) ℓ hℓ
  obtain ⟨cS, hcS, hSob⟩ :=
    Sobolev.exists_forall_norm_le_mul_sum_sqrt_integral_norm_iteratedFDeriv_sq_of_contDiff_box (letters K).length (2 * ℓ)
      (by positivity)
  obtain ⟨m, hm, hmR, hmC⟩ := exists_pos_le_norm_all ωR hωR ωC hωC

  refine ⟨C ∪ (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => p.1 * p.2) '' (C ×ˢ Θ),
    hC.union ((hC.prod hΘ).image continuous_mul), Set.subset_union_left, ?_⟩

  set r : ℕ := Fintype.card (InfinitePlace K) with hr
  set κ₀ : ℝ := m ^ 2 with hκ₀def
  have hκ₀ : 0 < κ₀ := by positivity
  set A : ℝ := c₃ ^ 2 * (Λ.card : ℝ) * (Λ.card : ℝ) * ((c₂ : ℝ) / κ₀ ^ r) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨cS * ((letters K).length + 1) * Real.sqrt A, by positivity, ?_⟩
  intro b hbU hbR hbC hreg M hM hL2 x hx

  have hreg' : ∀ l : List (Letter K), l.length ≤ (letters K).length →
      Continuous (W l b) ∧ (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (W l b)) ∧
        (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (W l b)) :=
    fun l hl => hreg l (hl.trans hlen)
  obtain ⟨hF, hD⟩ := hC3 b hreg' x
  have hC1 : ∀ l, (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, W l b (g * u) = W l b g) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal) (t : ℝˣ) (g : AdelicGL2 (𝓞 K) K),
        W l b (g * archRealGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom t)) =
          ((ωR w hw t : ℂˣ) : ℂ) * W l b g) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex) (z : ℂˣ) (g : AdelicGL2 (𝓞 K) K),
        W l b (g * archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom z)) =
          ((ωC w hw z : ℂˣ) : ℂ) * W l b g) :=
    AutomorphicForm.foldr_archDeriv_mul_eq_of_forall_mul_eq K N ωR ωC b hbU hbR hbC

  set chart : (Fin (letters K).length → ℝ) → AdelicGL2 (𝓞 K) K := fun t =>
    (List.ofFn fun j => Sum.elim (fun d => archFlowAt d.2.1 d.2.2 (t j)) (fun d => archFlowAtComplex d.2.1 d.2.2 (t j))
      ((letters K).get j)).prod with hchart
  have hflow_cont : ∀ d : Letter K, Continuous fun s : ℝ =>
      (Sum.elim (fun d => archFlowAt d.2.1 d.2.2 s) (fun d => archFlowAtComplex d.2.1 d.2.2 s) d : AdelicGL2 (𝓞 K) K) := by
    rintro (⟨w, hw, d⟩ | ⟨w, hw, d⟩)
    · exact hflR w hw d
    · exact hflC w hw d
  have hchart_cont : Continuous chart := by
    have : chart = fun t => (((List.finRange (letters K).length).map fun j =>
        Sum.elim (fun d => archFlowAt d.2.1 d.2.2 (t j)) (fun d => archFlowAtComplex d.2.1 d.2.2 (t j))
          ((letters K).get j))).prod := by
      funext t; simp only [hchart, List.ofFn_eq_map]
    rw [this]
    exact continuous_list_prod _ fun j _ => (hflow_cont _).comp (continuous_apply j)
  have hchart0 : chart 0 = 1 := by
    rw [hchart]
    refine List.prod_eq_one fun y hy => ?_
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    rcases (letters K).get j with ⟨w, hw, d⟩ | ⟨w, hw, d⟩
    · exact archFlowAt_zero hw d
    · exact archFlowAtComplex_zero hw d

  set F : (Fin (letters K).length → ℝ) → ℂ := fun t => b (x * chart t) with hFdef
  have hF0 : F 0 = b x := by simp only [hFdef, hchart0, mul_one]
  have hS := hSob (fun _ => -ℓ) F hF 0 (fun i => by simp only [Pi.zero_apply]; constructor <;> linarith)
  have h2l : -ℓ + 2 * ℓ = ℓ := by ring
  simp only [h2l] at hS
  rw [hF0] at hS
  set box : Set (Fin (letters K).length → ℝ) := Set.pi Set.univ fun _ => Set.Icc (-ℓ) ℓ with hbox
  have hboxm : MeasurableSet box := MeasurableSet.univ_pi fun _ => measurableSet_Icc

  have hκle : ∀ c : ℂ, m ≤ ‖c‖ → ENNReal.ofReal κ₀ ≤ ‖c‖ₑ ^ 2 := by
    intro c hc
    rw [hκ₀def, ENNReal.ofReal_pow hm.le, ← ofReal_norm]
    exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal hc) 2
  have hsub : (fun θ => x * θ) '' Θ ⊆ C ∪ (fun p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K => p.1 * p.2) '' (C ×ˢ Θ) := by
    rintro _ ⟨θ, hθ, rfl⟩
    exact Or.inr ⟨(x, θ), ⟨hx, hθ⟩, rfl⟩
  have hword : ∀ l ∈ Λ, ∫⁻ t in box, ‖W l b (x * chart t)‖ₑ ^ 2 ≤ ENNReal.ofReal ((c₂ : ℝ) * M ^ 2 / κ₀ ^ r) := by
    intro l hlΛ
    have hl : l.length ≤ (letters K).length := hΛ l hlΛ
    have hWc : Continuous (W l b) := (hreg' l hl).1
    have h2 := hC2 x (ENNReal.ofReal κ₀) (fun y => ‖W l b y‖ₑ ^ 2) (hWc.measurable.enorm.pow_const 2)
      (fun y u hu => by simp only [(hC1 l).1 y u hu])
      (fun y w hw t ht => by
        simp only [(hC1 l).2.1 w hw t y, enorm_mul, mul_pow]
        exact mul_le_mul_left (hκle _ (hmR w hw t ht)) _)
      (fun y w hw z hz => by
        simp only [(hC1 l).2.2 w hw z y, enorm_mul, mul_pow]
        exact mul_le_mul_left (hκle _ (hmC w hw z hz)) _)
    have hint := lintegral_enorm_sq_le_of_eLpNorm_le hM (hL2 l (hl.trans hlen))
    exact le_ofReal_div_of_mul_le hκ₀ r c₂ h2 ((lintegral_mono_set hsub).trans hint)

  have hmeasW : ∀ l ∈ Λ, Measurable fun t : Fin (letters K).length → ℝ => ‖W l b (x * chart t)‖ₑ ^ 2 := by
    intro l hl
    have hWc : Continuous (W l b) := (hreg' l (hΛ l hl)).1
    exact (hWc.comp (continuous_const.mul hchart_cont)).measurable.enorm.pow_const 2
  have hD' : ∀ k, k ≤ (letters K).length → ∀ t : Fin (letters K).length → ℝ, (∀ j, t j ∈ Set.Icc (-ℓ) ℓ) →
      ‖iteratedFDeriv ℝ k F t‖ ≤ c₃ * ∑ l ∈ Λ, ‖W l b (x * chart t)‖ :=
    fun k hk t ht => hD k hk t ht
  have hI : ∀ k, k ≤ (letters K).length → ∫ y in box, ‖iteratedFDeriv ℝ k F y‖ ^ 2 ≤ A * M ^ 2 := by
    intro k hk
    have h := setIntegral_sq_le_of_pointwise volume box hboxm Λ c₃ (fun y => ‖iteratedFDeriv ℝ k F y‖)
      (fun y => norm_nonneg _) (fun l y => W l b (x * chart y)) hmeasW
      (fun y hy => hD' k hk y fun j => (Set.mem_univ_pi.mp hy) j) _ (by positivity) hword
    refine h.trans (le_of_eq ?_)
    rw [hA]; ring
  exact final_bound hA0 hM hcS (fun k => ∫ y in box, ‖iteratedFDeriv ℝ k F y‖ ^ 2) ‖b x‖ (norm_nonneg _) hS hI

end
end S_AutomorphicForm_exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le
end P2MW
export P2MW.S_AutomorphicForm_exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le (solution)
