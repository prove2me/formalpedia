-- Prove2me | solution 1 for AutomorphicForm.setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/169801f1-4e43-504f-969b-763c3129559e

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Theorems.Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
import Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem
import Theorems.Thm_NumberField_AdeleRing_exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact
import Theorems.Thm_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory

open scoped ENNReal NNReal
open NumberField.AdelicVolume Set

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar

noncomputable section

namespace SquareMassSiegel

variable (K : Type) [Field K] [NumberField K]

local notation "G𝔸" => GL (Fin 2) (AdeleRing (𝓞 K) K)
local notation "Z𝔸" => GL (Fin 1) (AdeleRing (𝓞 K) K)
local notation "𝔸" => AdeleRing (𝓞 K) K
local notation "μG" => adelicGLHaar (Fin 2) (𝓞 K) K
local notation "μZ" => adelicGLHaar (Fin 1) (𝓞 K) K

private def window (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) : Set G𝔸 :=
  ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂

private def region (x : G𝔸) (C : Set G𝔸) : Set G𝔸 :=
  Set.image2 (fun (t : 𝔸) (c : G𝔸) => unipotentGL2 t * x * c) (closure (adelicBox K)) C

private def cen : Z𝔸 →* G𝔸 :=
  (centralScalar (𝓞 K) K).comp Matrix.GeneralLinearGroup.det

private def ratCentre : Subgroup (GL (Fin 2) K) :=
  (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ →* GL (Fin 2) K).range

private def cmass (E : Set G𝔸) (γ : GL (Fin 2) K) (g : G𝔸) : ℝ≥0∞ :=
  μZ {z : Z𝔸 | cen K z * globalPoints (𝓞 K) K γ * g ∈ E}

private def fibre (E : Set G𝔸) (g : G𝔸) : ℝ≥0∞ :=
  ∑' q : GL (Fin 2) K ⧸ ratCentre K, cmass K E (Quotient.out q) g

private theorem fst_apply_ne_zero (t : (𝔸)ˣ) (w : InfinitePlace K) : (t : 𝔸).1 w ≠ 0 := by
  intro h0
  have h1 : ((t : 𝔸) * ((t⁻¹ : (𝔸)ˣ) : 𝔸)).1 w = (1 : 𝔸).1 w := by rw [Units.mul_inv]
  have h2 : ((t : 𝔸) * ((t⁻¹ : (𝔸)ˣ) : 𝔸)).1 w = (t : 𝔸).1 w * ((t⁻¹ : (𝔸)ˣ) : 𝔸).1 w := rfl
  rw [h2, h0, zero_mul] at h1
  exact zero_ne_one h1

private theorem archComponent_centralScalar_apply (t : (𝔸)ˣ) (w : InfinitePlace K) (i j : Fin 2) :
    ((archComponent K w (glArch (𝓞 K) K (centralScalar (𝓞 K) K t)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j = if i = j then (t : 𝔸).1 w else 0 := by
  rw [archComponent_apply, glArch_apply]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, if_pos rfl]
  · rw [centralScalar_apply_ne _ h, if_neg h]
    rfl

private theorem archDetNorm_centralScalar_mul' (t : (𝔸)ˣ) (w : InfinitePlace K) (g : G𝔸) :
    archDetNorm w (centralScalar (𝓞 K) K t * g) = ‖(t : 𝔸).1 w‖ ^ 2 * archDetNorm w g := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]
  congr 1
  rw [Matrix.det_fin_two]
  simp only [archComponent_centralScalar_apply]
  simp [sq, norm_mul]

private theorem mul_centralScalar_mem_centreCutSiegelSet {c u d₁ d₂ a' b' : ℝ} {h : G𝔸}
    (hh : h ∈ centreCutSiegelSet K c u d₁ d₂) (t : (𝔸)ˣ)
    (hf : glFin (𝓞 K) K (centralScalar (𝓞 K) K t) ∈ finiteIntegralGL2 (𝓞 K) K)
    (hband : ∀ w : InfinitePlace K, ‖(t : 𝔸).1 w‖ ^ 2 * archDetNorm w h ∈ Icc a' b') :
    h * centralScalar (𝓞 K) K t ∈ centreCutSiegelSet K c u a' b' := by
  rw [mul_centralScalar_comm]
  obtain ⟨h1, h2, h3, h4⟩ := mem_centreCutSiegelSet_iff.mp hh
  have e := archComponent_centralScalar_apply K t
  have e00 : ∀ w : InfinitePlace K,
      ((archComponent K w (glArch (𝓞 K) K (centralScalar (𝓞 K) K t)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 0 0 = (t : 𝔸).1 w := fun w => by rw [e, if_pos rfl]
  have e11 : ∀ w : InfinitePlace K,
      ((archComponent K w (glArch (𝓞 K) K (centralScalar (𝓞 K) K t)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 1 1 = (t : 𝔸).1 w := fun w => by rw [e, if_pos rfl]
  have e01 : ∀ w : InfinitePlace K,
      ((archComponent K w (glArch (𝓞 K) K (centralScalar (𝓞 K) K t)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 0 1 = 0 := fun w => by rw [e, if_neg (by decide)]
  have e10 : ∀ w : InfinitePlace K,
      ((archComponent K w (glArch (𝓞 K) K (centralScalar (𝓞 K) K t)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) 1 0 = 0 := fun w => by rw [e, if_neg (by decide)]
  refine mem_centreCutSiegelSet_iff.mpr ⟨?_, fun w => ?_, fun w => ?_, fun w => ?_⟩
  · rw [map_mul]
    exact mul_mem hf h1
  · rw [map_mul, map_mul,
      localHeight_scalar_entries_mul (fst_apply_ne_zero K t w) (e00 w) (e01 w) (e10 w) (e11 w)]
    exact h2 w
  · rw [map_mul, map_mul,
      xWindowSq_scalar_entries_mul (fst_apply_ne_zero K t w) (e00 w) (e01 w) (e10 w) (e11 w)]
    exact h3 w
  · rw [archDetNorm_centralScalar_mul']
    exact hband w

private def archIdele (a : (w : InfinitePlace K) → (w.Completion)ˣ) : (𝔸)ˣ where
  val := (fun w => ((a w : (w.Completion)ˣ) : w.Completion), 1)
  inv := (fun w => (((a w)⁻¹ : (w.Completion)ˣ) : w.Completion), 1)
  val_inv := Prod.ext (funext fun w => Units.mul_inv (a w)) (one_mul 1)
  inv_val := Prod.ext (funext fun w => Units.inv_mul (a w)) (one_mul 1)

private theorem archIdele_fst (a : (w : InfinitePlace K) → (w.Completion)ˣ) (w : InfinitePlace K) :
    ((archIdele K a : (𝔸)ˣ) : 𝔸).1 w = (a w : w.Completion) := rfl

private theorem glFin_centralScalar_archIdele (a : (w : InfinitePlace K) → (w.Completion)ˣ) :
    glFin (𝓞 K) K (centralScalar (𝓞 K) K (archIdele K a)) ∈ finiteIntegralGL2 (𝓞 K) K := by
  rw [glFin_scalar_eq_one K (w := (archIdele K a : 𝔸)) rfl (centralScalar_apply_eq _ 0)
    (centralScalar_apply_ne _ (by decide)) (centralScalar_apply_ne _ (by decide))
    (centralScalar_apply_eq _ 1)]
  exact one_mem _

omit [NumberField K] in

private theorem exists_norm_eq (w : InfinitePlace K) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ x : w.Completion, ‖x‖ = ρ := by
  rcases w.isReal_or_isComplex with hw | hw
  · obtain ⟨x, hx⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw ρ
    refine ⟨x, ?_⟩
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) x, hx, Real.norm_of_nonneg hρ]
  · obtain ⟨x, hx⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw (ρ : ℂ)
    refine ⟨x, ?_⟩
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) x, hx, Complex.norm_real, Real.norm_of_nonneg hρ]

omit [NumberField K] in

private theorem exists_unit_sq_mul_eq (w : InfinitePlace K) {D a : ℝ} (hD : 0 < D) (ha : 0 < a) :
    ∃ aw : (w.Completion)ˣ, ‖(aw : w.Completion)‖ ^ 2 * D = a := by
  obtain ⟨x, hx⟩ := exists_norm_eq K w (Real.sqrt_nonneg (a / D))
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hx
    exact (Real.sqrt_pos.mpr (div_pos ha hD)).ne hx
  refine ⟨Units.mk0 x hx0, ?_⟩
  rw [Units.val_mk0, hx, Real.sq_sqrt (div_pos ha hD).le, div_mul_cancel₀ _ hD.ne']

private theorem BAND (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hcov : CoversModCentre K (window K c u d₁ d₂ T)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    CoversModCentre K (window K c u a b T) := by
  intro g
  obtain ⟨γ, z, hz⟩ := hcov g
  rw [window, Set.mem_iUnion₂] at hz
  obtain ⟨x₀, hx₀, h, hh, hhx⟩ := hz
  dsimp only at hhx
  have hex : ∀ w : InfinitePlace K,
      ∃ aw : (w.Completion)ˣ, ‖(aw : w.Completion)‖ ^ 2 * archDetNorm w h = a :=
    fun w => exists_unit_sq_mul_eq K w (archDetNorm_pos w h) ha
  choose aw haw using hex
  refine ⟨γ, z * archIdele K aw, ?_⟩
  rw [window, Set.mem_iUnion₂]
  refine ⟨x₀, hx₀, h * centralScalar (𝓞 K) K (archIdele K aw), ?_, ?_⟩
  · refine mul_centralScalar_mem_centreCutSiegelSet K hh _ (glFin_centralScalar_archIdele K aw)
      fun w => ?_
    rw [archIdele_fst, haw w]
    exact ⟨le_rfl, hab⟩
  · show h * centralScalar (𝓞 K) K (archIdele K aw) * x₀ = _
    rw [map_mul, ← mul_assoc, ← hhx, mul_assoc, ← mul_centralScalar_comm (archIdele K aw) x₀,
      ← mul_assoc]

private theorem WMONO (c u : ℝ) {d₁ d₂ a b : ℝ} (T : Finset (AdelicGL2 (𝓞 K) K)) (h₁ : d₁ ≤ a)
    (h₂ : b ≤ d₂) : window K c u a b T ⊆ window K c u d₁ d₂ T := by
  intro g hg
  rw [window, Set.mem_iUnion₂] at hg ⊢
  obtain ⟨x, hx, h, hh, rfl⟩ := hg
  refine ⟨x, hx, h, ?_, rfl⟩
  obtain ⟨k1, k2, k3, k4⟩ := mem_centreCutSiegelSet_iff.mp hh
  exact mem_centreCutSiegelSet_iff.mpr ⟨k1, k2, k3, fun w => Icc_subset_Icc h₁ h₂ (k4 w)⟩

private theorem WMEAS (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) :
    MeasurableSet (window K c u d₁ d₂ T) := by
  refine Finset.measurableSet_biUnion T fun x _ => ?_
  rw [Set.image_mul_right]
  exact measurable_mul_const x⁻¹ (measurableSet_centreCutSiegelSet c u d₁ d₂)

private theorem continuous_unip : Continuous (fun t : 𝔸 => unipotentGL2 t) := by
  have hval : Continuous (fun t : 𝔸 => ((unipotentGL2 t : G𝔸) : Matrix (Fin 2) (Fin 2) 𝔸)) := by
    refine continuous_matrix fun i j => ?_
    simp only [unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  have hinv : ∀ t : 𝔸, (unipotentGL2 t)⁻¹ = unipotentGL2 (-t) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])
  simp only [hinv]
  exact hval.comp continuous_neg

private theorem isCompact_closure_box : IsCompact (closure (adelicBox K)) := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset K
  exact hC.closure_of_subset hsub

private theorem REGION (x : G𝔸) {C : Set G𝔸} (hC : IsCompact C) :
    IsCompact (region K x C) ∧ MeasurableSet (region K x C) := by
  have hcont : Continuous (fun p : 𝔸 × G𝔸 => unipotentGL2 p.1 * x * p.2) :=
    (((continuous_unip K).comp continuous_fst).mul continuous_const).mul continuous_snd
  have hcpt : IsCompact (region K x C) := by
    rw [region, ← Set.image_prod]
    exact ((isCompact_closure_box K).prod hC).image hcont
  exact ⟨hcpt, hcpt.isClosed.measurableSet⟩

private theorem cen_scalar (t : (𝔸)ˣ) :
    cen K (Matrix.GeneralLinearGroup.scalar (Fin 1) t) = centralScalar (𝓞 K) K t := by
  show centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 1) t))
    = centralScalar (𝓞 K) K t
  congr 1
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  simp

private theorem cen_mul_comm (z z' : Z𝔸) : cen K (z * z') = cen K (z' * z) := by
  rw [map_mul, map_mul]
  show centralScalar (𝓞 K) K _ * centralScalar (𝓞 K) K _ = centralScalar (𝓞 K) K _ * centralScalar (𝓞 K) K _
  rw [mul_centralScalar_comm]

private theorem globalPoints_scalar (k : Kˣ) :
    globalPoints (𝓞 K) K (Matrix.GeneralLinearGroup.scalar (Fin 2) k)
      = centralScalar (𝓞 K) K (Units.map (algebraMap K (𝔸)) k) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [centralScalar_val, Matrix.diagonal_apply]
  show algebraMap K (𝔸) (Matrix.scalar (Fin 2) (k : K) i j) = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

private theorem cmass_mul_ratCentre (E : Set G𝔸) (γ : GL (Fin 2) K) {s : GL (Fin 2) K}
    (hs : s ∈ ratCentre K) (g : G𝔸) : cmass K E (γ * s) g = cmass K E γ g := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hs
  set k₁ : Z𝔸 := Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap K (𝔸)) k) with hk₁
  have hset : {z : Z𝔸 | cen K z * globalPoints (𝓞 K) K (γ * Matrix.GeneralLinearGroup.scalar (Fin 2) k) * g ∈ E}
      = (fun z : Z𝔸 => k₁ * z) ⁻¹' {z : Z𝔸 | cen K z * globalPoints (𝓞 K) K γ * g ∈ E} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    have : cen K z * globalPoints (𝓞 K) K (γ * Matrix.GeneralLinearGroup.scalar (Fin 2) k) * g
        = cen K (k₁ * z) * globalPoints (𝓞 K) K γ * g := by
      rw [map_mul, globalPoints_scalar, map_mul, hk₁, cen_scalar, ← mul_assoc, mul_centralScalar_comm,
        ← mul_assoc]
    rw [this]
  unfold cmass
  rw [hset, measure_preimage_mul]

private theorem cen_mul_eq (z : Z𝔸) (X : G𝔸) : cen K z * X = X * cen K z :=
  (mul_centralScalar_comm (Matrix.GeneralLinearGroup.det z) X).symm

private theorem det_val (z : Z𝔸) :
    ((Matrix.GeneralLinearGroup.det z : (𝔸)ˣ) : 𝔸) = (z : Matrix (Fin 1) (Fin 1) 𝔸) 0 0 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]

private theorem det_inv_val (z : Z𝔸) :
    (((Matrix.GeneralLinearGroup.det z)⁻¹ : (𝔸)ˣ) : 𝔸) = ((z⁻¹ : Z𝔸) : Matrix (Fin 1) (Fin 1) 𝔸) 0 0 := by
  rw [← map_inv, det_val]

private theorem glFin_centralScalar_mem (t : (𝔸)ˣ) (h₁ : (t : 𝔸).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K)
    (h₂ : ((t⁻¹ : (𝔸)ˣ) : 𝔸).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    glFin (𝓞 K) K (centralScalar (𝓞 K) K t) ∈ finiteIntegralGL2 (𝓞 K) K := by
  rw [mem_finiteIntegralGL2_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [glFin_apply]
    by_cases h : i = j
    · subst h
      rw [centralScalar_apply_eq]
      exact h₁
    · rw [centralScalar_apply_ne _ h]
      exact AdelicLevel.zero_mem_integralFiniteAdeles
  · rw [← map_inv, ← map_inv, glFin_apply]
    by_cases h : i = j
    · subst h
      rw [centralScalar_apply_eq]
      exact h₂
    · rw [centralScalar_apply_ne _ h]
      exact AdelicLevel.zero_mem_integralFiniteAdeles

private def centralBox (α β : ℝ) : Set Z𝔸 :=
  (⋂ w : InfinitePlace K, {z : Z𝔸 | ‖((z : Matrix (Fin 1) (Fin 1) 𝔸) 0 0).1 w‖ ^ 2 ∈ Ioo α β}) ∩
    ({z : Z𝔸 | ((z : Matrix (Fin 1) (Fin 1) 𝔸) 0 0).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K} ∩
      {z : Z𝔸 | (((z⁻¹ : Z𝔸) : Matrix (Fin 1) (Fin 1) 𝔸) 0 0).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K})

private theorem isOpen_centralBox (α β : ℝ) : IsOpen (centralBox K α β) := by
  have hval : Continuous (fun z : Z𝔸 => (z : Matrix (Fin 1) (Fin 1) 𝔸) 0 0) :=
    Units.continuous_val.matrix_elem 0 0
  have hinv : Continuous (fun z : Z𝔸 => ((z⁻¹ : Z𝔸) : Matrix (Fin 1) (Fin 1) 𝔸) 0 0) :=
    Units.continuous_coe_inv.matrix_elem 0 0
  refine (isOpen_iInter_of_finite fun w => ?_).inter (IsOpen.inter ?_ ?_)
  · exact isOpen_Ioo.preimage (((continuous_apply w).comp (continuous_fst.comp hval)).norm.pow 2)
  · exact (AdelicLevel.isOpen_integralFiniteAdeles (𝓞 K) K).preimage (continuous_snd.comp hval)
  · exact (AdelicLevel.isOpen_integralFiniteAdeles (𝓞 K) K).preimage (continuous_snd.comp hinv)

private theorem one_mem_centralBox {α β : ℝ} (hα : α < 1) (hβ : 1 < β) : (1 : Z𝔸) ∈ centralBox K α β := by
  have h1 : ((1 : Z𝔸) : Matrix (Fin 1) (Fin 1) 𝔸) 0 0 = 1 := by
    rw [Units.val_one, Matrix.one_apply_eq]
  refine ⟨Set.mem_iInter.mpr fun w => ?_, ?_, ?_⟩
  · show ‖(((1 : Z𝔸) : Matrix (Fin 1) (Fin 1) 𝔸) 0 0).1 w‖ ^ 2 ∈ Ioo α β
    rw [h1]
    have : ((1 : 𝔸)).1 w = 1 := rfl
    rw [this, norm_one, one_pow]
    exact ⟨hα, hβ⟩
  · show (((1 : Z𝔸) : Matrix (Fin 1) (Fin 1) 𝔸) 0 0).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K
    rw [h1]
    exact AdelicLevel.one_mem_integralFiniteAdeles
  · show ((((1 : Z𝔸)⁻¹ : Z𝔸) : Matrix (Fin 1) (Fin 1) 𝔸) 0 0).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K
    rw [inv_one, h1]
    exact AdelicLevel.one_mem_integralFiniteAdeles

private theorem mul_cen_mem_of_mem_centralBox {c u a b a' b' : ℝ} (ha' : 0 < a') (hb' : 0 < b')
    (hb : 0 ≤ b) {h : G𝔸} (hh : h ∈ centreCutSiegelSet K c u a' b') {z : Z𝔸}
    (hz : z ∈ centralBox K (a / a') (b / b')) :
    h * cen K z ∈ centreCutSiegelSet K c u a b := by
  obtain ⟨hz₁, hz₂, hz₃⟩ := hz
  rw [Set.mem_iInter] at hz₁
  have hD := (mem_centreCutSiegelSet_iff.mp hh).2.2.2
  refine mul_centralScalar_mem_centreCutSiegelSet K hh (Matrix.GeneralLinearGroup.det z) ?_ fun w => ?_
  · refine glFin_centralScalar_mem K _ ?_ ?_
    · rw [det_val]
      exact hz₂
    · rw [det_inv_val]
      exact hz₃
  · rw [det_val]
    have hs := hz₁ w
    have hDw := hD w
    have hs0 : (0 : ℝ) ≤ ‖((z : Matrix (Fin 1) (Fin 1) 𝔸) 0 0).1 w‖ ^ 2 := by positivity
    constructor
    · calc a = a / a' * a' := (div_mul_cancel₀ a ha'.ne').symm
        _ ≤ _ := mul_le_mul hs.1.le hDw.1 ha'.le hs0
    · calc _ ≤ b / b' * b' := mul_le_mul hs.2.le hDw.2 (archDetNorm_pos w h).le (div_nonneg hb hb'.le)
        _ = b := div_mul_cancel₀ b hb'.ne'

private theorem FLOOR (c u a b : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (ha : 0 < a) (hab : a < b)
    (hcov : ∀ a' b' : ℝ, 0 < a' → a' ≤ b' → CoversModCentre K (window K c u a' b' T)) :
    ∃ m : ℝ, 0 < m ∧ ∀ g : G𝔸, ENNReal.ofReal m ≤ fibre K (window K c u a b T) g := by
  have hpos : 0 < (b - a) / 3 := by linarith
  have ha' : 0 < a + (b - a) / 3 := by linarith
  have hb' : 0 < b - (b - a) / 3 := by linarith
  have hab' : a + (b - a) / 3 ≤ b - (b - a) / 3 := by linarith
  have hα : a / (a + (b - a) / 3) < 1 := (div_lt_one ha').mpr (by linarith)
  have hβ : 1 < b / (b - (b - a) / 3) := (one_lt_div hb').mpr (by linarith)
  obtain ⟨N, hN, hN1⟩ := exists_compact_mem_nhds (1 : Z𝔸)
  have hVopen : IsOpen (interior N ∩ centralBox K (a / (a + (b - a) / 3)) (b / (b - (b - a) / 3))) :=
    isOpen_interior.inter (isOpen_centralBox K _ _)
  have hV1 : (1 : Z𝔸) ∈ interior N ∩ centralBox K (a / (a + (b - a) / 3)) (b / (b - (b - a) / 3)) :=
    ⟨mem_interior_iff_mem_nhds.mpr hN1, one_mem_centralBox K hα hβ⟩
  have hVpos : 0 < μZ (interior N ∩ centralBox K (a / (a + (b - a) / 3)) (b / (b - (b - a) / 3))) :=
    hVopen.measure_pos μZ ⟨1, hV1⟩
  have hVfin : μZ (interior N ∩ centralBox K (a / (a + (b - a) / 3)) (b / (b - (b - a) / 3))) < ⊤ :=
    (measure_mono (Set.inter_subset_left.trans interior_subset)).trans_lt hN.measure_lt_top
  refine ⟨(μZ (interior N ∩ centralBox K (a / (a + (b - a) / 3)) (b / (b - (b - a) / 3)))).toReal,
    ENNReal.toReal_pos hVpos.ne' hVfin.ne, fun g => ?_⟩
  rw [ENNReal.ofReal_toReal hVfin.ne]
  obtain ⟨γ₀, z₀, hz₀⟩ := hcov _ _ ha' hab' g
  rw [window, Set.mem_iUnion₂] at hz₀
  obtain ⟨x₀, hx₀, h, hh, hhx⟩ := hz₀
  dsimp only at hhx
  set z₁ : Z𝔸 := Matrix.GeneralLinearGroup.scalar (Fin 1) z₀ with hz₁
  have hcz₁ : cen K z₁ = centralScalar (𝓞 K) K z₀ := cen_scalar K z₀
  have hsub : (fun z : Z𝔸 => z₁⁻¹ * z) ⁻¹'
        (interior N ∩ centralBox K (a / (a + (b - a) / 3)) (b / (b - (b - a) / 3)))
      ⊆ {z : Z𝔸 | cen K z * globalPoints (𝓞 K) K γ₀ * g ∈ window K c u a b T} := by
    intro z hz
    rw [Set.mem_preimage] at hz
    show cen K z * globalPoints (𝓞 K) K γ₀ * g ∈ window K c u a b T
    rw [window, Set.mem_iUnion₂]
    refine ⟨x₀, hx₀, h * cen K (z₁⁻¹ * z), mul_cen_mem_of_mem_centralBox K ha' hb'
      (ha.trans hab).le hh hz.2, ?_⟩
    show h * cen K (z₁⁻¹ * z) * x₀ = cen K z * globalPoints (𝓞 K) K γ₀ * g
    calc h * cen K (z₁⁻¹ * z) * x₀ = h * x₀ * cen K (z₁⁻¹ * z) := by
          rw [mul_assoc, cen_mul_eq K (z₁⁻¹ * z) x₀, ← mul_assoc]
      _ = globalPoints (𝓞 K) K γ₀ * g * centralScalar (𝓞 K) K z₀ * cen K (z₁⁻¹ * z) := by rw [hhx]
      _ = cen K z₁ * cen K (z₁⁻¹ * z) * globalPoints (𝓞 K) K γ₀ * g := by
          rw [hcz₁, mul_centralScalar_comm z₀ (globalPoints (𝓞 K) K γ₀ * g), mul_assoc,
            ← cen_mul_eq K (z₁⁻¹ * z) (globalPoints (𝓞 K) K γ₀ * g), ← mul_assoc, ← mul_assoc]
      _ = cen K z * globalPoints (𝓞 K) K γ₀ * g := by rw [← map_mul, mul_inv_cancel_left]
  calc μZ (interior N ∩ centralBox K (a / (a + (b - a) / 3)) (b / (b - (b - a) / 3)))
      = μZ ((fun z : Z𝔸 => z₁⁻¹ * z) ⁻¹'
          (interior N ∩ centralBox K (a / (a + (b - a) / 3)) (b / (b - (b - a) / 3)))) :=
        (measure_preimage_mul μZ z₁⁻¹ _).symm
    _ ≤ cmass K (window K c u a b T) γ₀ g := measure_mono hsub
    _ = cmass K (window K c u a b T)
          (Quotient.out (QuotientGroup.mk γ₀ : GL (Fin 2) K ⧸ ratCentre K)) g := by
        obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul (ratCentre K) γ₀
        rw [hs, cmass_mul_ratCentre K _ _ s.2]
    _ ≤ fibre K (window K c u a b T) g := ENNReal.le_tsum _

private theorem det_fst (x : G𝔸) (w : InfinitePlace K) :
    ((Matrix.GeneralLinearGroup.det x : (𝔸)ˣ) : 𝔸).1 w
      = ((archComponent K w (glArch (𝓞 K) K x) : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  have h := RingHom.map_det ((archEval K w).comp (adeleArch (𝓞 K) K)) (x : Matrix (Fin 2) (Fin 2) 𝔸)
  exact h.trans (congrArg Matrix.det (Matrix.ext fun i j => rfl))

private theorem det_snd (x : G𝔸) :
    ((Matrix.GeneralLinearGroup.det x : (𝔸)ˣ) : 𝔸).2
      = ((glFin (𝓞 K) K x : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) :
          Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)).det := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  have h := RingHom.map_det (adeleFin (𝓞 K) K) (x : Matrix (Fin 2) (Fin 2) 𝔸)
  exact h.trans (congrArg Matrix.det (Matrix.ext fun i j => rfl))

private theorem archDetNorm_eq (w : InfinitePlace K) (x : G𝔸) :
    archDetNorm w x = ‖((Matrix.GeneralLinearGroup.det x : (𝔸)ˣ) : 𝔸).1 w‖ := by
  rw [det_fst]
  rfl

private theorem det_snd_mem {x : G𝔸} (hx : glFin (𝓞 K) K x ∈ finiteIntegralGL2 (𝓞 K) K) :
    ((Matrix.GeneralLinearGroup.det x : (𝔸)ˣ) : 𝔸).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  rw [det_snd, Matrix.det_fin_two]
  have h := (mem_finiteIntegralGL2_iff.mp hx).1
  exact AdelicLevel.sub_mem_integralFiniteAdeles (AdelicLevel.mul_mem_integralFiniteAdeles (h 0 0) (h 1 1))
    (AdelicLevel.mul_mem_integralFiniteAdeles (h 0 1) (h 1 0))

private theorem det_inv_snd_mem {x : G𝔸} (hx : glFin (𝓞 K) K x ∈ finiteIntegralGL2 (𝓞 K) K) :
    (((Matrix.GeneralLinearGroup.det x)⁻¹ : (𝔸)ˣ) : 𝔸).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  rw [← map_inv]
  refine det_snd_mem K ?_
  rw [map_inv]
  exact inv_mem hx

private theorem inv_fst_apply (t : (𝔸)ˣ) (w : InfinitePlace K) :
    ((t⁻¹ : (𝔸)ˣ) : 𝔸).1 w = ((t : 𝔸).1 w)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  have h := congrArg (fun y : 𝔸 => y.1 w) (Units.inv_mul t)
  exact h

private theorem exists_isCompact_adeles (r : ℝ) {B : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)}
    (hB : IsCompact B) :
    ∃ A : Set 𝔸, IsCompact A ∧ ∀ y : 𝔸, (∀ w : InfinitePlace K, ‖y.1 w‖ ≤ r) → y.2 ∈ B → y ∈ A := by
  have hball : ∀ w : InfinitePlace K,
      IsCompact (InfinitePlace.Completion.extensionEmbedding w ⁻¹' Metric.closedBall (0 : ℂ) r) :=
    fun w => (InfinitePlace.Completion.isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage
      (isCompact_closedBall 0 r)
  refine ⟨(Set.pi Set.univ fun w : InfinitePlace K =>
      InfinitePlace.Completion.extensionEmbedding w ⁻¹' Metric.closedBall (0 : ℂ) r) ×ˢ B,
    (isCompact_univ_pi hball).prod hB, fun y hy₁ hy₂ => ⟨?_, hy₂⟩⟩
  refine Set.mem_univ_pi.mpr fun w => ?_
  rw [Set.mem_preimage, mem_closedBall_zero_iff, SiegelCoordinates.norm_extensionEmbedding]
  exact hy₁ w

private theorem exists_isCompact_ideles {α β : ℝ} (hα : 0 < α) :
    ∃ Q : Set (𝔸)ˣ, IsCompact Q ∧ ∀ t : (𝔸)ˣ, (∀ w : InfinitePlace K, ‖(t : 𝔸).1 w‖ ∈ Icc α β) →
      (t : 𝔸).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K →
      ((t⁻¹ : (𝔸)ˣ) : 𝔸).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K → t ∈ Q := by
  have hbox : ∀ r : ℝ, ∃ A : Set 𝔸, IsCompact A ∧
      ∀ y : 𝔸, (∀ w : InfinitePlace K, ‖y.1 w‖ ≤ r) → y.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K → y ∈ A :=
    fun r => exists_isCompact_adeles K r (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 K) K)
  obtain ⟨A, hA, hAmem⟩ := hbox β
  obtain ⟨A', hA', hA'mem⟩ := hbox α⁻¹
  refine ⟨Units.embedProduct 𝔸 ⁻¹' (A ×ˢ (MulOpposite.op '' A')),
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hA.prod (hA'.image MulOpposite.continuous_op)),
    fun t ht hf hf' => ?_⟩
  rw [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod]
  refine ⟨hAmem _ (fun w => (ht w).2) hf, ⟨_, hA'mem _ (fun w => ?_) hf', rfl⟩⟩
  rw [inv_fst_apply, norm_inv]
  exact inv_anti₀ hα (ht w).1

private theorem det_mem_of_mem_centreCutSiegelSet {c u a b : ℝ}
    {Q : Set (𝔸)ˣ} (hQ : ∀ t : (𝔸)ˣ, (∀ w : InfinitePlace K, ‖(t : 𝔸).1 w‖ ∈ Icc a b) →
      (t : 𝔸).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K →
      ((t⁻¹ : (𝔸)ˣ) : 𝔸).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K → t ∈ Q)
    {h : G𝔸} (hh : h ∈ centreCutSiegelSet K c u a b) : Matrix.GeneralLinearGroup.det h ∈ Q := by
  obtain ⟨h1, -, -, h4⟩ := mem_centreCutSiegelSet_iff.mp hh
  refine hQ _ (fun w => ?_) (det_snd_mem K h1) (det_inv_snd_mem K h1)
  rw [← archDetNorm_eq]
  exact h4 w

private theorem det_unipotent (t : 𝔸) : Matrix.GeneralLinearGroup.det (unipotentGL2 t : G𝔸) = 1 := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, unipotentGL2_coe, Matrix.det_fin_two_of]
  simp

private theorem continuous_det : Continuous (Matrix.GeneralLinearGroup.det : G𝔸 → (𝔸)ˣ) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun g : G𝔸 => ((Matrix.GeneralLinearGroup.det g : (𝔸)ˣ) : 𝔸)
    simp only [Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.continuous_val.matrix_det
  · show Continuous fun g : G𝔸 => (((Matrix.GeneralLinearGroup.det g)⁻¹ : (𝔸)ˣ) : 𝔸)
    simp only [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.continuous_coe_inv.matrix_det

private theorem NORM (χ : (⊤ : Subgroup (𝔸)ˣ) →* ℂˣ)
    (hχc : Continuous fun z : (𝔸)ˣ => χ ⟨z, Subgroup.mem_top z⟩)
    (c u a b : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (ha : 0 < a)
    {C : Set G𝔸} (hC : IsCompact C) (c' u' d₁' d₂' : ℝ) (hd₁' : 0 < d₁') :
    ∃ Mup mlow : ℝ, 0 < Mup ∧ 0 < mlow ∧
      (∀ x ∈ centreCutSiegelSet K c' u' d₁' d₂', ∀ e ∈ region K x C,
        ‖((χ ⟨Matrix.GeneralLinearGroup.det e, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ ≤ Mup) ∧
      (∀ w ∈ window K c u a b T,
        mlow ≤ ‖((χ ⟨Matrix.GeneralLinearGroup.det w, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖) := by
  set f : (𝔸)ˣ → ℝ := fun t => ‖((χ ⟨t, Subgroup.mem_top t⟩ : ℂˣ) : ℂ)‖ with hf_def
  have hf : Continuous f := continuous_norm.comp (Units.continuous_val.comp hχc)
  have hf0 : ∀ t, 0 ≤ f t := fun t => norm_nonneg _
  have hfpos : ∀ t, 0 < f t := fun t => norm_pos_iff.mpr (Units.ne_zero _)
  have hfmul : ∀ s t, f (s * t) = f s * f t := by
    intro s t
    have : (⟨s * t, Subgroup.mem_top (s * t)⟩ : (⊤ : Subgroup (𝔸)ˣ))
        = ⟨s, Subgroup.mem_top s⟩ * ⟨t, Subgroup.mem_top t⟩ := rfl
    simp only [hf_def, this, map_mul, Units.val_mul, norm_mul]

  obtain ⟨Q₁, hQ₁, hQ₁mem⟩ := exists_isCompact_ideles K (β := d₂') hd₁'
  obtain ⟨M₁, hM₁⟩ := hQ₁.exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨M₂, hM₂⟩ := hC.exists_bound_of_continuousOn (hf.comp (continuous_det K)).continuousOn
  have hup : ∀ x ∈ centreCutSiegelSet K c' u' d₁' d₂', ∀ e ∈ region K x C,
      f (Matrix.GeneralLinearGroup.det e) ≤ max 1 (M₁ * M₂) := by
    intro x hx e he
    obtain ⟨t, -, k, hk, rfl⟩ := Set.mem_image2.mp he
    rw [map_mul, map_mul, det_unipotent, one_mul, hfmul]
    have h₁ : f (Matrix.GeneralLinearGroup.det x) ≤ M₁ := by
      have := hM₁ _ (det_mem_of_mem_centreCutSiegelSet K hQ₁mem hx)
      rwa [norm_norm] at this
    have h₂ : f (Matrix.GeneralLinearGroup.det k) ≤ M₂ := by
      have := hM₂ k hk
      rwa [Function.comp_apply, norm_norm] at this
    exact (mul_le_mul h₁ h₂ (hf0 _) ((hf0 _).trans h₁)).trans (le_max_right _ _)

  by_cases hW : (window K c u a b T).Nonempty
  · obtain ⟨w₀, hw₀⟩ := hW
    rw [window, Set.mem_iUnion₂] at hw₀
    obtain ⟨x₀, hx₀T, h₀, hh₀, -⟩ := hw₀
    obtain ⟨Q₂, hQ₂, hQ₂mem⟩ := exists_isCompact_ideles K (β := b) ha
    obtain ⟨t₀, -, ht₀⟩ := hQ₂.exists_isMinOn ⟨_, det_mem_of_mem_centreCutSiegelSet K hQ₂mem hh₀⟩
      hf.continuousOn
    obtain ⟨x₁, -, hx₁⟩ := T.exists_min_image (fun x => f (Matrix.GeneralLinearGroup.det x)) ⟨x₀, hx₀T⟩
    refine ⟨max 1 (M₁ * M₂), f t₀ * f (Matrix.GeneralLinearGroup.det x₁), lt_max_of_lt_left one_pos,
      mul_pos (hfpos _) (hfpos _), hup, fun w hw => ?_⟩
    rw [window, Set.mem_iUnion₂] at hw
    obtain ⟨x, hxT, h, hh, rfl⟩ := hw
    show _ ≤ f (Matrix.GeneralLinearGroup.det (h * x))
    rw [map_mul, hfmul]
    exact mul_le_mul (ht₀ (det_mem_of_mem_centreCutSiegelSet K hQ₂mem hh)) (hx₁ x hxT) (hf0 _) (hf0 _)
  · exact ⟨max 1 (M₁ * M₂), 1, lt_max_of_lt_left one_pos, one_pos, hup,
      fun w hw => absurd ⟨w, hw⟩ hW⟩

private theorem unip_inv (s : 𝔸) : (unipotentGL2 s : G𝔸)⁻¹ = unipotentGL2 (-s) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

private theorem trace_conj (x M : G𝔸) :
    Matrix.trace ((x⁻¹ * M * x : G𝔸) : Matrix (Fin 2) (Fin 2) 𝔸) = Matrix.trace (M : Matrix (Fin 2) (Fin 2) 𝔸) := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    one_mul]

private theorem trace_cen_mul_unip (t : Z𝔸) (s : 𝔸) :
    Matrix.trace ((cen K t * unipotentGL2 s : G𝔸) : Matrix (Fin 2) (Fin 2) 𝔸)
      = 2 * ((Matrix.GeneralLinearGroup.det t : (𝔸)ˣ) : 𝔸) := by
  rw [Units.val_mul]
  show Matrix.trace ((centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det t) : Matrix (Fin 2) (Fin 2) 𝔸)
    * (unipotentGL2 s : Matrix (Fin 2) (Fin 2) 𝔸)) = _
  rw [centralScalar_val, unipotentGL2_coe, Matrix.trace_fin_two]
  simp [Matrix.diagonal_mul, two_mul]

private def traceSet (C : Set G𝔸) : Set 𝔸 :=
  (fun M : G𝔸 => Matrix.trace (M : Matrix (Fin 2) (Fin 2) 𝔸)) '' Set.image2 (fun c c' : G𝔸 => c * c'⁻¹) C C

private theorem isCompact_traceSet {C : Set G𝔸} (hC : IsCompact C) : IsCompact (traceSet K C) := by
  have h₁ : IsCompact (Set.image2 (fun c c' : G𝔸 => c * c'⁻¹) C C) := by
    rw [← Set.image_prod]
    exact (hC.prod hC).image (continuous_fst.mul continuous_snd.inv)
  exact h₁.image Units.continuous_val.matrix_trace

private theorem two_mul_det_mem_traceSet {C : Set G𝔸} {x : G𝔸} {t : Z𝔸} {e : G𝔸}
    (he : e ∈ region K x C) (he' : cen K t * e ∈ region K x C) :
    2 * ((Matrix.GeneralLinearGroup.det t : (𝔸)ˣ) : 𝔸) ∈ traceSet K C := by
  obtain ⟨b₀, -, c₀, hc₀, rfl⟩ := Set.mem_image2.mp he
  obtain ⟨b, -, c, hc, hbc⟩ := Set.mem_image2.mp he'
  have hc' : c = (unipotentGL2 b * x)⁻¹ * (cen K t * (unipotentGL2 b₀ * x * c₀)) :=
    eq_inv_mul_of_mul_eq hbc
  have hM : c * c₀⁻¹ = x⁻¹ * ((unipotentGL2 b)⁻¹ * cen K t * unipotentGL2 b₀) * x := by
    rw [hc']
    group
  have hS : (unipotentGL2 b : G𝔸)⁻¹ * cen K t * unipotentGL2 b₀ = cen K t * unipotentGL2 (-b + b₀) := by
    rw [unip_inv, ← cen_mul_eq, mul_assoc, ← unipotentGL2_add]
  refine ⟨c * c₀⁻¹, Set.mem_image2_of_mem hc hc₀, ?_⟩
  beta_reduce
  rw [hM, trace_conj, hS, trace_cen_mul_unip]

private theorem exists_isCompact_confining {C : Set G𝔸} (hC : IsCompact C) :
    ∃ P : Set Z𝔸, IsCompact P ∧ ∀ (x : G𝔸) (t : Z𝔸) (e : G𝔸),
      e ∈ region K x C → cen K t * e ∈ region K x C → t ∈ P := by

  set half : Set 𝔸 := (fun y : 𝔸 => algebraMap K (𝔸) (2 : K)⁻¹ * y) '' traceSet K C with hhalf
  have hhalf_cpt : IsCompact half := (isCompact_traceSet K hC).image (continuous_const.mul continuous_id)
  have h2 : algebraMap K (𝔸) (2 : K)⁻¹ * 2 = 1 := by
    rw [show (2 : 𝔸) = algebraMap K (𝔸) 2 from (map_ofNat _ 2).symm, ← map_mul, inv_mul_cancel₀ two_ne_zero,
      map_one]
  have hmem : ∀ y : 𝔸, 2 * y ∈ traceSet K C → y ∈ half := fun y hy =>
    ⟨2 * y, hy, by beta_reduce; rw [← mul_assoc, h2, one_mul]⟩

  set A : Set (Matrix (Fin 1) (Fin 1) 𝔸) := {m | m 0 0 ∈ half} with hA
  have hA_cpt : IsCompact A := by
    have hpi : A = Set.pi Set.univ fun _ : Fin 1 => Set.pi Set.univ fun _ : Fin 1 => half := by
      ext m
      constructor
      · intro h i _ j _
        fin_cases i
        fin_cases j
        exact h
      · intro h
        exact h 0 (Set.mem_univ _) 0 (Set.mem_univ _)
    rw [hpi]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hhalf_cpt
  refine ⟨Units.embedProduct (Matrix (Fin 1) (Fin 1) 𝔸) ⁻¹' (A ×ˢ (MulOpposite.op '' A)),
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hA_cpt.prod (hA_cpt.image MulOpposite.continuous_op)),
    fun x t e he he' => ?_⟩
  have h₁ := two_mul_det_mem_traceSet K he he'
  have he'' : cen K t⁻¹ * (cen K t * e) ∈ region K x C := by
    rwa [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  have h₂ := two_mul_det_mem_traceSet K he' he''
  rw [Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod]
  refine ⟨?_, ⟨_, ?_, rfl⟩⟩
  · show (t : Matrix (Fin 1) (Fin 1) 𝔸) 0 0 ∈ half
    rw [← det_val]
    exact hmem _ h₁
  · show ((t⁻¹ : Z𝔸) : Matrix (Fin 1) (Fin 1) 𝔸) 0 0 ∈ half
    rw [← det_inv_val, ← map_inv]
    exact hmem _ h₂

private theorem exists_cmass_region_le {C : Set G𝔸} (hC : IsCompact C) :
    ∃ Mc : ℝ≥0∞, Mc < ⊤ ∧ ∀ (x : G𝔸) (γ : GL (Fin 2) K) (g : G𝔸), cmass K (region K x C) γ g ≤ Mc := by
  obtain ⟨P, hP, hPmem⟩ := exists_isCompact_confining K hC
  refine ⟨μZ P, hP.measure_lt_top, fun x γ g => ?_⟩
  unfold cmass
  rcases Set.eq_empty_or_nonempty {z : Z𝔸 | cen K z * globalPoints (𝓞 K) K γ * g ∈ region K x C} with hS | ⟨z₀, hz₀⟩
  · rw [hS, measure_empty]
    exact zero_le
  · calc μZ {z : Z𝔸 | cen K z * globalPoints (𝓞 K) K γ * g ∈ region K x C}
        ≤ μZ ((fun z : Z𝔸 => z₀⁻¹ * z) ⁻¹' P) := by
          refine measure_mono fun z hz => ?_
          rw [Set.mem_preimage]
          refine hPmem x (z₀⁻¹ * z) (cen K z₀ * globalPoints (𝓞 K) K γ * g) hz₀ ?_
          have : cen K (z₀⁻¹ * z) * (cen K z₀ * globalPoints (𝓞 K) K γ * g)
              = cen K z * globalPoints (𝓞 K) K γ * g := by
            rw [← mul_assoc, ← mul_assoc, ← map_mul, cen_mul_comm, mul_inv_cancel_left]
          rw [this]
          exact hz
      _ = μZ P := measure_preimage_mul μZ z₀⁻¹ P

section Local

variable {L : Type*} [NormedField L]

private def entryNormSq (M : Matrix (Fin 2) (Fin 2) L) : ℝ :=
  ‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 + ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2

private theorem entryNormSq_nonneg (M : Matrix (Fin 2) (Fin 2) L) : 0 ≤ entryNormSq M := by
  unfold entryNormSq
  positivity

private theorem row_mul_le (M N : Matrix (Fin 2) (Fin 2) L) (i : Fin 2) :
    ‖(M * N) i 0‖ ^ 2 + ‖(M * N) i 1‖ ^ 2 ≤ (‖M i 0‖ ^ 2 + ‖M i 1‖ ^ 2) * entryNormSq N := by
  have h : ∀ j : Fin 2, ‖(M * N) i j‖ ^ 2
      ≤ (‖M i 0‖ ^ 2 + ‖M i 1‖ ^ 2) * (‖N 0 j‖ ^ 2 + ‖N 1 j‖ ^ 2) := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    have h1 : ‖M i 0 * N 0 j + M i 1 * N 1 j‖ ≤ ‖M i 0‖ * ‖N 0 j‖ + ‖M i 1‖ * ‖N 1 j‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
    refine (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans ?_
    nlinarith [sq_nonneg (‖M i 0‖ * ‖N 1 j‖ - ‖M i 1‖ * ‖N 0 j‖), norm_nonneg (M i 0),
      norm_nonneg (M i 1), norm_nonneg (N 0 j), norm_nonneg (N 1 j)]
  calc ‖(M * N) i 0‖ ^ 2 + ‖(M * N) i 1‖ ^ 2
      ≤ (‖M i 0‖ ^ 2 + ‖M i 1‖ ^ 2) * (‖N 0 0‖ ^ 2 + ‖N 1 0‖ ^ 2)
        + (‖M i 0‖ ^ 2 + ‖M i 1‖ ^ 2) * (‖N 0 1‖ ^ 2 + ‖N 1 1‖ ^ 2) := add_le_add (h 0) (h 1)
    _ = (‖M i 0‖ ^ 2 + ‖M i 1‖ ^ 2) * entryNormSq N := by
        unfold entryNormSq
        ring

private def transFactor (k : GL (Fin 2) L) : ℝ :=
  entryNormSq (k : Matrix (Fin 2) (Fin 2) L) / ‖(k : Matrix (Fin 2) (Fin 2) L).det‖

private theorem aux_ineq {dg dk Rg Rgk E : ℝ} (hdk : 0 < dk) (hRg : 0 < Rg) (hRgk : 0 < Rgk)
    (hdg : 0 ≤ dg) (hle : Rgk ≤ Rg * E) : dg / Rg ≤ E / dk * (dg * dk / Rgk) := by
  rw [div_mul_div_comm, div_le_div_iff₀ hRg (mul_pos hdk hRgk)]
  have h := mul_le_mul_of_nonneg_left hle (mul_nonneg hdg hdk.le)
  calc dg * (dk * Rgk) = dg * dk * Rgk := by ring
    _ ≤ dg * dk * (Rg * E) := h
    _ = E * (dg * dk) * Rg := by ring

private theorem localHeight_le_transFactor_mul (g k : GL (Fin 2) L) :
    localHeight g ≤ transFactor k * localHeight (g * k) := by
  have hRg := rowNormSq_pos g
  have hRgk := rowNormSq_pos (g * k)
  rw [Units.val_mul] at hRgk
  have hdk : 0 < ‖(k : Matrix (Fin 2) (Fin 2) L).det‖ :=
    norm_pos_iff.mpr (Matrix.isUnits_det_units k).ne_zero
  unfold localHeight transFactor
  rw [Units.val_mul, Matrix.det_mul, norm_mul]
  exact aux_ineq hdk hRg hRgk (norm_nonneg _) (row_mul_le _ _ 1)

private theorem continuous_transFactor : Continuous (transFactor : GL (Fin 2) L → ℝ) := by
  have hc : ∀ i j : Fin 2, Continuous fun k : GL (Fin 2) L => ‖(k : Matrix (Fin 2) (Fin 2) L) i j‖ :=
    fun i j => (Units.continuous_val.matrix_elem i j).norm
  have hnum : Continuous fun k : GL (Fin 2) L => entryNormSq (k : Matrix (Fin 2) (Fin 2) L) := by
    unfold entryNormSq
    exact ((((hc 0 0).pow 2).add ((hc 0 1).pow 2)).add ((hc 1 0).pow 2)).add ((hc 1 1).pow 2)
  have hdet : Continuous fun k : GL (Fin 2) L => ‖(k : Matrix (Fin 2) (Fin 2) L).det‖ :=
    (Units.continuous_val.matrix_det).norm
  exact hnum.div hdet fun k => (norm_pos_iff.mpr (Matrix.isUnits_det_units k).ne_zero).ne'

private def ratioFactor (k : GL (Fin 2) L) : ℝ :=
  entryNormSq (k : Matrix (Fin 2) (Fin 2) L) * entryNormSq ((k⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)

private theorem continuous_ratioFactor : Continuous (ratioFactor : GL (Fin 2) L → ℝ) := by
  have hc : ∀ i j : Fin 2,
      Continuous fun k : GL (Fin 2) L => ‖(k : Matrix (Fin 2) (Fin 2) L) i j‖ ^ 2 :=
    fun i j => ((Units.continuous_val.matrix_elem i j).norm).pow 2
  have hc' : ∀ i j : Fin 2,
      Continuous fun k : GL (Fin 2) L => ‖((k⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j‖ ^ 2 :=
    fun i j => ((Units.continuous_coe_inv.matrix_elem i j).norm).pow 2
  unfold ratioFactor entryNormSq
  exact ((((hc 0 0).add (hc 0 1)).add (hc 1 0)).add (hc 1 1)).mul
    ((((hc' 0 0).add (hc' 0 1)).add (hc' 1 0)).add (hc' 1 1))

private theorem transFactor_nonneg (k : GL (Fin 2) L) : 0 ≤ transFactor k :=
  div_nonneg (entryNormSq_nonneg _) (norm_nonneg _)

private theorem ratioFactor_nonneg (k : GL (Fin 2) L) : 0 ≤ ratioFactor k :=
  mul_nonneg (entryNormSq_nonneg _) (entryNormSq_nonneg _)

private def ratio (g : GL (Fin 2) L) : ℝ :=
  topNormSq (g : Matrix (Fin 2) (Fin 2) L) / rowNormSq (g : Matrix (Fin 2) (Fin 2) L)

private theorem ratio_eq (g : GL (Fin 2) L) : ratio g = xWindowSq g + localHeight g ^ 2 := by
  simp only [ratio, xWindowSq]
  ring

private theorem topNormSq_nonneg' (M : Matrix (Fin 2) (Fin 2) L) : 0 ≤ topNormSq M := by
  unfold topNormSq
  positivity

private theorem ratio_nonneg (g : GL (Fin 2) L) : 0 ≤ ratio g :=
  div_nonneg (topNormSq_nonneg' _) (rowNormSq_pos g).le

private theorem ratio_mul_le (g k : GL (Fin 2) L) : ratio (g * k) ≤ ratioFactor k * ratio g := by
  have hrg := rowNormSq_pos g
  have hrgk := rowNormSq_pos (g * k)
  have htop : topNormSq ((g * k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) L) * entryNormSq (k : Matrix (Fin 2) (Fin 2) L) := by
    rw [Units.val_mul]
    exact row_mul_le _ _ 0
  have hrow : rowNormSq (g : Matrix (Fin 2) (Fin 2) L)
      ≤ rowNormSq ((g * k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
        * entryNormSq ((k⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
    have hg : (g : Matrix (Fin 2) (Fin 2) L) = ((g * k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
        * ((k⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) := by
      rw [← Units.val_mul, mul_inv_cancel_right]
    calc rowNormSq (g : Matrix (Fin 2) (Fin 2) L)
        = rowNormSq (((g * k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
            * ((k⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)) := by rw [← hg]
      _ ≤ _ := row_mul_le _ _ 1
  have hdiv : 0 ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) L) / rowNormSq (g : Matrix (Fin 2) (Fin 2) L) :=
    div_nonneg (topNormSq_nonneg' _) hrg.le
  unfold ratio ratioFactor
  rw [div_le_iff₀ hrgk]
  calc topNormSq ((g * k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) L) * entryNormSq (k : Matrix (Fin 2) (Fin 2) L) := htop
    _ = topNormSq (g : Matrix (Fin 2) (Fin 2) L) / rowNormSq (g : Matrix (Fin 2) (Fin 2) L)
          * rowNormSq (g : Matrix (Fin 2) (Fin 2) L) * entryNormSq (k : Matrix (Fin 2) (Fin 2) L) := by
        rw [div_mul_cancel₀ _ hrg.ne']
    _ ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) L) / rowNormSq (g : Matrix (Fin 2) (Fin 2) L)
          * (rowNormSq ((g * k : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
            * entryNormSq ((k⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L))
          * entryNormSq (k : Matrix (Fin 2) (Fin 2) L) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrow hdiv) (entryNormSq_nonneg _)
    _ = _ := by ring

private theorem ratio_unip_mul_le (b : L) (g : GL (Fin 2) L) :
    ratio (unipotentGL2 b * g) ≤ 2 * ratio g + 2 * ‖b‖ ^ 2 := by
  have hrg := rowNormSq_pos g
  have hrow : rowNormSq ((unipotentGL2 b * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = rowNormSq (g : Matrix (Fin 2) (Fin 2) L) := by
    rw [rowNormSq_scalar_entries_mul (z := (1 : L)) (by rw [unipotentGL2_coe]; rfl)
      (by rw [unipotentGL2_coe]; rfl) g, norm_one, one_pow, one_mul]
  have h0 : ∀ j : Fin 2, ((unipotentGL2 b * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 j
      = (g : Matrix (Fin 2) (Fin 2) L) 0 j + b * (g : Matrix (Fin 2) (Fin 2) L) 1 j := by
    intro j
    rw [Units.val_mul, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]
    simp
  have hsq : ∀ u v : L, ‖u + b * v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * (‖b‖ ^ 2 * ‖v‖ ^ 2) := by
    intro u v
    have h1 : ‖u + b * v‖ ≤ ‖u‖ + ‖b‖ * ‖v‖ := by
      rw [← norm_mul]
      exact norm_add_le _ _
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖u‖ - ‖b‖ * ‖v‖)]
  have htop : topNormSq ((unipotentGL2 b * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      ≤ 2 * topNormSq (g : Matrix (Fin 2) (Fin 2) L)
        + 2 * ‖b‖ ^ 2 * rowNormSq (g : Matrix (Fin 2) (Fin 2) L) := by
    unfold topNormSq rowNormSq
    rw [h0 0, h0 1]
    nlinarith [hsq ((g : Matrix (Fin 2) (Fin 2) L) 0 0) ((g : Matrix (Fin 2) (Fin 2) L) 1 0),
      hsq ((g : Matrix (Fin 2) (Fin 2) L) 0 1) ((g : Matrix (Fin 2) (Fin 2) L) 1 1)]
  unfold ratio
  rw [hrow, div_le_iff₀ hrg]
  calc topNormSq ((unipotentGL2 b * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) ≤ _ := htop
    _ = (2 * (topNormSq (g : Matrix (Fin 2) (Fin 2) L) / rowNormSq (g : Matrix (Fin 2) (Fin 2) L))
          + 2 * ‖b‖ ^ 2) * rowNormSq (g : Matrix (Fin 2) (Fin 2) L) := by
        field_simp

private theorem localHeight_unip_mul (b : L) (g : GL (Fin 2) L) :
    localHeight (unipotentGL2 b * g) = localHeight g := by
  rw [SiegelCoordinates.localHeight_upper_entries_mul (a := (1 : L)) (t := (1 : L)) one_ne_zero
    (by rw [unipotentGL2_coe]; rfl) (by rw [unipotentGL2_coe]; rfl) (by rw [unipotentGL2_coe]; rfl) g,
    norm_one, div_one, one_mul]

private theorem local_bounds {q β' r : L} (hr : r ≠ 0) (D S X Y M : GL (Fin 2) L)
    (hD00 : (D : Matrix (Fin 2) (Fin 2) L) 0 0 = q) (hD01 : (D : Matrix (Fin 2) (Fin 2) L) 0 1 = β')
    (hD10 : (D : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hD11 : (D : Matrix (Fin 2) (Fin 2) L) 1 1 = 1)
    (hS : ∀ i j, (S : Matrix (Fin 2) (Fin 2) L) i j = if i = j then r else 0)
    (hXY : localHeight X = localHeight Y) (h : D * Y = S * (X * M)) :
    ‖q‖ ≤ transFactor (M⁻¹ : GL (Fin 2) L)
      ∧ ‖β'‖ ^ 2 ≤ 2 * (ratioFactor M * ratio X) + 2 * ‖q‖ ^ 2 * ratio Y := by
  have hY := localHeight_pos Y
  have hSmul : localHeight (S * (X * M)) = localHeight (X * M) :=
    localHeight_scalar_entries_mul hr (hS 0 0) (by rw [hS]; rfl) (by rw [hS]; rfl) (hS 1 1) (X * M)
  constructor
  · have h1 : localHeight (D * Y) = ‖q‖ / ‖(1 : L)‖ * localHeight Y :=
      SiegelCoordinates.localHeight_upper_entries_mul one_ne_zero hD00 hD10 hD11 Y
    rw [norm_one, div_one] at h1
    have h2 : localHeight (X * M) ≤ transFactor (M⁻¹ : GL (Fin 2) L) * localHeight Y := by
      have := localHeight_le_transFactor_mul (X * M) M⁻¹
      rwa [mul_inv_cancel_right, hXY] at this
    have h3 : ‖q‖ * localHeight Y ≤ transFactor (M⁻¹ : GL (Fin 2) L) * localHeight Y := by
      rw [← h1, h, hSmul]
      exact h2
    exact le_of_mul_le_mul_right h3 hY
  ·
    set P : GL (Fin 2) L := X * M with hP
    have hmat : (D : Matrix (Fin 2) (Fin 2) L) * (Y : Matrix (Fin 2) (Fin 2) L)
        = (S : Matrix (Fin 2) (Fin 2) L) * (P : Matrix (Fin 2) (Fin 2) L) := by
      rw [← Units.val_mul, ← Units.val_mul, h]
    have hSP : ∀ i j : Fin 2, ((S : Matrix (Fin 2) (Fin 2) L) * (P : Matrix (Fin 2) (Fin 2) L)) i j
        = r * (P : Matrix (Fin 2) (Fin 2) L) i j := by
      intro i j
      rw [Matrix.mul_apply, Fin.sum_univ_two, hS, hS]
      fin_cases i <;> simp
    have htopEq : ∀ j : Fin 2, q * (Y : Matrix (Fin 2) (Fin 2) L) 0 j + β' * (Y : Matrix (Fin 2) (Fin 2) L) 1 j
        = r * (P : Matrix (Fin 2) (Fin 2) L) 0 j := by
      intro j
      rw [← hSP, ← hmat, Matrix.mul_apply, Fin.sum_univ_two, hD00, hD01]
    have hbotEq : ∀ j : Fin 2, (Y : Matrix (Fin 2) (Fin 2) L) 1 j = r * (P : Matrix (Fin 2) (Fin 2) L) 1 j := by
      intro j
      rw [← hSP, ← hmat, Matrix.mul_apply, Fin.sum_univ_two, hD10, hD11, zero_mul, one_mul, zero_add]

    have hrowY : rowNormSq (Y : Matrix (Fin 2) (Fin 2) L) = ‖r‖ ^ 2 * rowNormSq (P : Matrix (Fin 2) (Fin 2) L) := by
      unfold rowNormSq
      rw [hbotEq 0, hbotEq 1, norm_mul, norm_mul]
      ring

    have hper : ∀ j : Fin 2, ‖β'‖ ^ 2 * ‖(Y : Matrix (Fin 2) (Fin 2) L) 1 j‖ ^ 2
        ≤ 2 * (‖r‖ ^ 2 * ‖(P : Matrix (Fin 2) (Fin 2) L) 0 j‖ ^ 2)
          + 2 * (‖q‖ ^ 2 * ‖(Y : Matrix (Fin 2) (Fin 2) L) 0 j‖ ^ 2) := by
      intro j
      have e : β' * (Y : Matrix (Fin 2) (Fin 2) L) 1 j
          = r * (P : Matrix (Fin 2) (Fin 2) L) 0 j - q * (Y : Matrix (Fin 2) (Fin 2) L) 0 j := by
        rw [← htopEq j]
        ring
      have h1 : ‖β' * (Y : Matrix (Fin 2) (Fin 2) L) 1 j‖
          ≤ ‖r‖ * ‖(P : Matrix (Fin 2) (Fin 2) L) 0 j‖ + ‖q‖ * ‖(Y : Matrix (Fin 2) (Fin 2) L) 0 j‖ := by
        rw [e, ← norm_mul, ← norm_mul]
        exact norm_sub_le _ _
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      rw [norm_mul, mul_pow] at h2
      nlinarith [sq_nonneg (‖r‖ * ‖(P : Matrix (Fin 2) (Fin 2) L) 0 j‖ - ‖q‖ * ‖(Y : Matrix (Fin 2) (Fin 2) L) 0 j‖)]
    have hsum : ‖β'‖ ^ 2 * rowNormSq (Y : Matrix (Fin 2) (Fin 2) L)
        ≤ 2 * (‖r‖ ^ 2 * topNormSq (P : Matrix (Fin 2) (Fin 2) L))
          + 2 * (‖q‖ ^ 2 * topNormSq (Y : Matrix (Fin 2) (Fin 2) L)) := by
      unfold rowNormSq topNormSq
      nlinarith [hper 0, hper 1]
    have hrP := rowNormSq_pos P
    have hrY := rowNormSq_pos Y
    have hrn : (0 : ℝ) < ‖r‖ ^ 2 := by positivity

    have hβ : ‖β'‖ ^ 2 ≤ 2 * ratio P + 2 * ‖q‖ ^ 2 * ratio Y := by
      unfold ratio
      rw [hrowY] at hsum hrY
      have key : ‖β'‖ ^ 2 * (‖r‖ ^ 2 * rowNormSq (P : Matrix (Fin 2) (Fin 2) L))
          ≤ (2 * (topNormSq (P : Matrix (Fin 2) (Fin 2) L) / rowNormSq (P : Matrix (Fin 2) (Fin 2) L))
            + 2 * ‖q‖ ^ 2 * (topNormSq (Y : Matrix (Fin 2) (Fin 2) L)
              / (‖r‖ ^ 2 * rowNormSq (P : Matrix (Fin 2) (Fin 2) L))))
            * (‖r‖ ^ 2 * rowNormSq (P : Matrix (Fin 2) (Fin 2) L)) := by
        rw [add_mul, mul_assoc (2 * ‖q‖ ^ 2), div_mul_cancel₀ _ hrY.ne']
        calc ‖β'‖ ^ 2 * (‖r‖ ^ 2 * rowNormSq (P : Matrix (Fin 2) (Fin 2) L)) ≤ _ := hsum
          _ = _ := by
            field_simp
      rw [hrowY]
      exact le_of_mul_le_mul_right key hrY
    calc ‖β'‖ ^ 2 ≤ 2 * ratio P + 2 * ‖q‖ ^ 2 * ratio Y := hβ
      _ ≤ 2 * (ratioFactor M * ratio X) + 2 * ‖q‖ ^ 2 * ratio Y := by
        have := ratio_mul_le X M
        rw [← hP] at this
        linarith

end Local

private def diffSet (C : Set G𝔸) : Set G𝔸 :=
  Set.image2 (fun c c' : G𝔸 => c * c'⁻¹) C C

private theorem isCompact_diffSet {C : Set G𝔸} (hC : IsCompact C) : IsCompact (diffSet K C) := by
  unfold diffSet
  rw [← Set.image_prod]
  exact (hC.prod hC).image (continuous_fst.mul continuous_snd.inv)

private def Linked (C : Set G𝔸) (x : G𝔸) (δ : GL (Fin 2) K) : Prop :=
  ∃ (b b₀ : 𝔸) (ρ : Z𝔸) (M : G𝔸), b ∈ closure (adelicBox K) ∧ b₀ ∈ closure (adelicBox K) ∧ M ∈ diffSet K C ∧
    globalPoints (𝓞 K) K δ * (unipotentGL2 b₀ * x) = cen K ρ * (unipotentGL2 b * x) * M

private def upper (q β' : K) (hq : q ≠ 0) : GL (Fin 2) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![q, β'; 0, 1] (by rw [Matrix.det_fin_two_of]; simp [hq])

omit [NumberField K] in
private theorem upper_coe (q β' : K) (hq : q ≠ 0) :
    (upper K q β' hq : Matrix (Fin 2) (Fin 2) K) = !![q, β'; 0, 1] := rfl

omit [NumberField K] in
private theorem upper_apply_zero_zero (q β' : K) (hq : q ≠ 0) :
    (upper K q β' hq : Matrix (Fin 2) (Fin 2) K) 0 0 = q := rfl

omit [NumberField K] in
private theorem upper_apply_zero_one (q β' : K) (hq : q ≠ 0) :
    (upper K q β' hq : Matrix (Fin 2) (Fin 2) K) 0 1 = β' := rfl

omit [NumberField K] in
private theorem upper_apply_one_zero (q β' : K) (hq : q ≠ 0) :
    (upper K q β' hq : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := rfl

omit [NumberField K] in
private theorem upper_apply_one_one (q β' : K) (hq : q ≠ 0) :
    (upper K q β' hq : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := rfl

private theorem linked_of_mem {C : Set G𝔸} {x g : G𝔸} {γ γ₀ : GL (Fin 2) K} {z z₀ : Z𝔸}
    (h : cen K z * globalPoints (𝓞 K) K γ * g ∈ region K x C)
    (h₀ : cen K z₀ * globalPoints (𝓞 K) K γ₀ * g ∈ region K x C) :
    Linked K C x (γ * γ₀⁻¹) := by
  obtain ⟨b, hb, c, hc, hbc⟩ := Set.mem_image2.mp h
  obtain ⟨b₀, hb₀, c₀, hc₀, hbc₀⟩ := Set.mem_image2.mp h₀
  refine ⟨b, b₀, z₀ * z⁻¹, c * c₀⁻¹, hb, hb₀, Set.mem_image2_of_mem hc hc₀, ?_⟩
  have e₁ : globalPoints (𝓞 K) K γ * g = (cen K z)⁻¹ * (unipotentGL2 b * x * c) := by
    rw [hbc, mul_assoc (cen K z), inv_mul_cancel_left]
  have e₂ : globalPoints (𝓞 K) K γ₀ * g = (cen K z₀)⁻¹ * (unipotentGL2 b₀ * x * c₀) := by
    rw [hbc₀, mul_assoc (cen K z₀), inv_mul_cancel_left]
  have e₃ : globalPoints (𝓞 K) K γ * (globalPoints (𝓞 K) K γ₀)⁻¹
      = (globalPoints (𝓞 K) K γ * g) * (globalPoints (𝓞 K) K γ₀ * g)⁻¹ := by
    group
  have key : ∀ P : G𝔸, P * cen K z₀ = cen K z₀ * P := fun P => (cen_mul_eq K z₀ P).symm
  rw [map_mul, map_inv, e₃, e₁, e₂, map_mul, map_inv, mul_inv_rev, inv_inv,
    ← mul_assoc _ _ (cen K z₀), key]
  group

private theorem linked_of_scalar_mul {C : Set G𝔸} {x : G𝔸} {δ : GL (Fin 2) K} (s : Kˣ)
    (h : Linked K C x (Matrix.GeneralLinearGroup.scalar (Fin 2) s * δ)) : Linked K C x δ := by
  obtain ⟨b, b₀, ρ, M, hb, hb₀, hM, heq⟩ := h
  refine ⟨b, b₀, (Matrix.GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap K (𝔸)) s))⁻¹ * ρ, M,
    hb, hb₀, hM, ?_⟩
  rw [map_mul, globalPoints_scalar] at heq
  rw [map_mul, map_inv, cen_scalar]
  simp only [mul_assoc] at heq ⊢
  rw [← heq, inv_mul_cancel_left]

private def ac (w : InfinitePlace K) (g : G𝔸) : GL (Fin 2) w.Completion :=
  archComponent K w (glArch (𝓞 K) K g)

private theorem ac_mul (w : InfinitePlace K) (g h : G𝔸) : ac K w (g * h) = ac K w g * ac K w h := by
  unfold ac
  rw [map_mul, map_mul]

private theorem ac_apply (w : InfinitePlace K) (g : G𝔸) (i j : Fin 2) :
    (ac K w g : Matrix (Fin 2) (Fin 2) w.Completion) i j = ((g : Matrix (Fin 2) (Fin 2) 𝔸) i j).1 w :=
  rfl

private theorem ac_globalPoints_apply (w : InfinitePlace K) (γ : GL (Fin 2) K) (i j : Fin 2) :
    (ac K w (globalPoints (𝓞 K) K γ) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = ((γ : Matrix (Fin 2) (Fin 2) K) i j : w.Completion) :=
  rfl

private theorem ac_cen_apply (w : InfinitePlace K) (ρ : Z𝔸) (i j : Fin 2) :
    (ac K w (cen K ρ) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = if i = j then ((Matrix.GeneralLinearGroup.det ρ : (𝔸)ˣ) : 𝔸).1 w else 0 :=
  archComponent_centralScalar_apply K (Matrix.GeneralLinearGroup.det ρ) w i j

private theorem ac_unip (w : InfinitePlace K) (b : 𝔸) : ac K w (unipotentGL2 b) = unipotentGL2 (b.1 w) := by
  ext i j
  rw [ac_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

private theorem linked_arch {C : Set G𝔸} {x : G𝔸} {q β' : K} (hq : q ≠ 0)
    (h : Linked K C x (upper K q β' hq)) (w : InfinitePlace K) :
    ∃ M ∈ diffSet K C, ∃ b ∈ closure (adelicBox K), ∃ b₀ ∈ closure (adelicBox K),
      ‖(q : w.Completion)‖ ≤ transFactor ((ac K w M)⁻¹ : GL (Fin 2) w.Completion)
        ∧ ‖(β' : w.Completion)‖ ^ 2
          ≤ 2 * (ratioFactor (ac K w M) * (2 * ratio (ac K w x) + 2 * ‖b.1 w‖ ^ 2))
            + 2 * ‖(q : w.Completion)‖ ^ 2 * (2 * ratio (ac K w x) + 2 * ‖b₀.1 w‖ ^ 2) := by
  obtain ⟨b, b₀, ρ, M, hb, hb₀, hM, heq⟩ := h
  refine ⟨M, hM, b, hb, b₀, hb₀, ?_⟩
  have heqw := congrArg (ac K w) heq
  rw [ac_mul, ac_mul, ac_mul, ac_mul, ac_mul, ac_unip, ac_unip, mul_assoc] at heqw
  have hXY : localHeight (unipotentGL2 (b.1 w) * ac K w x) = localHeight (unipotentGL2 (b₀.1 w) * ac K w x) := by
    rw [localHeight_unip_mul, localHeight_unip_mul]
  obtain ⟨h1, h2⟩ := local_bounds (q := (q : w.Completion)) (β' := (β' : w.Completion))
    (fst_apply_ne_zero K (Matrix.GeneralLinearGroup.det ρ) w) _ _ _ _ _
    (ac_globalPoints_apply K w _ 0 0) (ac_globalPoints_apply K w _ 0 1)
    (by rw [ac_globalPoints_apply, upper_apply_one_zero]; simp; try rfl)
    (by rw [ac_globalPoints_apply, upper_apply_one_one]; simp; try rfl)
    (ac_cen_apply K w ρ) hXY heqw
  refine ⟨h1, h2.trans ?_⟩
  have hrf := ratioFactor_nonneg (ac K w M)
  have hb1 := mul_le_mul_of_nonneg_left (ratio_unip_mul_le (b.1 w) (ac K w x)) hrf
  have hq2 : (0 : ℝ) ≤ ‖(q : w.Completion)‖ ^ 2 := by positivity
  have hb2 := mul_le_mul_of_nonneg_left (ratio_unip_mul_le (b₀.1 w) (ac K w x)) hq2
  linarith

private theorem snd_mem_of_mem_closure_box {b : 𝔸} (hb : b ∈ closure (adelicBox K)) :
    b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  have hcl : IsClosed {y : 𝔸 | y.2 ∈ AdelicBox.integralFiniteAdeles (𝓞 K) K} :=
    (AdelicBox.isClosed_integralFiniteAdeles K).preimage continuous_snd
  exact closure_minimal (fun y hy => hy.2) hcl hb

private theorem glFin_unip_mem {b : 𝔸} (hb : b ∈ closure (adelicBox K)) :
    glFin (𝓞 K) K (unipotentGL2 b) ∈ finiteIntegralGL2 (𝓞 K) K := by
  have h2 := snd_mem_of_mem_closure_box K hb
  have hneg : (-b).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    rw [show (-b).2 = -b.2 from rfl, neg_eq_zero_sub]
    exact AdelicLevel.sub_mem_integralFiniteAdeles AdelicLevel.zero_mem_integralFiniteAdeles h2
  rw [mem_finiteIntegralGL2_iff, ← map_inv, unip_inv]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [glFin_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · exact AdelicLevel.one_mem_integralFiniteAdeles
    · exact h2
    · exact AdelicLevel.zero_mem_integralFiniteAdeles
    · exact AdelicLevel.one_mem_integralFiniteAdeles
  · rw [glFin_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · exact AdelicLevel.one_mem_integralFiniteAdeles
    · exact hneg
    · exact AdelicLevel.zero_mem_integralFiniteAdeles
    · exact AdelicLevel.one_mem_integralFiniteAdeles

private theorem isCompact_finiteIntegralGL2' :
    IsCompact (finiteIntegralGL2 (𝓞 K) K : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))) := by
  have : (finiteIntegralGL2 (𝓞 K) K : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)))
      = {g : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) |
          (∀ i j, (g : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j
            ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) ∧
          ∀ i j, ((g⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) :
            Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j
            ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K} :=
    Set.ext fun g => mem_finiteIntegralGL2_iff
  rw [this]
  exact isCompact_setOf_integral (𝓞 K) K

private def finBox (C : Set G𝔸) : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) :=
  Set.image2
    (fun (p : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)
        × GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))
      (m : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) => p.1 * m * p.2⁻¹)
    ((finiteIntegralGL2 (𝓞 K) K : Set _) ×ˢ (finiteIntegralGL2 (𝓞 K) K : Set _))
    (glFin (𝓞 K) K '' diffSet K C)

private theorem isCompact_finBox {C : Set G𝔸} (hC : IsCompact C) : IsCompact (finBox K C) := by
  unfold finBox
  rw [← Set.image_prod]
  refine (((isCompact_finiteIntegralGL2' K).prod (isCompact_finiteIntegralGL2' K)).prod
    ((isCompact_diffSet K hC).image (continuous_glFin (𝓞 K) K))).image ?_
  exact ((continuous_fst.comp continuous_fst).mul continuous_snd).mul
    (continuous_snd.comp continuous_fst).inv

private def finConf (C : Set G𝔸) (j : Fin 2) : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) :=
  (fun N : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) =>
    ((N⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) 1 1
      * (N : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) 0 j) '' finBox K C

private theorem isCompact_finConf {C : Set G𝔸} (hC : IsCompact C) (j : Fin 2) : IsCompact (finConf K C j) :=
  (isCompact_finBox K hC).image
    ((Units.continuous_coe_inv.matrix_elem 1 1).mul (Units.continuous_val.matrix_elem 0 j))

omit [NumberField K] in
private theorem upper_inv_apply_one_one {q β' : K} (hq : q ≠ 0) :
    (((upper K q β' hq)⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
  rw [Matrix.coe_units_inv, upper_coe, Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.det_fin_two_of,
    Matrix.smul_apply, Matrix.of_apply]
  simp [Ring.inverse_eq_inv', hq]

private theorem glFin_globalPoints_apply (γ : GL (Fin 2) K) (i j : Fin 2) :
    (glFin (𝓞 K) K (globalPoints (𝓞 K) K γ) : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j
      = algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) ((γ : Matrix (Fin 2) (Fin 2) K) i j) :=
  rfl

private theorem glFin_cen_apply (ρ : Z𝔸) (i j : Fin 2) :
    (glFin (𝓞 K) K (cen K ρ) : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j
      = if i = j then ((Matrix.GeneralLinearGroup.det ρ : (𝔸)ˣ) : 𝔸).2 else 0 := by
  rw [glFin_apply]
  show ((centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det ρ) : Matrix (Fin 2) (Fin 2) 𝔸) i j).2 = _
  rw [centralScalar_val, Matrix.diagonal_apply]
  split_ifs <;> rfl

private theorem linked_fin {C : Set G𝔸} {x : G𝔸} (hx : glFin (𝓞 K) K x ∈ finiteIntegralGL2 (𝓞 K) K)
    {q β' : K} (hq : q ≠ 0) (h : Linked K C x (upper K q β' hq)) :
    (algebraMap K (𝔸) q).2 ∈ finConf K C 0 ∧ (algebraMap K (𝔸) β').2 ∈ finConf K C 1 := by
  obtain ⟨b, b₀, ρ, M, hb, hb₀, hM, heq⟩ := h
  set δ := upper K q β' hq with hδ
  set N : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) :=
    (glFin (𝓞 K) K (unipotentGL2 b) * glFin (𝓞 K) K x) * glFin (𝓞 K) K M
      * (glFin (𝓞 K) K (unipotentGL2 b₀) * glFin (𝓞 K) K x)⁻¹ with hN
  have hNmem : N ∈ finBox K C := by
    refine Set.mem_image2_of_mem
      (a := (glFin (𝓞 K) K (unipotentGL2 b) * glFin (𝓞 K) K x, glFin (𝓞 K) K (unipotentGL2 b₀) * glFin (𝓞 K) K x))
      ⟨Subgroup.mul_mem _ (glFin_unip_mem K hb) hx, Subgroup.mul_mem _ (glFin_unip_mem K hb₀) hx⟩
      (Set.mem_image_of_mem _ hM)

  have hsplit : glFin (𝓞 K) K (globalPoints (𝓞 K) K δ) * (glFin (𝓞 K) K (unipotentGL2 b₀) * glFin (𝓞 K) K x)
      = glFin (𝓞 K) K (cen K ρ) * (glFin (𝓞 K) K (unipotentGL2 b) * glFin (𝓞 K) K x) * glFin (𝓞 K) K M := by
    have := congrArg (glFin (𝓞 K) K) heq
    simpa only [map_mul] using this
  have hfin : glFin (𝓞 K) K (globalPoints (𝓞 K) K δ) = glFin (𝓞 K) K (cen K ρ) * N := by
    rw [eq_mul_inv_of_mul_eq hsplit, hN]
    simp only [mul_assoc]
  set r : IsDedekindDomain.FiniteAdeleRing (𝓞 K) K := ((Matrix.GeneralLinearGroup.det ρ : (𝔸)ˣ) : 𝔸).2 with hr
  have hentry : ∀ i j : Fin 2,
      algebraMap K (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) ((δ : Matrix (Fin 2) (Fin 2) K) i j)
        = r * (N : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) i j := by
    intro i j
    rw [← glFin_globalPoints_apply, hfin, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, glFin_cen_apply,
      glFin_cen_apply]
    fin_cases i <;> simp [hr]

  have hinv : r = ((N⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) 1 1 := by
    have h1 : (glFin (𝓞 K) K (globalPoints (𝓞 K) K δ))⁻¹ = N⁻¹ * glFin (𝓞 K) K (cen K ρ⁻¹) := by
      rw [hfin, mul_inv_rev, map_inv, map_inv]
    have h2 := congrArg (fun g : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) =>
      (g : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) 1 1) h1
    rw [← map_inv, ← map_inv, glFin_globalPoints_apply, hδ, upper_inv_apply_one_one, map_one, Units.val_mul,
      Matrix.mul_apply, Fin.sum_univ_two, glFin_cen_apply, glFin_cen_apply,
      if_neg (show ¬ ((0 : Fin 2) = 1) by decide), if_pos rfl, mul_zero, zero_add] at h2

    have hrr : r * ((Matrix.GeneralLinearGroup.det ρ⁻¹ : (𝔸)ˣ) : 𝔸).2 = 1 := by
      rw [hr, map_inv]
      show (((Matrix.GeneralLinearGroup.det ρ : (𝔸)ˣ) : 𝔸)
        * (((Matrix.GeneralLinearGroup.det ρ)⁻¹ : (𝔸)ˣ) : 𝔸)).2 = 1
      rw [Units.mul_inv]
      rfl
    calc r = r * (((N⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) :
            Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)) 1 1
            * ((Matrix.GeneralLinearGroup.det ρ⁻¹ : (𝔸)ˣ) : 𝔸).2) := by rw [← h2, mul_one]
      _ = _ := by rw [mul_comm _ (((Matrix.GeneralLinearGroup.det ρ⁻¹ : (𝔸)ˣ) : 𝔸).2), ← mul_assoc, hrr, one_mul]
  refine ⟨⟨N, hNmem, ?_⟩, ⟨N, hNmem, ?_⟩⟩
  · beta_reduce
    rw [← hinv, ← hentry 0 0, hδ, upper_apply_zero_zero]
    rfl
  · beta_reduce
    rw [← hinv, ← hentry 0 1, hδ, upper_apply_zero_one]
    rfl

private theorem archHeight_eq_prod (g : G𝔸) :
    archHeight K (glArch (𝓞 K) K g) = ∏ w : InfinitePlace K, localHeight (ac K w g) ^ w.mult :=
  rfl

private theorem archHeight_unip_mul (b : 𝔸) (x : G𝔸) :
    archHeight K (glArch (𝓞 K) K (unipotentGL2 b * x)) = archHeight K (glArch (𝓞 K) K x) := by
  rw [archHeight_eq_prod, archHeight_eq_prod]
  exact Finset.prod_congr rfl fun w _ => by rw [ac_mul, ac_unip, localHeight_unip_mul]

private theorem exists_forall_linked_upper {C : Set G𝔸} (hC : IsCompact C) :
    ∃ T₁ : ℝ, ∀ x : G𝔸, glFin (𝓞 K) K x ∈ finiteIntegralGL2 (𝓞 K) K →
      T₁ < archHeight K (glArch (𝓞 K) K x) → ∀ δ : GL (Fin 2) K, Linked K C x δ →
        (δ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by
  obtain ⟨T₀, hT₀⟩ :=
    AutomorphicForm.WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem
      K (isCompact_diffSet K hC)
  refine ⟨T₀, fun x hx hT δ ⟨b, b₀, ρ, M, hb, hb₀, hM, heq⟩ => ?_⟩
  have hxb : glFin (𝓞 K) K (unipotentGL2 b * x) ∈ finiteIntegralGL2 (𝓞 K) K := by
    rw [map_mul]
    exact Subgroup.mul_mem _ (glFin_unip_mem K hb) hx
  have hxb₀ : glFin (𝓞 K) K (unipotentGL2 b₀ * x) ∈ finiteIntegralGL2 (𝓞 K) K := by
    rw [map_mul]
    exact Subgroup.mul_mem _ (glFin_unip_mem K hb₀) hx
  refine hT₀ (unipotentGL2 b * x) (unipotentGL2 b₀ * x) hxb hxb₀ (by rwa [archHeight_unip_mul])
    (by rwa [archHeight_unip_mul]) δ (Matrix.GeneralLinearGroup.det ρ⁻¹) ?_
  have h₁ : (unipotentGL2 b * x)⁻¹ * globalPoints (𝓞 K) K δ * (unipotentGL2 b₀ * x) = cen K ρ * M := by
    rw [mul_assoc, heq, cen_mul_eq, mul_assoc (unipotentGL2 b * x), inv_mul_cancel_left]
  have h₂ : (unipotentGL2 b * x)⁻¹ * globalPoints (𝓞 K) K δ * (unipotentGL2 b₀ * x)
      * centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det ρ⁻¹) = M := by
    rw [h₁, show centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det ρ⁻¹) = cen K ρ⁻¹ from rfl, cen_mul_eq,
      mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  rw [h₂]
  exact hM

private theorem exists_factor_bound {C : Set G𝔸} (hC : IsCompact C) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ M ∈ diffSet K C, ∀ w : InfinitePlace K,
      transFactor ((ac K w M)⁻¹ : GL (Fin 2) w.Completion) ≤ κ ∧ ratioFactor (ac K w M) ≤ κ := by
  have hcont : Continuous fun M : G𝔸 => ∑ w : InfinitePlace K,
      (transFactor ((ac K w M)⁻¹ : GL (Fin 2) w.Completion) + ratioFactor (ac K w M)) := by
    refine continuous_finsetSum _ fun w _ => ?_
    have hac : Continuous (ac K w) := (continuous_archComponent K w).comp (continuous_glArch (𝓞 K) K)
    exact (continuous_transFactor.comp hac.inv).add (continuous_ratioFactor.comp hac)
  obtain ⟨κ, hκ⟩ := (isCompact_diffSet K hC).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max κ 0, le_max_right _ _, fun M hM w => ?_⟩
  have hterm : ∀ v : InfinitePlace K,
      0 ≤ transFactor ((ac K v M)⁻¹ : GL (Fin 2) v.Completion) + ratioFactor (ac K v M) :=
    fun v => add_nonneg (transFactor_nonneg _) (ratioFactor_nonneg _)
  have hle : transFactor ((ac K w M)⁻¹ : GL (Fin 2) w.Completion) + ratioFactor (ac K w M) ≤ κ := by
    refine le_trans (Finset.single_le_sum (fun v _ => hterm v) (Finset.mem_univ w)) ?_
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hκ M hM))
  exact ⟨(le_add_of_nonneg_right (ratioFactor_nonneg _)).trans (hle.trans (le_max_left _ _)),
    (le_add_of_nonneg_left (transFactor_nonneg _)).trans (hle.trans (le_max_left _ _))⟩

private theorem exists_box_bound :
    ∃ rB : ℝ, 0 ≤ rB ∧ ∀ b ∈ closure (adelicBox K), ∀ w : InfinitePlace K, ‖b.1 w‖ ^ 2 ≤ rB := by
  have hcont : Continuous fun b : 𝔸 => ∑ w : InfinitePlace K, ‖b.1 w‖ ^ 2 :=
    continuous_finsetSum _ fun w _ => (((continuous_archEval K w).comp continuous_fst).norm).pow 2
  obtain ⟨r, hr⟩ := (isCompact_closure_box K).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max r 0, le_max_right _ _, fun b hb w => ?_⟩
  refine le_trans (Finset.single_le_sum (f := fun v : InfinitePlace K => ‖b.1 v‖ ^ 2)
    (fun v _ => by positivity) (Finset.mem_univ w)) ?_
  exact ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hr b hb))).trans (le_max_left _ _)

omit [NumberField K] in

private theorem diag_ne_zero {δ : GL (Fin 2) K} (h10 : (δ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    (δ : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 ∧ (δ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
  have hdet : (δ : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := (Matrix.isUnits_det_units δ).ne_zero
  rw [Matrix.det_fin_two, h10, mul_zero, sub_zero] at hdet
  exact ⟨left_ne_zero_of_mul hdet, right_ne_zero_of_mul hdet⟩

omit [NumberField K] in

private theorem eq_scalar_mul_upper {δ : GL (Fin 2) K} (h10 : (δ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) :
    δ = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 _ (diag_ne_zero K h10).2)
      * upper K ((δ : Matrix (Fin 2) (Fin 2) K) 0 0 / (δ : Matrix (Fin 2) (Fin 2) K) 1 1)
          ((δ : Matrix (Fin 2) (Fin 2) K) 0 1 / (δ : Matrix (Fin 2) (Fin 2) K) 1 1)
          (div_ne_zero (diag_ne_zero K h10).1 (diag_ne_zero K h10).2) := by
  obtain ⟨-, hd⟩ := diag_ne_zero K h10
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul]
  have hs : (Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 _ (diag_ne_zero K h10).2) :
      Matrix (Fin 2) (Fin 2) K) = Matrix.scalar (Fin 2) ((δ : Matrix (Fin 2) (Fin 2) K) 1 1) := rfl
  rw [hs, upper_coe, Matrix.scalar_apply, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [h10] <;> field_simp

private theorem finite_and_ncard_le {C : Set G𝔸} {x : G𝔸}
    (hupper : ∀ δ : GL (Fin 2) K, Linked K C x δ → (δ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (Qfin s : Finset K)
    (hQs : ∀ (q β' : K) (hq : q ≠ 0), Linked K C x (upper K q β' hq) →
      q ∈ Qfin ∧ β' ∈ s)
    (g : G𝔸) :
    {p : GL (Fin 2) K ⧸ ratCentre K | cmass K (region K x C) (Quotient.out p) g ≠ 0}.Finite ∧
      {p : GL (Fin 2) K ⧸ ratCentre K | cmass K (region K x C) (Quotient.out p) g ≠ 0}.ncard
        ≤ Qfin.card * s.card := by
  set Rel := {p : GL (Fin 2) K ⧸ ratCentre K | cmass K (region K x C) (Quotient.out p) g ≠ 0} with hRel
  rcases Rel.eq_empty_or_nonempty with hempty | ⟨p₀, hp₀⟩
  · rw [hempty]
    exact ⟨Set.finite_empty, by simp⟩

  obtain ⟨z₀, hz₀⟩ := nonempty_of_measure_ne_zero
    (show μZ {z : Z𝔸 | cen K z * globalPoints (𝓞 K) K (Quotient.out p₀) * g ∈ region K x C} ≠ 0 from hp₀)

  let δ : GL (Fin 2) K ⧸ ratCentre K → GL (Fin 2) K := fun p => Quotient.out p * (Quotient.out p₀)⁻¹
  let f : GL (Fin 2) K ⧸ ratCentre K → K × K := fun p =>
    ((δ p : Matrix (Fin 2) (Fin 2) K) 0 0 / (δ p : Matrix (Fin 2) (Fin 2) K) 1 1,
      (δ p : Matrix (Fin 2) (Fin 2) K) 0 1 / (δ p : Matrix (Fin 2) (Fin 2) K) 1 1)
  have hlink : ∀ p ∈ Rel, Linked K C x (δ p) := by
    intro p hp
    obtain ⟨z, hz⟩ := nonempty_of_measure_ne_zero
      (show μZ {z : Z𝔸 | cen K z * globalPoints (𝓞 K) K (Quotient.out p) * g ∈ region K x C} ≠ 0 from hp)
    exact linked_of_mem K hz hz₀
  have hmaps : ∀ p ∈ Rel, f p ∈ ((Qfin ×ˢ s : Finset (K × K)) : Set (K × K)) := by
    intro p hp
    have h10 := hupper _ (hlink p hp)
    have hnorm := eq_scalar_mul_upper K h10
    have hl := hlink p hp
    rw [hnorm] at hl
    obtain ⟨hq, hβ⟩ := hQs _ _ _ (linked_of_scalar_mul K _ hl)
    exact Finset.mem_coe.mpr (Finset.mem_product.mpr ⟨hq, hβ⟩)
  have hinj : Set.InjOn f Rel := by
    intro p hp p' hp' hf
    have h10 := hupper _ (hlink p hp)
    have h10' := hupper _ (hlink p' hp')
    obtain ⟨-, hd⟩ := diag_ne_zero K h10
    obtain ⟨-, hd'⟩ := diag_ne_zero K h10'
    have hn := eq_scalar_mul_upper K h10
    have hn' := eq_scalar_mul_upper K h10'
    have hfst : (δ p : Matrix (Fin 2) (Fin 2) K) 0 0 / (δ p : Matrix (Fin 2) (Fin 2) K) 1 1
        = (δ p' : Matrix (Fin 2) (Fin 2) K) 0 0 / (δ p' : Matrix (Fin 2) (Fin 2) K) 1 1 := congrArg Prod.fst hf
    have hsnd : (δ p : Matrix (Fin 2) (Fin 2) K) 0 1 / (δ p : Matrix (Fin 2) (Fin 2) K) 1 1
        = (δ p' : Matrix (Fin 2) (Fin 2) K) 0 1 / (δ p' : Matrix (Fin 2) (Fin 2) K) 1 1 := congrArg Prod.snd hf

    set t : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Units.mk0 _ hd' * (Units.mk0 _ hd)⁻¹) with ht
    have hδ : δ p' = t * δ p := by
      rw [ht, map_mul, map_inv, mul_assoc]
      conv_rhs => arg 2; arg 2; rw [hn]
      rw [inv_mul_cancel_left]
      conv_lhs => rw [hn']
      congr 1
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      fin_cases i <;> fin_cases j
      · exact hfst.symm
      · exact hsnd.symm
      · rfl
      · rfl
    have ht_mem : t ∈ ratCentre K := ⟨_, rfl⟩
    have hcomm : ∀ γ : GL (Fin 2) K, t * γ = γ * t := fun γ =>
      Units.ext (Matrix.scalar_commute ((Units.mk0 _ hd' * (Units.mk0 _ hd)⁻¹ : Kˣ) : K)
        (fun r' => Commute.all _ r') (γ : Matrix (Fin 2) (Fin 2) K)).eq

    have hout : Quotient.out p' = Quotient.out p * t := by
      have h : Quotient.out p' * (Quotient.out p₀)⁻¹ = t * (Quotient.out p * (Quotient.out p₀)⁻¹) := hδ
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, inv_mul_cancel_right] at h
      rw [h, hcomm]
    calc p = QuotientGroup.mk (Quotient.out p) := (QuotientGroup.out_eq' p).symm
      _ = QuotientGroup.mk (Quotient.out p * t) := (QuotientGroup.mk_mul_of_mem _ ht_mem).symm
      _ = QuotientGroup.mk (Quotient.out p') := by rw [hout]
      _ = p' := QuotientGroup.out_eq' p'
  have hfin : Rel.Finite :=
    Set.Finite.of_finite_image ((Qfin ×ˢ s).finite_toSet.subset (Set.image_subset_iff.mpr hmaps)) hinj
  refine ⟨hfin, ?_⟩
  calc Rel.ncard ≤ ((Qfin ×ˢ s : Finset (K × K)) : Set (K × K)).ncard :=
        Set.ncard_le_ncard_of_injOn f hmaps hinj (Qfin ×ˢ s).finite_toSet
    _ = Qfin.card * s.card := by rw [Set.ncard_coe_finset, Finset.card_product]

private theorem exists_prod_max_pow_le {c' : ℝ} (hc' : 0 < c') {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    ∃ (κ₀ : ℝ) (A : ℕ), 0 ≤ κ₀ ∧ ∀ x : G𝔸, (∀ w : InfinitePlace K, c' ≤ localHeight (ac K w x)) →
      1 ≤ archHeight K (glArch (𝓞 K) K x) →
        ∏ w : InfinitePlace K, max 1 (r₁ + r₂ * localHeight (ac K w x) ^ 2) ^ w.mult
          ≤ κ₀ * archHeight K (glArch (𝓞 K) K x) ^ A := by
  set d : ℕ := ∑ w : InfinitePlace K, w.mult with hd
  set cm : ℝ := min 1 c' with hcm
  have hcm0 : 0 < cm := lt_min one_pos hc'
  have hcm1 : cm ≤ 1 := min_le_left _ _
  have hcd0 : 0 < cm ^ d := pow_pos hcm0 d
  have hcd1 : cm ^ d ≤ 1 := pow_le_one₀ hcm0.le hcm1
  refine ⟨((1 + r₁ + r₂) / (cm ^ d) ^ 2) ^ d, 2 * d, by positivity, fun x hfloor hH => ?_⟩
  set H : ℝ := archHeight K (glArch (𝓞 K) K x) with hHdef

  have hloc : ∀ w : InfinitePlace K, localHeight (ac K w x) ^ w.mult ≤ H / cm ^ d := by
    intro w
    classical
    rw [le_div_iff₀ hcd0, hHdef, archHeight_eq_prod, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (localHeight_pos _).le _)
    calc cm ^ d ≤ cm ^ ∑ v ∈ Finset.univ.erase w, v.mult :=
          pow_le_pow_of_le_one hcm0.le hcm1 (Finset.sum_le_sum_of_subset (Finset.erase_subset w Finset.univ))
      _ = ∏ v ∈ Finset.univ.erase w, cm ^ v.mult := (Finset.prod_pow_eq_pow_sum _ _ _).symm
      _ ≤ ∏ v ∈ Finset.univ.erase w, localHeight (ac K v x) ^ v.mult :=
          Finset.prod_le_prod (fun v _ => pow_nonneg hcm0.le _) fun v _ =>
            pow_le_pow_left₀ hcm0.le ((min_le_right _ _).trans (hfloor v)) _
  have hHc1 : 1 ≤ H / cm ^ d := by
    rw [le_div_iff₀ hcd0, one_mul]
    exact hcd1.trans hH

  have hsq : ∀ w : InfinitePlace K, localHeight (ac K w x) ^ 2 ≤ (H / cm ^ d) ^ 2 := by
    intro w
    have hpos := localHeight_pos (ac K w x)
    rcases le_or_gt (localHeight (ac K w x)) 1 with h1 | h1
    · calc localHeight (ac K w x) ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hpos.le h1 2
        _ ≤ (H / cm ^ d) ^ 2 := pow_le_pow_left₀ zero_le_one hHc1 2
    · have h2 : localHeight (ac K w x) ≤ localHeight (ac K w x) ^ w.mult :=
        le_self_pow₀ h1.le (InfinitePlace.mult_ne_zero)
      exact pow_le_pow_left₀ hpos.le (h2.trans (hloc w)) 2
  have hmax : ∀ w : InfinitePlace K,
      max 1 (r₁ + r₂ * localHeight (ac K w x) ^ 2) ≤ (1 + r₁ + r₂) * (H / cm ^ d) ^ 2 := by
    intro w
    have hq := hsq w
    have hHc2 : 1 ≤ (H / cm ^ d) ^ 2 := one_le_pow₀ hHc1
    refine max_le ?_ ?_
    · nlinarith
    · nlinarith [mul_le_mul_of_nonneg_left hq hr₂, mul_le_mul_of_nonneg_left hHc2 hr₁]
  calc ∏ w : InfinitePlace K, max 1 (r₁ + r₂ * localHeight (ac K w x) ^ 2) ^ w.mult
      ≤ ∏ w : InfinitePlace K, ((1 + r₁ + r₂) * (H / cm ^ d) ^ 2) ^ w.mult :=
        Finset.prod_le_prod (fun w _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _) fun w _ =>
          pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (hmax w) _
    _ = ((1 + r₁ + r₂) * (H / cm ^ d) ^ 2) ^ d := Finset.prod_pow_eq_pow_sum _ _ _
    _ = ((1 + r₁ + r₂) / (cm ^ d) ^ 2) ^ d * H ^ (2 * d) := by
        rw [pow_mul, ← mul_pow, div_pow]
        congr 1
        ring

private theorem radius_arith {Q B RF R b b₀ κ u' rB H : ℝ} (hκ0 : 0 ≤ κ) (hQ : 0 ≤ Q) (hR : 0 ≤ R)
    (hb0 : 0 ≤ b) (hb₀0 : 0 ≤ b₀) (hQκ : Q ≤ κ) (hRFκ : RF ≤ κ) (hratio : R ≤ u' ^ 2 + H ^ 2)
    (hb : b ≤ rB) (hb₀ : b₀ ≤ rB) (hβ : B ^ 2 ≤ 2 * (RF * (2 * R + 2 * b)) + 2 * Q ^ 2 * (2 * R + 2 * b₀)) :
    B ≤ (2 * κ + 2 * κ ^ 2) * (2 * u' ^ 2 + 2 * rB) + 1 + 2 * (2 * κ + 2 * κ ^ 2) * H ^ 2 := by
  set X : ℝ := 2 * u' ^ 2 + 2 * rB + 2 * H ^ 2 with hX
  have hin : 2 * R + 2 * b ≤ X := by rw [hX]; linarith
  have hin₀ : 2 * R + 2 * b₀ ≤ X := by rw [hX]; linarith
  have hnn : 0 ≤ 2 * R + 2 * b := by positivity
  have hnn₀ : 0 ≤ 2 * R + 2 * b₀ := by positivity
  have hQsq : Q ^ 2 ≤ κ ^ 2 := pow_le_pow_left₀ hQ hQκ 2
  have h1 : RF * (2 * R + 2 * b) ≤ κ * X := mul_le_mul hRFκ hin hnn hκ0
  have h2 : Q ^ 2 * (2 * R + 2 * b₀) ≤ κ ^ 2 * X := mul_le_mul hQsq hin₀ hnn₀ (by positivity)
  have hβX : B ^ 2 ≤ (2 * κ + 2 * κ ^ 2) * X := by linarith [h1, h2, hβ]
  have hBle : B ≤ B ^ 2 + 1 := by nlinarith [sq_nonneg (B - 1 / 2)]
  have hexp : (2 * κ + 2 * κ ^ 2) * X
      = (2 * κ + 2 * κ ^ 2) * (2 * u' ^ 2 + 2 * rB) + 2 * (2 * κ + 2 * κ ^ 2) * H ^ 2 := by
    rw [hX]; ring
  linarith [hβX, hBle, hexp]

private theorem FIBRE {C : Set G𝔸} (hC : IsCompact C) (c' u' d₁' d₂' : ℝ) (hc' : 0 < c') :
    ∃ (T₁ : ℝ) (A : ℕ) (Mfib : ℝ), ∀ x ∈ centreCutSiegelSet K c' u' d₁' d₂',
      T₁ < archHeight K (glArch (𝓞 K) K x) → ∀ g : G𝔸,
        fibre K (region K x C) g ≤ ENNReal.ofReal (Mfib * archHeight K (glArch (𝓞 K) K x) ^ A) := by
  obtain ⟨T₀, hT₀⟩ := exists_forall_linked_upper K hC
  obtain ⟨κ, hκ0, hκ⟩ := exists_factor_bound K hC
  obtain ⟨rB, hrB0, hrB⟩ := exists_box_bound K
  obtain ⟨Aq, hAq, hAqmem⟩ := exists_isCompact_adeles K κ (isCompact_finConf K hC 0)
  have hQfin := NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact K hAq
  set Qfin : Finset K := hQfin.toFinset with hQfin_def
  obtain ⟨Mb, hMb⟩ :=
    NumberField.AdeleRing.exists_finset_forall_mem_and_card_le_mul_prod_pow_of_isCompact K (isCompact_finConf K hC 1)
  obtain ⟨Mc, hMc_top, hMc⟩ := exists_cmass_region_le K hC

  set cκ : ℝ := 2 * κ + 2 * κ ^ 2 with hcκ
  have hcκ0 : 0 ≤ cκ := by positivity
  set r₁ : ℝ := cκ * (2 * u' ^ 2 + 2 * rB) + 1 with hr₁
  set r₂ : ℝ := 2 * cκ with hr₂
  have hr₁0 : 0 ≤ r₁ := by positivity
  have hr₂0 : 0 ≤ r₂ := by positivity
  obtain ⟨κ₀, A, hκ₀, hpoly⟩ := exists_prod_max_pow_le K hc' hr₁0 hr₂0
  refine ⟨max T₀ 1, A, (Qfin.card : ℝ) * max Mb 0 * κ₀ * Mc.toReal, fun x hxS hT g => ?_⟩
  obtain ⟨hxint, hxfloor, hxwin, -⟩ := mem_centreCutSiegelSet_iff.mp hxS
  have hT₀x : T₀ < archHeight K (glArch (𝓞 K) K x) := (le_max_left _ _).trans_lt hT
  have hH1 : 1 ≤ archHeight K (glArch (𝓞 K) K x) := ((le_max_right _ _).trans_lt hT).le
  have hupper := hT₀ x hxint hT₀x

  obtain ⟨s, hs_mem, hs_card⟩ := hMb 0 fun w => r₁ + r₂ * localHeight (ac K w x) ^ 2

  have hQs : ∀ (q β' : K) (hq : q ≠ 0), Linked K C x (upper K q β' hq) →
      q ∈ Qfin ∧ β' ∈ s := by
    intro q β' hq hl
    obtain ⟨hqfin, hβfin⟩ := linked_fin K hxint hq hl

    have harch : ∀ w : InfinitePlace K,
        ‖(q : w.Completion)‖ ≤ κ ∧ ‖(β' : w.Completion)‖ ≤ r₁ + r₂ * localHeight (ac K w x) ^ 2 := by
      intro w
      obtain ⟨M, hM, b, hb, b₀, hb₀, hqw, hβw⟩ := linked_arch K hq hl w
      obtain ⟨hMt, hMr⟩ := hκ M hM w
      have hratio : ratio (ac K w x) ≤ u' ^ 2 + localHeight (ac K w x) ^ 2 := by
        rw [ratio_eq]
        exact add_le_add (hxwin w) le_rfl
      refine ⟨hqw.trans hMt, ?_⟩
      rw [hr₁, hr₂, hcκ]
      exact radius_arith hκ0 (norm_nonneg _) (ratio_nonneg _) (by positivity) (by positivity)
        (hqw.trans hMt) hMr hratio (hrB b hb w) (hrB b₀ hb₀ w) hβw
    constructor
    · rw [hQfin_def, Set.Finite.mem_toFinset]
      exact hAqmem _ (fun w => (harch w).1) hqfin
    · refine hs_mem β' ?_ fun w => ?_
      · rw [sub_zero]
        exact hβfin
      · rw [sub_zero]
        exact (harch w).2
  obtain ⟨hfin, hcard⟩ := finite_and_ncard_le K hupper Qfin s hQs g

  have hsum : fibre K (region K x C) g ≤ (hfin.toFinset.card : ℝ≥0∞) * Mc := by
    unfold fibre
    rw [tsum_eq_sum (s := hfin.toFinset) fun p hp => by simpa using hp]
    calc ∑ p ∈ hfin.toFinset, cmass K (region K x C) (Quotient.out p) g
        ≤ ∑ _p ∈ hfin.toFinset, Mc := Finset.sum_le_sum fun p _ => hMc x _ g
      _ = (hfin.toFinset.card : ℝ≥0∞) * Mc := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcount : (hfin.toFinset.card : ℝ) ≤ (Qfin.card : ℝ) * (max Mb 0 * (κ₀ * archHeight K (glArch (𝓞 K) K x) ^ A)) := by
    have h1 : (hfin.toFinset.card : ℝ) ≤ (Qfin.card : ℝ) * (s.card : ℝ) := by
      rw [← Set.ncard_eq_toFinset_card _ hfin]
      exact_mod_cast hcard
    have h2 : (s.card : ℝ) ≤ max Mb 0 * (κ₀ * archHeight K (glArch (𝓞 K) K x) ^ A) := by
      refine hs_card.trans ?_
      have hprod := hpoly x (fun w => hxfloor w) hH1
      have hprod0 : 0 ≤ ∏ w : InfinitePlace K, max 1 (r₁ + r₂ * localHeight (ac K w x) ^ 2) ^ w.mult :=
        Finset.prod_nonneg fun w _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
      calc Mb * ∏ w : InfinitePlace K, max 1 (r₁ + r₂ * localHeight (ac K w x) ^ 2) ^ w.mult
          ≤ max Mb 0 * ∏ w : InfinitePlace K, max 1 (r₁ + r₂ * localHeight (ac K w x) ^ 2) ^ w.mult :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hprod0
        _ ≤ max Mb 0 * (κ₀ * archHeight K (glArch (𝓞 K) K x) ^ A) :=
            mul_le_mul_of_nonneg_left hprod (le_max_right _ _)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))
  have hconv : (hfin.toFinset.card : ℝ≥0∞) * Mc = ENNReal.ofReal ((hfin.toFinset.card : ℝ) * Mc.toReal) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_toReal hMc_top.ne]
  refine hsum.trans ?_
  rw [hconv]
  refine ENNReal.ofReal_le_ofReal ?_
  have hMcR : 0 ≤ Mc.toReal := ENNReal.toReal_nonneg
  calc (hfin.toFinset.card : ℝ) * Mc.toReal
      ≤ (Qfin.card : ℝ) * (max Mb 0 * (κ₀ * archHeight K (glArch (𝓞 K) K x) ^ A)) * Mc.toReal :=
        mul_le_mul_of_nonneg_right hcount hMcR
    _ = (Qfin.card : ℝ) * max Mb 0 * κ₀ * Mc.toReal * archHeight K (glArch (𝓞 K) K x) ^ A := by ring

private theorem X1 (χ : (⊤ : Subgroup (𝔸)ˣ) →* ℂˣ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsLsXiFunction (𝓞 K) K ⊤ χ φ) (hcont : Continuous φ) (hne : ∃ g, φ g ≠ 0) :
    (∀ u : Kˣ, χ ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u, Subgroup.mem_top _⟩ = 1) ∧
      Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => χ ⟨z, Subgroup.mem_top z⟩ :=
  AutomorphicForm.isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous K χ φ hφ hcont hne

section Instances

private scoped instance countable_numberField : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private scoped instance countable_ringOfIntegers : Countable (𝓞 K) :=
  (NumberField.RingOfIntegers.coe_injective (K := K)).countable

private scoped instance countable_ideal : Countable (Ideal (𝓞 K)) := by
  refine (Function.Surjective.countable (f := fun s : Finset (𝓞 K) => Ideal.span (s : Set (𝓞 K))) ?_)
  intro I
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  exact ⟨s, hs⟩

private scoped instance countable_heightOneSpectrum : Countable (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :=
  Function.Injective.countable (f := IsDedekindDomain.HeightOneSpectrum.asIdeal)
    fun _ _ h => IsDedekindDomain.HeightOneSpectrum.ext h

open scoped RestrictedProduct in
private scoped instance secondCountable_finiteAdeleRing :
    SecondCountableTopology (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) := by
  haveI : SecondCountableTopology
      (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]) :=
    RestrictedProduct.secondCountableTopology fun v => Valued.isOpen_valuationSubring _
  exact inferInstanceAs <| SecondCountableTopology <|
    Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]

private scoped instance secondCountable_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ v : InfinitePlace K, SecondCountableTopology v.Completion := by
    intro v
    haveI : Countable (WithAbs v.1) := (WithAbs.equiv v.1).toEquiv.injective.countable
    haveI : SecondCountableTopology v.1.Completion := UniformSpace.secondCountable_of_separable _
    exact (NumberField.InfinitePlace.Completion.isometry_toCompletion (v := v)).isEmbedding.secondCountableTopology
  exact inferInstanceAs <| SecondCountableTopology <| (v : InfinitePlace K) → v.Completion

private scoped instance secondCountable_adeleRing : SecondCountableTopology (𝔸) :=
  inferInstanceAs <| SecondCountableTopology (InfiniteAdeleRing K × IsDedekindDomain.FiniteAdeleRing (𝓞 K) K)

private scoped instance secondCountable_gl {n : ℕ} : SecondCountableTopology (GL (Fin n) (𝔸)) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (𝔸)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → 𝔸))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (𝔸))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

private scoped instance countable_cosets : Countable (GL (Fin 2) K ⧸ ratCentre K) := by
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (GL (Fin 2) K) := Units.val_injective.countable
  exact QuotientGroup.mk_surjective.countable

end Instances

private theorem continuous_cen : Continuous (cen K) := by
  have hdet : Continuous (Matrix.GeneralLinearGroup.det : Z𝔸 → (𝔸)ˣ) :=
    Units.continuous_iff.mpr ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩
  have hsc : Continuous (centralScalar (𝓞 K) K) := by
    refine Units.continuous_iff.mpr ⟨?_, ?_⟩
    · show Continuous fun w : (𝔸)ˣ => ((centralScalar (𝓞 K) K w : G𝔸) : Matrix (Fin 2) (Fin 2) 𝔸)
      simp only [centralScalar_val]
      exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
    · show Continuous fun w : (𝔸)ˣ => (((centralScalar (𝓞 K) K w)⁻¹ : G𝔸) : Matrix (Fin 2) (Fin 2) 𝔸)
      simp only [← map_inv, centralScalar_val]
      exact (continuous_pi fun _ => Units.continuous_coe_inv).matrix_diagonal
  exact hsc.comp hdet

private theorem muZ_inv (A : Set Z𝔸) : μZ A⁻¹ = μZ A := by
  letI : CommGroup Z𝔸 :=
    { (inferInstance : Group Z𝔸) with
      mul_comm := fun a b => Units.ext (by
        ext i j
        rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_one, Fin.sum_univ_one]
        rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
        exact mul_comm _ _) }
  haveI : (μZ).Regular := by
    unfold adelicGLHaar
    infer_instance
  exact Measure.measure_inv μZ A

omit [NumberField K] in
private theorem ratCentre_mul_comm {s : GL (Fin 2) K} (hs : s ∈ ratCentre K) (γ : GL (Fin 2) K) :
    γ * s = s * γ := by
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp hs
  exact Units.ext (Matrix.scalar_commute ((k : Kˣ) : K) (fun r' => Commute.all _ r') (γ : Matrix (Fin 2) (Fin 2) K)).eq.symm

private def cosetInv (p : GL (Fin 2) K ⧸ ratCentre K) : GL (Fin 2) K ⧸ ratCentre K :=
  QuotientGroup.mk (Quotient.out p)⁻¹

omit [NumberField K] in
private theorem cosetInv_involutive : Function.Involutive (cosetInv K) := by
  intro p
  unfold cosetInv
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (ratCentre K) (Quotient.out p)⁻¹
  rw [hh, mul_inv_rev, inv_inv, ← ratCentre_mul_comm K (inv_mem h.2), QuotientGroup.mk_mul_of_mem _ (inv_mem h.2),
    QuotientGroup.out_eq']

private theorem cmass_out_cosetInv (E : Set G𝔸) (p : GL (Fin 2) K ⧸ ratCentre K) (g : G𝔸) :
    cmass K E (Quotient.out (cosetInv K p)) g = cmass K E (Quotient.out p)⁻¹ g := by
  unfold cosetInv
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (ratCentre K) (Quotient.out p)⁻¹
  rw [hh, cmass_mul_ratCentre K E _ h.2]

private theorem tsum_cmass_inv (E : Set G𝔸) (g : G𝔸) :
    ∑' p : GL (Fin 2) K ⧸ ratCentre K, cmass K E (Quotient.out p)⁻¹ g = fibre K E g := by
  unfold fibre
  rw [← (Equiv.mk (cosetInv K) (cosetInv K) (cosetInv_involutive K) (cosetInv_involutive K)).tsum_eq
    (fun q => cmass K E (Quotient.out q) g)]
  exact tsum_congr fun p => (cmass_out_cosetInv K E p g).symm

private theorem cmass_inv (E : Set G𝔸) (γ : GL (Fin 2) K) (y : G𝔸) :
    μZ ((fun z : Z𝔸 => (cen K z * globalPoints (𝓞 K) K γ)⁻¹ * y) ⁻¹' E) = cmass K E γ⁻¹ y := by
  unfold cmass
  rw [← muZ_inv K {z : Z𝔸 | cen K z * globalPoints (𝓞 K) K γ⁻¹ * y ∈ E}]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_inv, Set.mem_setOf_eq, mul_inv_rev]
  rw [← map_inv (cen K) z, ← map_inv (globalPoints (𝓞 K) K) γ, cen_mul_eq]

private theorem measurable_cmass {E : Set G𝔸} (hE : MeasurableSet E) (γ : GL (Fin 2) K) :
    Measurable fun y : G𝔸 => cmass K E γ y := by
  have hS : MeasurableSet ((fun q : Z𝔸 × G𝔸 => cen K q.1 * globalPoints (𝓞 K) K γ * q.2) ⁻¹' E) :=
    ((((continuous_cen K).comp continuous_fst).mul continuous_const).mul continuous_snd).measurable hE
  have h := measurable_measure_prodMk_right (μ := μZ) hS
  have hfun : (fun y : G𝔸 => μZ ((fun z : Z𝔸 => (z, y)) ⁻¹'
      ((fun q : Z𝔸 × G𝔸 => cen K q.1 * globalPoints (𝓞 K) K γ * q.2) ⁻¹' E))) = fun y => cmass K E γ y := by
    funext y
    unfold cmass
    congr 1
  exact hfun ▸ h

private theorem lintegral_indicator_one_comp {E : Set G𝔸} (hE : MeasurableSet E) {f : Z𝔸 → G𝔸}
    (hf : Continuous f) :
    ∫⁻ z, E.indicator (1 : G𝔸 → ℝ≥0∞) (f z) ∂μZ = μZ (f ⁻¹' E) := by
  rw [← lintegral_indicator_one (hf.measurable hE)]
  exact lintegral_congr fun z => by classical simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]

private theorem cmass_eq_lintegral {D : Set G𝔸} (hD : MeasurableSet D) (γ : GL (Fin 2) K) (y : G𝔸) :
    cmass K D γ y = ∫⁻ z, D.indicator (1 : G𝔸 → ℝ≥0∞) (cen K z * globalPoints (𝓞 K) K γ * y) ∂μZ := by
  unfold cmass
  exact (lintegral_indicator_one_comp K hD (f := fun z : Z𝔸 => cen K z * globalPoints (𝓞 K) K γ * y)
    (((continuous_cen K).mul continuous_const).mul continuous_const)).symm

private def chiDet (χ : (⊤ : Subgroup (𝔸)ˣ) →* ℂˣ) (g : G𝔸) : ℂ :=
  ((χ ⟨Matrix.GeneralLinearGroup.det g, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)

private theorem det_cen (z : Z𝔸) :
    Matrix.GeneralLinearGroup.det (cen K z) = Matrix.GeneralLinearGroup.det z ^ 2 := by
  show Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det z)) = _
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

private theorem det_globalPoints (γ : GL (Fin 2) K) :
    Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ)
      = Units.map (algebraMap K (𝔸)) (Matrix.GeneralLinearGroup.det γ) := by
  refine Units.ext ?_
  rw [Units.coe_map, MonoidHom.coe_coe, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

private theorem norm_phi_mul (χ : (⊤ : Subgroup (𝔸)ˣ) →* ℂˣ) {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsLsXiFunction (𝓞 K) K ⊤ χ φ) (z : Z𝔸) (γ : GL (Fin 2) K) (y : G𝔸) :
    ‖φ (cen K z * globalPoints (𝓞 K) K γ * y)‖
      = ‖((χ ⟨Matrix.GeneralLinearGroup.det z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ * ‖φ y‖ := by
  have h := hφ.central_transform ⟨Matrix.GeneralLinearGroup.det z, Subgroup.mem_top _⟩ (globalPoints (𝓞 K) K γ * y)
  rw [hφ.left_invariant] at h
  rw [mul_assoc]
  exact (congrArg norm h).trans (norm_mul _ _)

private theorem norm_cd_mul (χ : (⊤ : Subgroup (𝔸)ˣ) →* ℂˣ)
    (hχK : ∀ v : Kˣ, χ ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K)) v, Subgroup.mem_top _⟩ = 1)
    (z : Z𝔸) (γ : GL (Fin 2) K) (y : G𝔸) :
    ‖chiDet K χ (cen K z * globalPoints (𝓞 K) K γ * y)‖
      = ‖((χ ⟨Matrix.GeneralLinearGroup.det z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ ^ 2 * ‖chiDet K χ y‖ := by
  have hsplit : (⟨Matrix.GeneralLinearGroup.det (cen K z * globalPoints (𝓞 K) K γ * y), Subgroup.mem_top _⟩ :
        (⊤ : Subgroup (𝔸)ˣ))
      = (⟨Matrix.GeneralLinearGroup.det z, Subgroup.mem_top _⟩ : (⊤ : Subgroup (𝔸)ˣ)) ^ 2
        * ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K)) (Matrix.GeneralLinearGroup.det γ), Subgroup.mem_top _⟩
        * ⟨Matrix.GeneralLinearGroup.det y, Subgroup.mem_top _⟩ :=
    Subtype.ext (by simp only [Subgroup.coe_mul, SubmonoidClass.coe_pow, map_mul, det_cen, det_globalPoints])
  unfold chiDet
  rw [hsplit, map_mul, map_mul, map_pow, hχK, mul_one, Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow]

private theorem sq_nnnorm_le (χ : (⊤ : Subgroup (𝔸)ˣ) →* ℂˣ)
    (hχK : ∀ v : Kˣ, χ ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K)) v, Subgroup.mem_top _⟩ = 1)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsLsXiFunction (𝓞 K) K ⊤ χ φ) {E D : Set G𝔸} {Mup mlow : ℝ}
    (hmlow : 0 < mlow) (hup : ∀ e ∈ E, ‖chiDet K χ e‖ ≤ Mup) (hlow : ∀ w ∈ D, mlow ≤ ‖chiDet K χ w‖)
    {z : Z𝔸} {γ : GL (Fin 2) K} {y : G𝔸} (hy : y ∈ E) (hzy : cen K z * globalPoints (𝓞 K) K γ * y ∈ D) :
    (‖φ y‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal (Mup / mlow) * (‖φ (cen K z * globalPoints (𝓞 K) K γ * y)‖₊ : ℝ≥0∞) ^ 2 := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ‖((χ ⟨Matrix.GeneralLinearGroup.det z, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ := ⟨_, rfl⟩
  have h1 : mlow ≤ c ^ 2 * ‖chiDet K χ y‖ := by
    have := hlow _ hzy
    rw [norm_cd_mul K χ hχK, ← hc] at this
    exact this
  have h2 : ‖chiDet K χ y‖ ≤ Mup := hup y hy
  have hMup : 0 ≤ Mup := (norm_nonneg _).trans h2
  have h3 : mlow ≤ c ^ 2 * Mup := h1.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg c))
  have hreal : ‖φ y‖ ^ 2 ≤ Mup / mlow * ‖φ (cen K z * globalPoints (𝓞 K) K γ * y)‖ ^ 2 := by
    rw [norm_phi_mul K χ hφ, ← hc, mul_pow, div_mul_eq_mul_div, le_div_iff₀ hmlow]
    have := mul_le_mul_of_nonneg_left h3 (sq_nonneg ‖φ y‖)
    linarith
  have hc0 : 0 ≤ Mup / mlow := div_nonneg hMup hmlow.le
  have hnn : ‖φ y‖₊ ^ 2 ≤ (Mup / mlow).toNNReal * ‖φ (cen K z * globalPoints (𝓞 K) K γ * y)‖₊ ^ 2 := by
    rw [← NNReal.coe_le_coe]
    simp only [NNReal.coe_pow, NNReal.coe_mul, coe_nnnorm, Real.coe_toNNReal _ hc0]
    exact hreal
  show (‖φ y‖₊ : ℝ≥0∞) ^ 2 ≤ (((Mup / mlow).toNNReal : ℝ≥0) : ℝ≥0∞) * (‖φ _‖₊ : ℝ≥0∞) ^ 2
  exact_mod_cast hnn

private theorem UNFOLD (χ : (⊤ : Subgroup (𝔸)ˣ) →* ℂˣ)
    (hχK : ∀ v : Kˣ, χ ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K)) v, Subgroup.mem_top _⟩ = 1)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : IsLsXiFunction (𝓞 K) K ⊤ χ φ)
    (hφm : AEStronglyMeasurable φ μG)
    (E D : Set G𝔸) (hE : MeasurableSet E) (hD : MeasurableSet D)
    (Mup mlow : ℝ) (hmlow : 0 < mlow)
    (hup : ∀ e ∈ E, ‖((χ ⟨Matrix.GeneralLinearGroup.det e, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖ ≤ Mup)
    (hlow : ∀ w ∈ D, mlow ≤ ‖((χ ⟨Matrix.GeneralLinearGroup.det w, Subgroup.mem_top _⟩ : ℂˣ) : ℂ)‖)
    (m : ℝ) (hm : 0 < m) (hfloor : ∀ g : G𝔸, ENNReal.ofReal m ≤ fibre K D g)
    (B : ℝ) (hfib : ∀ g : G𝔸, fibre K E g ≤ ENNReal.ofReal B) :
    ∫⁻ y in E, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μG
      ≤ ENNReal.ofReal (Mup / mlow / m * B) * ∫⁻ y in D, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μG := by
  set F : G𝔸 → ℝ≥0∞ := fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2 with hF
  have hFm : AEMeasurable F μG := by
    have h := hφm.enorm.pow_const 2
    simpa only [enorm_eq_nnnorm] using h
  have hFtop : ∀ y, F y ≠ ⊤ := fun y => ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hEFtop : ∀ y, E.indicator F y ≠ ⊤ := fun y =>
    ne_top_of_le_ne_top (hFtop y) (Set.indicator_le_self E F y)
  have hDFtop : ∀ y, D.indicator F y ≠ ⊤ := fun y =>
    ne_top_of_le_ne_top (hFtop y) (Set.indicator_le_self D F y)
  have hEF : AEMeasurable (E.indicator F) μG := hFm.indicator hE
  have hDF : AEMeasurable (D.indicator F) μG := hFm.indicator hD
  set cR : ℝ≥0∞ := ENNReal.ofReal (Mup / mlow) with hcR
  have hcRtop : cR ≠ ⊤ := ENNReal.ofReal_ne_top

  have hmeas₁ : ∀ p : GL (Fin 2) K ⧸ ratCentre K, AEMeasurable
      (fun q : G𝔸 × Z𝔸 => E.indicator F q.1
        * D.indicator (1 : G𝔸 → ℝ≥0∞) (cen K q.2 * globalPoints (𝓞 K) K (Quotient.out p) * q.1))
      (MeasureTheory.Measure.prod μG μZ) := by
    intro p
    have hmap : Measurable fun q : G𝔸 × Z𝔸 => cen K q.2 * globalPoints (𝓞 K) K (Quotient.out p) * q.1 :=
      ((((continuous_cen K).comp continuous_snd).mul continuous_const).mul continuous_fst).measurable
    exact (hEF.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul
      ((measurable_one.indicator hD).comp hmap).aemeasurable
  have hmeas₂ : ∀ p : GL (Fin 2) K ⧸ ratCentre K, AEMeasurable
      (fun q : Z𝔸 × G𝔸 => E.indicator (1 : G𝔸 → ℝ≥0∞) ((cen K q.1 * globalPoints (𝓞 K) K (Quotient.out p))⁻¹ * q.2)
        * D.indicator F q.2)
      (MeasureTheory.Measure.prod μZ μG) := by
    intro p
    have hmap : Measurable fun q : Z𝔸 × G𝔸 => (cen K q.1 * globalPoints (𝓞 K) K (Quotient.out p))⁻¹ * q.2 :=
      (((((continuous_cen K).comp continuous_fst).mul continuous_const).inv).mul continuous_snd).measurable
    exact ((measurable_one.indicator hE).comp hmap).aemeasurable.mul
      (hDF.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)

  have hpt : ∀ (p : GL (Fin 2) K ⧸ ratCentre K) (z : Z𝔸) (y : G𝔸),
      E.indicator F y * D.indicator (1 : G𝔸 → ℝ≥0∞) (cen K z * globalPoints (𝓞 K) K (Quotient.out p) * y)
        ≤ cR * (E.indicator (1 : G𝔸 → ℝ≥0∞) y
            * D.indicator F (cen K z * globalPoints (𝓞 K) K (Quotient.out p) * y)) := by
    intro p z y
    by_cases hy : y ∈ E
    · by_cases hzy : cen K z * globalPoints (𝓞 K) K (Quotient.out p) * y ∈ D
      · rw [Set.indicator_of_mem hy F, Set.indicator_of_mem hzy (1 : G𝔸 → ℝ≥0∞),
          Set.indicator_of_mem hy (1 : G𝔸 → ℝ≥0∞), Set.indicator_of_mem hzy F]
        simp only [Pi.one_apply, mul_one, one_mul]
        exact sq_nnnorm_le K χ hχK hφ hmlow hup hlow hy hzy
      · simp [hzy]
    · simp [hy]

  have hinner : ∀ (p : GL (Fin 2) K ⧸ ratCentre K) (y : G𝔸),
      ∫⁻ z, E.indicator (1 : G𝔸 → ℝ≥0∞) ((cen K z * globalPoints (𝓞 K) K (Quotient.out p))⁻¹ * y)
          * D.indicator F y ∂μZ
        = D.indicator F y * cmass K E (Quotient.out p)⁻¹ y := by
    intro p y
    rw [lintegral_mul_const' _ _ (hDFtop y),
      lintegral_indicator_one_comp K hE
        (f := fun z : Z𝔸 => (cen K z * globalPoints (𝓞 K) K (Quotient.out p))⁻¹ * y)
        ((((continuous_cen K).mul continuous_const).inv).mul continuous_const),
      cmass_inv, mul_comm]

  have htrans : ∀ (p : GL (Fin 2) K ⧸ ratCentre K) (z : Z𝔸),
      ∫⁻ y, E.indicator (1 : G𝔸 → ℝ≥0∞) y
          * D.indicator F (cen K z * globalPoints (𝓞 K) K (Quotient.out p) * y) ∂μG
        = ∫⁻ y, E.indicator (1 : G𝔸 → ℝ≥0∞) ((cen K z * globalPoints (𝓞 K) K (Quotient.out p))⁻¹ * y)
          * D.indicator F y ∂μG := by
    intro p z
    have h := lintegral_mul_left_eq_self (μ := μG)
      (fun y => E.indicator (1 : G𝔸 → ℝ≥0∞) ((cen K z * globalPoints (𝓞 K) K (Quotient.out p))⁻¹ * y)
        * D.indicator F y)
      (cen K z * globalPoints (𝓞 K) K (Quotient.out p))
    simp only [inv_mul_cancel_left] at h
    exact h
  have key : ENNReal.ofReal m * ∫⁻ y, E.indicator F y ∂μG
      ≤ cR * (ENNReal.ofReal B * ∫⁻ y, D.indicator F y ∂μG) :=
    calc ENNReal.ofReal m * ∫⁻ y, E.indicator F y ∂μG
        = ∫⁻ y, ENNReal.ofReal m * E.indicator F y ∂μG := (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ y, E.indicator F y * fibre K D y ∂μG :=
          lintegral_mono fun y => by rw [mul_comm]; exact mul_le_mul_right (hfloor y) _
      _ = ∫⁻ y, ∑' p : GL (Fin 2) K ⧸ ratCentre K, E.indicator F y * cmass K D (Quotient.out p) y ∂μG := by
          simp only [fibre, ENNReal.tsum_mul_left]
      _ = ∑' p : GL (Fin 2) K ⧸ ratCentre K, ∫⁻ y, E.indicator F y * cmass K D (Quotient.out p) y ∂μG :=
          lintegral_tsum fun p => hEF.mul (measurable_cmass K hD _).aemeasurable
      _ = ∑' p : GL (Fin 2) K ⧸ ratCentre K, ∫⁻ y, ∫⁻ z, E.indicator F y
            * D.indicator (1 : G𝔸 → ℝ≥0∞) (cen K z * globalPoints (𝓞 K) K (Quotient.out p) * y) ∂μZ ∂μG :=
          tsum_congr fun p => lintegral_congr fun y => by
            rw [cmass_eq_lintegral K hD, lintegral_const_mul' _ _ (hEFtop y)]
      _ = ∑' p : GL (Fin 2) K ⧸ ratCentre K, ∫⁻ z, ∫⁻ y, E.indicator F y
            * D.indicator (1 : G𝔸 → ℝ≥0∞) (cen K z * globalPoints (𝓞 K) K (Quotient.out p) * y) ∂μG ∂μZ :=
          tsum_congr fun p => lintegral_lintegral_swap (hmeas₁ p)
      _ ≤ ∑' p : GL (Fin 2) K ⧸ ratCentre K, ∫⁻ z, ∫⁻ y, cR * (E.indicator (1 : G𝔸 → ℝ≥0∞) y
            * D.indicator F (cen K z * globalPoints (𝓞 K) K (Quotient.out p) * y)) ∂μG ∂μZ :=
          ENNReal.tsum_le_tsum fun p => lintegral_mono fun z => lintegral_mono fun y => hpt p z y
      _ = cR * ∑' p : GL (Fin 2) K ⧸ ratCentre K, ∫⁻ z, ∫⁻ y, E.indicator (1 : G𝔸 → ℝ≥0∞) y
            * D.indicator F (cen K z * globalPoints (𝓞 K) K (Quotient.out p) * y) ∂μG ∂μZ := by
          simp only [lintegral_const_mul' cR _ hcRtop, ENNReal.tsum_mul_left]
      _ = cR * ∑' p : GL (Fin 2) K ⧸ ratCentre K, ∫⁻ z, ∫⁻ y,
            E.indicator (1 : G𝔸 → ℝ≥0∞) ((cen K z * globalPoints (𝓞 K) K (Quotient.out p))⁻¹ * y)
              * D.indicator F y ∂μG ∂μZ := by
          congr 1
          exact tsum_congr fun p => lintegral_congr fun z => htrans p z
      _ = cR * ∑' p : GL (Fin 2) K ⧸ ratCentre K, ∫⁻ y, ∫⁻ z,
            E.indicator (1 : G𝔸 → ℝ≥0∞) ((cen K z * globalPoints (𝓞 K) K (Quotient.out p))⁻¹ * y)
              * D.indicator F y ∂μZ ∂μG := by
          congr 1
          exact tsum_congr fun p => lintegral_lintegral_swap (hmeas₂ p)
      _ = cR * ∑' p : GL (Fin 2) K ⧸ ratCentre K, ∫⁻ y, D.indicator F y * cmass K E (Quotient.out p)⁻¹ y ∂μG := by
          congr 1
          exact tsum_congr fun p => lintegral_congr fun y => hinner p y
      _ = cR * ∫⁻ y, D.indicator F y * fibre K E y ∂μG := by
          congr 1
          rw [← lintegral_tsum fun p : GL (Fin 2) K ⧸ ratCentre K =>
            hDF.fun_mul (measurable_cmass K hE (Quotient.out p)⁻¹).aemeasurable]
          exact lintegral_congr fun y => by rw [ENNReal.tsum_mul_left, tsum_cmass_inv]
      _ ≤ cR * ∫⁻ y, D.indicator F y * ENNReal.ofReal B ∂μG :=
          mul_le_mul_right (lintegral_mono fun y => mul_le_mul_right (hfib y) _) _
      _ = cR * (ENNReal.ofReal B * ∫⁻ y, D.indicator F y ∂μG) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm (∫⁻ y, D.indicator F y ∂μG)]

  rw [← lintegral_indicator hE, ← lintegral_indicator hD]
  have hm0 : ENNReal.ofReal m ≠ 0 := (ENNReal.ofReal_pos.mpr hm).ne'
  by_cases hsign : 0 ≤ Mup / mlow / m
  · have hkey := (ENNReal.mul_le_iff_le_inv hm0 ENNReal.ofReal_ne_top).mp key
    refine hkey.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hsign, ENNReal.ofReal_div_of_pos hm, ← hcR, div_eq_mul_inv]
    ring
  · have hneg : Mup / mlow ≤ 0 := by
      by_contra h
      exact hsign (div_nonneg (not_le.mp h).le hm.le)
    have hcR0 : cR = 0 := by
      rw [hcR, ENNReal.ofReal_eq_zero]
      exact hneg
    rw [hcR0, zero_mul] at key
    have hzero : ∫⁻ y, E.indicator F y ∂μG = 0 :=
      (mul_eq_zero.mp (le_antisymm key zero_le)).resolve_left hm0
    rw [hzero]
    exact zero_le

private theorem square_mass_le (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : IsLsXiFunction (𝓞 K) K ⊤ χ φ)
    (hcont : Continuous φ)
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C)
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c') (hd₁' : 0 < d₁') :
    ∃ (T₁ : ℝ) (A : ℕ) (M : ℝ), ∀ x ∈ centreCutSiegelSet K c' u' d₁' d₂',
      T₁ < archHeight K (glArch (𝓞 K) K x) →
        ∫⁻ y in Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
          unipotentGL2 t * x * c) (closure (adelicBox K)) C,
            (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≤ ENNReal.ofReal (M * archHeight K (glArch (𝓞 K) K x) ^ A) *
            ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
              (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by

  by_cases hne : ∃ g, φ g ≠ 0
  swap
  · refine ⟨0, 0, 0, fun x hx hH => ?_⟩
    have h0 : (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) = fun _ => 0 := by
      funext y
      have hy : φ y = 0 := not_not.mp fun h => hne ⟨y, h⟩
      simp [hy]
    show ∫⁻ y in region K x C, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μG ≤ _
    rw [h0, lintegral_zero]
    exact zero_le
  obtain ⟨hχK, hχc⟩ := X1 K χ φ hφ hcont hne
  have hφm : AEStronglyMeasurable φ μG := hcont.aestronglyMeasurable

  have hd₂ : 0 < d₂ := by
    obtain ⟨γ, z, hmem⟩ := hcov 1
    obtain ⟨x₀, -, s, hs, -⟩ := Set.mem_iUnion₂.mp hmem
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
    exact (archDetNorm_pos w s).trans_le ((mem_centreCutSiegelSet_iff.mp hs).2.2.2 w).2
  have hdp : 0 < max d₁ (d₂ / 2) := lt_max_of_lt_right (by positivity)
  have hdp' : max d₁ (d₂ / 2) < d₂ := max_lt hd (by linarith)
  have hsub : window K c u (max d₁ (d₂ / 2)) d₂ T ⊆ window K c u d₁ d₂ T :=
    WMONO K c u T (le_max_left _ _) le_rfl
  obtain ⟨m, hm, hfloor⟩ := FLOOR K c u (max d₁ (d₂ / 2)) d₂ T hdp hdp'
    (fun a' b' ha' hab' => BAND K c u d₁ d₂ T hcov ha' hab')
  obtain ⟨Mup, mlow, -, hmlow, hup, hlow⟩ :=
    NORM K χ hχc c u (max d₁ (d₂ / 2)) d₂ T hdp hC c' u' d₁' d₂' hd₁'
  obtain ⟨T₁, A, Mfib, hfib⟩ := FIBRE K hC c' u' d₁' d₂' hc'
  refine ⟨T₁, A, Mup / mlow / m * Mfib, fun x hx hH => ?_⟩
  have key := UNFOLD K χ hχK φ hφ hφm (region K x C) (window K c u (max d₁ (d₂ / 2)) d₂ T)
    (REGION K x hC).2 (WMEAS K c u _ _ T) Mup mlow hmlow (hup x hx) hlow m hm hfloor
    (Mfib * archHeight K (glArch (𝓞 K) K x) ^ A) (hfib x hx hH)
  have hmono : ∫⁻ y in window K c u (max d₁ (d₂ / 2)) d₂ T, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μG
      ≤ ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μG :=
    lintegral_mono_set hsub
  have hM : Mup / mlow / m * (Mfib * archHeight K (glArch (𝓞 K) K x) ^ A)
      = Mup / mlow / m * Mfib * archHeight K (glArch (𝓞 K) K x) ^ A := by ring
  show ∫⁻ y in region K x C, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μG ≤ _
  calc ∫⁻ y in region K x C, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μG
      ≤ ENNReal.ofReal (Mup / mlow / m * (Mfib * archHeight K (glArch (𝓞 K) K x) ^ A)) *
          ∫⁻ y in window K c u (max d₁ (d₂ / 2)) d₂ T, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂μG := key
    _ ≤ ENNReal.ofReal (Mup / mlow / m * Mfib * archHeight K (glArch (𝓞 K) K x) ^ A) *
          ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂, (‖φ y‖₊ : ℝ≥0∞) ^ 2
            ∂μG := by
        rw [hM]
        exact mul_le_mul_of_nonneg_left hmono zero_le

end SquareMassSiegel
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre.SquareMassSiegel"

end
p2m_reactivate "P2MW.S_AutomorphicForm_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre.SquareMassSiegel"

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsLsXiFunction (𝓞 K) K ⊤ χ φ)
    (hcont : Continuous φ)
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C)
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c') (hd₁' : 0 < d₁') :
    ∃ (T₁ : ℝ) (A : ℕ) (M : ℝ), ∀ x ∈ centreCutSiegelSet K c' u' d₁' d₂',
      T₁ < archHeight K (glArch (𝓞 K) K x) →
        ∫⁻ y in Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
          unipotentGL2 t * x * c) (closure (adelicBox K)) C,
            (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≤ ENNReal.ofReal (M * archHeight K (glArch (𝓞 K) K x) ^ A) *
            ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
              (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  exact SquareMassSiegel.square_mass_le K c u d₁ d₂ T hd hcov χ φ hφ hcont hC c' u' d₁' d₂' hc' hd₁'

end S_AutomorphicForm_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre (solution)
