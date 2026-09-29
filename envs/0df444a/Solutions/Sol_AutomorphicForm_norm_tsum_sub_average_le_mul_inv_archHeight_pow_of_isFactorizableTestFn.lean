-- Prove2me | solution 1 for AutomorphicForm.norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/3a0a453e-5754-5674-b375-83f4396c7d16

import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_isCompact_cover_of_archHeight_le
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_IsFactorizableTestFn_comp_mul_unipotentGL2_mul_mem_pureTensorSet
import Theorems.Thm_NumberField_AdelicFourier_tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_comp_mul_left
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_pureTensor_eq
import Theorems.Thm_NumberField_AdelicFourier_fourierIntegral_mem_schwartzBruhat
import Theorems.Thm_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_InfinitePlace_exists_sum_prod_inv_one_add_mul_pow_le
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_NumberField_StandardAddChar_stdAddChar_apply_mk_zero_eq_fourierChar_trace
import Theorems.Thm_exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport
import Theorems.Thm_IsLocallyConstant_isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn
p2m_attr_erase "instance" "NumberField.AdelicCentre.locallyCompactSpace_adelicPGL2 NumberField.AdelicCentre.isTopologicalGroup_adelicPGL2 NumberField.AdelicCentre.t2Space_adelicPGL2 NumberField.AdelicCentre.isClosed_center instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_zero AutomorphicForm.SiegelCoordinates.upperUnit_apply_one_one AutomorphicForm.SiegelCoordinates.upperUnit_apply_zero_one"

open NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel MeasureTheory

set_option autoImplicit false

noncomputable section

namespace UnipotentKernelDecay

section SliceAffine

open NumberField AutomorphicForm

variable {R : Type*} [CommRing R]

private def diagGL2 (t₁ t₂ : Rˣ) : GL (Fin 2) R where
  val := !![(t₁ : R), 0; 0, (t₂ : R)]
  inv := !![((t₁⁻¹ : Rˣ) : R), 0; 0, ((t₂⁻¹ : Rˣ) : R)]
  val_inv := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[scoped simp] private theorem diagGL2_coe (t₁ t₂ : Rˣ) :
    (diagGL2 t₁ t₂ : Matrix (Fin 2) (Fin 2) R) = !![(t₁ : R), 0; 0, (t₂ : R)] := rfl

private def sliceScale (t₁ t₂ : Rˣ) : Rˣ := t₁⁻¹ * t₂

end SliceAffine

section PlaceNorms

open NumberField NumberField.InfinitePlace

variable {F : Type*} [Field F]

private theorem norm_extensionEmbedding (w : InfinitePlace F) (x : w.Completion) :
    ‖InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

private theorem norm_extensionEmbeddingOfIsReal {w : InfinitePlace F} (hw : w.IsReal) (x : w.Completion) :
    ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x‖ = ‖x‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
    (map_zero _) x

section Global

variable {K : Type} [Field K] [NumberField K]

private theorem globalPoints_apply (γ : GL (Fin 2) K) (i j : Fin 2) :
    ((globalPoints (𝓞 K) K γ : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
      = algebraMap K (AdeleRing (𝓞 K) K) ((γ : Matrix (Fin 2) (Fin 2) K) i j) := rfl

end Global

end PlaceNorms

section HighStructure

open NumberField NumberField.InfinitePlace IsDedekindDomain Matrix
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel

section Local

variable {K : Type*} [NormedField K]

private theorem localHeight_torus_mul {s : GL (Fin 2) K} {β : K}
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = β) (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = 1)
    (g : GL (Fin 2) K) :
    localHeight (s * g) = ‖β‖ * localHeight g := by
  have hcoe : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl
  have hdets : (s : Matrix (Fin 2) (Fin 2) K).det = β := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdet : ‖((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖β‖ * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [hcoe, Matrix.det_mul, hdets, norm_mul]
  have hrow : rowNormSq ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    rw [rowNormSq_scalar_entries_mul h10 h11 g, norm_one, one_pow, one_mul]
  unfold localHeight
  rw [hdet, hrow, mul_div_assoc]

private theorem xWindowSq_torus_mul {s : GL (Fin 2) K} {β : K}
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = β) (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0) (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = 1)
    (g : GL (Fin 2) K) :
    xWindowSq (s * g) = ‖β‖ ^ 2 * xWindowSq g := by
  have hrow : rowNormSq ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    rw [rowNormSq_scalar_entries_mul h10 h11 g, norm_one, one_pow, one_mul]
  unfold xWindowSq
  rw [topNormSq_scalar_entries_mul h00 h01 g, hrow, localHeight_torus_mul h00 h01 h10 h11 g,
    mul_pow, mul_div_assoc, mul_sub]

end Local

section Adelic

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

private theorem glFin_diagGL2_of_snd_eq_one {β : 𝔸ˣ} (hβ : (β : 𝔸).2 = 1) :
    glFin (𝓞 F) F (diagGL2 β 1) = 1 := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [glFin_apply, diagGL2, hβ] <;> rfl

private theorem archHeight_glArch_diagGL2_mul (β : 𝔸ˣ) (g : AdelicGL2 (𝓞 F) F) :
    archHeight F (glArch (𝓞 F) F (diagGL2 β 1 * g))
      = (∏ v : InfinitePlace F, ‖(β : 𝔸).1 v‖ ^ v.mult) * archHeight F (glArch (𝓞 F) F g) := by
  unfold archHeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_mul, map_mul, ← mul_pow]
  congr 1
  refine localHeight_torus_mul ?_ ?_ ?_ ?_ (archComponent F v (glArch (𝓞 F) F g))
  · rw [archComponent_apply, glArch_apply]; simp [diagGL2]
  · rw [archComponent_apply, glArch_apply]; simp [diagGL2]; rfl
  · rw [archComponent_apply, glArch_apply]; simp [diagGL2]; rfl
  · rw [archComponent_apply, glArch_apply]; simp [diagGL2]; rfl

private theorem xWindowSq_archComponent_glArch_diagGL2_mul (β : 𝔸ˣ) (g : AdelicGL2 (𝓞 F) F)
    (v : InfinitePlace F) :
    xWindowSq (archComponent F v (glArch (𝓞 F) F (diagGL2 β 1 * g)))
      = ‖(β : 𝔸).1 v‖ ^ 2 * xWindowSq (archComponent F v (glArch (𝓞 F) F g)) := by
  rw [map_mul, map_mul]
  refine xWindowSq_torus_mul ?_ ?_ ?_ ?_ (archComponent F v (glArch (𝓞 F) F g))
  · rw [archComponent_apply, glArch_apply]; simp [diagGL2]
  · rw [archComponent_apply, glArch_apply]; simp [diagGL2]; rfl
  · rw [archComponent_apply, glArch_apply]; simp [diagGL2]; rfl
  · rw [archComponent_apply, glArch_apply]; simp [diagGL2]; rfl

private theorem diagGL2_mul_mem_integralWindowedSiegelSet {c u : ℝ} {x : AdelicGL2 (𝓞 F) F}
    (hx : x ∈ integralWindowedSiegelSet F c u) {t : ℝ} (ht : 1 ≤ t)
    (htH : t ^ Module.finrank ℚ F = archHeight F (glArch (𝓞 F) F x))
    {β : 𝔸ˣ} (hβf : (β : 𝔸).2 = 1) (hβa : ∀ v : InfinitePlace F, ‖(β : 𝔸).1 v‖ = t⁻¹) :
    diagGL2 β 1 * x ∈ integralWindowedSiegelSet F 1 u ∧
      archHeight F (glArch (𝓞 F) F (diagGL2 β 1 * x)) = 1 := by
  obtain ⟨hfin, _, hwin⟩ := hx
  have ht0 : 0 < t := one_pos.trans_le ht
  have hH : archHeight F (glArch (𝓞 F) F (diagGL2 β 1 * x)) = 1 := by
    rw [archHeight_glArch_diagGL2_mul, ← htH]
    simp_rw [hβa]
    rw [Finset.prod_pow_eq_pow_sum, sum_mult_eq, inv_pow,
      inv_mul_cancel₀ (pow_ne_zero _ ht0.ne')]
  refine ⟨⟨?_, hH.symm.le, fun v => ?_⟩, hH⟩
  · rw [map_mul, glFin_diagGL2_of_snd_eq_one F hβf, one_mul]; exact hfin
  · rw [xWindowSq_archComponent_glArch_diagGL2_mul, hβa]
    have hle : t⁻¹ ^ 2 ≤ 1 := by
      rw [inv_pow]; exact inv_le_one_of_one_le₀ (one_le_pow₀ ht)
    rcases le_or_gt 0 (xWindowSq (archComponent F v (glArch (𝓞 F) F x))) with h0 | h0
    · exact (mul_le_of_le_one_left h0 hle).trans (hwin v)
    · exact ((mul_neg_of_pos_of_neg (by positivity) h0).le).trans (sq_nonneg u)

omit [NumberField F] in

private theorem exists_norm_eq (w : InfinitePlace F) {r : ℝ} (hr : 0 ≤ r) :
    ∃ a : w.Completion, ‖a‖ = r := by
  by_cases hw : IsReal w
  · refine ⟨(Completion.ringEquivRealOfIsReal hw).symm r, ?_⟩
    rw [← norm_extensionEmbeddingOfIsReal hw, ← Completion.ringEquivRealOfIsReal_apply hw,
      RingEquiv.apply_symm_apply, Real.norm_eq_abs, abs_of_nonneg hr]
  · have hc : IsComplex w := not_isReal_iff_isComplex.mp hw
    refine ⟨(Completion.ringEquivComplexOfIsComplex hc).symm r, ?_⟩
    rw [← norm_extensionEmbedding w, ← Completion.ringEquivComplexOfIsComplex_apply hc,
      RingEquiv.apply_symm_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

private theorem exists_archIdele_norm_eq {t : ℝ} (ht : 0 < t) :
    ∃ α : 𝔸ˣ, (α : 𝔸).2 = 1 ∧ ∀ v : InfinitePlace F, ‖(α : 𝔸).1 v‖ = t := by
  choose a ha using fun v : InfinitePlace F => exists_norm_eq F v ht.le
  have ha0 : ∀ v, a v ≠ 0 := fun v h => by
    have := ha v; rw [h, norm_zero] at this; exact ht.ne' this.symm
  refine ⟨⟨(fun v => a v, 1), (fun v => (a v)⁻¹, 1), ?_, ?_⟩, rfl, fun v => ha v⟩
  · refine Prod.ext (funext fun v => ?_) (one_mul 1)
    exact mul_inv_cancel₀ (ha0 v)
  · refine Prod.ext (funext fun v => ?_) (one_mul 1)
    exact inv_mul_cancel₀ (ha0 v)

section UT

variable {R : Type*} [CommRing R]

private theorem inv_apply_one_zero {L : Type*} [Field L] (γ : GL (Fin 2) L)
    (h : (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    ((γ⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 := by
  simp [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, h]

private theorem isUnit_apply_of_apply_one_zero (b : GL (Fin 2) R)
    (h : (b : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) :
    IsUnit ((b : Matrix (Fin 2) (Fin 2) R) 0 0) ∧ IsUnit ((b : Matrix (Fin 2) (Fin 2) R) 1 1) := by
  have hdet : IsUnit (b : Matrix (Fin 2) (Fin 2) R).det := (Matrix.isUnits_det_units b)
  rw [Matrix.det_fin_two, h, mul_zero, sub_zero] at hdet
  exact ⟨isUnit_of_mul_isUnit_left hdet, isUnit_of_mul_isUnit_right hdet⟩

private theorem eq_unipotent_mul_diag_of_apply_one_zero (b : GL (Fin 2) R)
    (h : (b : Matrix (Fin 2) (Fin 2) R) 1 0 = 0) :
    ∃ (w : R) (t₁ t₂ : Rˣ), b = unipotentGL2 w * diagGL2 t₁ t₂ ∧
      (t₁ : R) = (b : Matrix (Fin 2) (Fin 2) R) 0 0 ∧ (t₂ : R) = (b : Matrix (Fin 2) (Fin 2) R) 1 1 := by
  obtain ⟨h0, h1⟩ := isUnit_apply_of_apply_one_zero b h
  refine ⟨(b : Matrix (Fin 2) (Fin 2) R) 0 1 * ((h1.unit⁻¹ : Rˣ) : R), h0.unit, h1.unit, ?_,
    rfl, rfl⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, diagGL2, h]
  rw [mul_assoc, h1.val_inv_mul, mul_one]

private theorem diag_mul_mul_diag_apply (a d a' d' : Rˣ) (M : GL (Fin 2) R) (i j : Fin 2) :
    ((diagGL2 a d * M * diagGL2 a' d' : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i j
      = ![(a : R), d] i * (M : Matrix (Fin 2) (Fin 2) R) i j * ![(a' : R), d'] j := by
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, diagGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

end UT

private theorem centralScalar_eq_diagGL2 (z : 𝔸ˣ) : centralScalar (𝓞 F) F z = diagGL2 z z := by
  apply Units.ext
  change Matrix.scalar (Fin 2) (z : 𝔸) = ((diagGL2 z z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) 𝔸)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagGL2, Matrix.scalar_apply, Matrix.diagonal]

private theorem centralScalar_comm (z : 𝔸ˣ) (g : AdelicGL2 (𝓞 F) F) :
    g * centralScalar (𝓞 F) F z = centralScalar (𝓞 F) F z * g := by
  apply Units.ext
  change (g : Matrix (Fin 2) (Fin 2) 𝔸) * (Matrix.scalar (Fin 2) (z : 𝔸))
    = (Matrix.scalar (Fin 2) (z : 𝔸)) * (g : Matrix (Fin 2) (Fin 2) 𝔸)
  exact ((Matrix.scalar_commute (z : 𝔸) (Commute.all _) (g : Matrix (Fin 2) (Fin 2) 𝔸)).eq).symm

private theorem exists_eq_unipotent_mul_diag_mul_mem_of_one_le_archHeight (c u : ℝ) :
    ∃ K : Set (AdelicGL2 (𝓞 F) F), IsCompact K ∧
      ∀ x ∈ integralWindowedSiegelSet F c u, 1 ≤ archHeight F (glArch (𝓞 F) F x) →
        ∃ (w : 𝔸) (t₁ t₂ : 𝔸ˣ) (k : AdelicGL2 (𝓞 F) F) (α : 𝔸ˣ) (q : Fˣ) (t : ℝ),
          k ∈ K ∧ x = unipotentGL2 w * diagGL2 t₁ t₂ * k ∧
          sliceScale t₁ t₂ = α⁻¹ * Units.map (algebraMap F 𝔸 : F →* 𝔸) q ∧
          (α : 𝔸).2 = 1 ∧ (∀ v : InfinitePlace F, ‖(α : 𝔸).1 v‖ = t) ∧ 1 ≤ t ∧
          t ^ Module.finrank ℚ F = archHeight F (glArch (𝓞 F) F x) := by
  obtain ⟨K, hK, hcov⟩ := exists_isCompact_cover_of_archHeight_le F 1 u 1 one_pos
  refine ⟨K, hK, fun x hx hH => ?_⟩

  set H : ℝ := archHeight F (glArch (𝓞 F) F x) with hHdef
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hn : Module.finrank ℚ F ≠ 0 := Module.finrank_pos.ne'
  set t : ℝ := H ^ ((Module.finrank ℚ F : ℝ)⁻¹) with htdef
  have ht1 : 1 ≤ t := Real.one_le_rpow hH (by positivity)
  have ht0 : 0 < t := one_pos.trans_le ht1
  have htH : t ^ Module.finrank ℚ F = H := Real.rpow_inv_natCast_pow hH0 hn

  obtain ⟨α, hαf, hαa⟩ := exists_archIdele_norm_eq F ht0
  have hβf : ((α⁻¹ : 𝔸ˣ) : 𝔸).2 = 1 := by
    have h : adeleFin (𝓞 F) F ((α⁻¹ : 𝔸ˣ) : 𝔸) * adeleFin (𝓞 F) F (α : 𝔸) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [adeleFin_apply, adeleFin_apply, hαf, mul_one] at h
    exact h
  have hβa : ∀ v : InfinitePlace F, ‖((α⁻¹ : 𝔸ˣ) : 𝔸).1 v‖ = t⁻¹ := by
    intro v
    have h : archEval F v (adeleArch (𝓞 F) F ((α⁻¹ : 𝔸ˣ) : 𝔸))
        * archEval F v (adeleArch (𝓞 F) F (α : 𝔸)) = 1 := by
      rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    rw [archEval_apply, archEval_apply, adeleArch_apply, adeleArch_apply] at h
    have h' : ‖((α⁻¹ : 𝔸ˣ) : 𝔸).1 v‖ * t = 1 := by
      rw [← hαa v, ← norm_mul, h, norm_one]
    exact eq_inv_of_mul_eq_one_left h'
  obtain ⟨hx', hH'⟩ := diagGL2_mul_mem_integralWindowedSiegelSet F hx ht1 htH hβf hβa

  obtain ⟨γ, z, hγ, hk⟩ := hcov _ hx' hH'.le
  set k := globalPoints (𝓞 F) F γ * (diagGL2 α⁻¹ 1 * x) * centralScalar (𝓞 F) F z with hkdef

  set b : AdelicGL2 (𝓞 F) F :=
    diagGL2 α 1 * globalPoints (𝓞 F) F γ⁻¹ * centralScalar (𝓞 F) F z⁻¹ with hbdef
  have hDinv : (diagGL2 α⁻¹ 1 : AdelicGL2 (𝓞 F) F) = (diagGL2 α 1)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    apply Units.ext; ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, diagGL2]
  have hxb : x = b * k := by
    rw [hbdef, hkdef, map_inv, map_inv, hDinv]
    rw [centralScalar_comm F z (globalPoints (𝓞 F) F γ * ((diagGL2 α 1)⁻¹ * x))]
    group

  set γi : GL (Fin 2) F := γ⁻¹ with hγidef
  have hγi10 : (γi : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    rw [hγidef]; exact inv_apply_one_zero γ hγ
  set G : AdelicGL2 (𝓞 F) F := globalPoints (𝓞 F) F γi with hGdef
  have hG : ∀ i j, (G : Matrix (Fin 2) (Fin 2) 𝔸) i j
      = algebraMap F 𝔸 ((γi : Matrix (Fin 2) (Fin 2) F) i j) := fun i j => by
    rw [hGdef, globalPoints_apply]
  set Z : AdelicGL2 (𝓞 F) F := centralScalar (𝓞 F) F z⁻¹ with hZdef
  have hZ : Z = diagGL2 z⁻¹ z⁻¹ := by rw [hZdef, centralScalar_eq_diagGL2]
  have hb10 : (b : Matrix (Fin 2) (Fin 2) 𝔸) 1 0 = 0 := by
    rw [hbdef, hZ, diag_mul_mul_diag_apply]
    simp [hG, hγi10]
  have hb00 : (b : Matrix (Fin 2) (Fin 2) 𝔸) 0 0
      = (α : 𝔸) * algebraMap F 𝔸 ((γi : Matrix (Fin 2) (Fin 2) F) 0 0) * ((z⁻¹ : 𝔸ˣ) : 𝔸) := by
    rw [hbdef, hZ, diag_mul_mul_diag_apply]
    simp [hG]
  have hb11 : (b : Matrix (Fin 2) (Fin 2) 𝔸) 1 1
      = algebraMap F 𝔸 ((γi : Matrix (Fin 2) (Fin 2) F) 1 1) * ((z⁻¹ : 𝔸ˣ) : 𝔸) := by
    rw [hbdef, hZ, diag_mul_mul_diag_apply]
    simp [hG]
  obtain ⟨w, t₁, t₂, hbw, ht₁, ht₂⟩ := eq_unipotent_mul_diag_of_apply_one_zero b hb10

  obtain ⟨he, hd⟩ := isUnit_apply_of_apply_one_zero γi hγi10
  obtain ⟨e, he'⟩ := he
  obtain ⟨d, hd'⟩ := hd
  refine ⟨w, t₁, t₂, k, α, e⁻¹ * d, t, hk, by rw [hxb, hbw], ?_, hαf, hαa, ht1, htH⟩

  have h1 : (t₁ : 𝔸) = (α : 𝔸) * algebraMap F 𝔸 (e : F) * ((z⁻¹ : 𝔸ˣ) : 𝔸) := by
    rw [ht₁, hb00, ← he']
  have h2 : (t₂ : 𝔸) = algebraMap F 𝔸 (d : F) * ((z⁻¹ : 𝔸ˣ) : 𝔸) := by
    rw [ht₂, hb11, ← hd']
  have hαα : ((α⁻¹ : 𝔸ˣ) : 𝔸) * (α : 𝔸) = 1 := α.inv_mul
  have hee : algebraMap F 𝔸 ((e⁻¹ : Fˣ) : F) * algebraMap F 𝔸 (e : F) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  rw [sliceScale, inv_mul_eq_iff_eq_mul]
  apply Units.ext
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, map_mul, h1, h2]
  linear_combination
    (-(algebraMap F 𝔸 (d : F) * ((z⁻¹ : 𝔸ˣ) : 𝔸)
      * (algebraMap F 𝔸 ((e⁻¹ : Fˣ) : F) * algebraMap F 𝔸 (e : F)))) * hαα
    + (-(algebraMap F 𝔸 (d : F) * ((z⁻¹ : 𝔸ˣ) : 𝔸))) * hee

end Adelic

end HighStructure

section SliceFourier

open MeasureTheory NumberField NumberField.AdelicFourier

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F

private theorem fourierIntegral_affine
    [MeasurableSpace 𝔸] [BorelSpace 𝔸] (μ : Measure 𝔸) [μ.IsAddHaarMeasure]
    (ψ : AddChar 𝔸 ℂ) (Ψ : 𝔸 → ℂ) (τ : 𝔸ˣ) (β η : 𝔸) :
    fourierIntegral ψ μ (fun s => Ψ ((τ : 𝔸) * s + β)) η
      = ((distribHaarChar 𝔸 τ : ℝ) : ℂ)⁻¹ * (ψ (β * ((τ⁻¹ : 𝔸ˣ) * η))
          * fourierIntegral ψ μ Ψ (((τ⁻¹ : 𝔸ˣ) : 𝔸) * η)) := by
  have h1 : (fun s => Ψ ((τ : 𝔸) * s + β)) = fun v => (Ψ ∘ fun u => u + β) ((τ : 𝔸) * v) := by
    funext v; rfl
  rw [h1, fourierIntegral_comp_mul_left F μ ψ (Ψ ∘ fun u => u + β) τ η,
    fourierIntegral_comp_add_right ψ μ Ψ β]

private theorem norm_fourierIntegral_affine
    [MeasurableSpace 𝔸] [BorelSpace 𝔸] (μ : Measure 𝔸) [μ.IsAddHaarMeasure]
    (ψ : AddChar 𝔸 ℂ) (hψu : ∀ x : 𝔸, ‖ψ x‖ = 1) (Ψ : 𝔸 → ℂ) (τ : 𝔸ˣ) (β η : 𝔸) :
    ‖fourierIntegral ψ μ (fun s => Ψ ((τ : 𝔸) * s + β)) η‖
      = ((distribHaarChar 𝔸 τ : ℝ))⁻¹ * ‖fourierIntegral ψ μ Ψ (((τ⁻¹ : 𝔸ˣ) : 𝔸) * η)‖ := by
  rw [fourierIntegral_affine, norm_mul, norm_mul, hψu, one_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (NNReal.coe_nonneg _)]

end SliceFourier

section FiniteIntegrality

open IsDedekindDomain

private theorem exists_ne_zero_forall_mem_range_of_isCompact
    (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {C : Set (FiniteAdeleRing R K)} (hC : IsCompact C) :
    ∃ s : R, s ≠ 0 ∧ ∀ k : K, algebraMap K (FiniteAdeleRing R K) k ∈ C →
      algebraMap R K s * k ∈ (algebraMap R K).range := by
  obtain ⟨s, hs0, hs⟩ :=
    FiniteAdeleRing.exists_ne_zero_forall_mul_apply_mem_adicCompletionIntegers_of_isCompact R K hC
  refine ⟨s, hs0, fun k hk => HeightOneSpectrum.mem_integers_of_valuation_le_one K _ fun v => ?_⟩
  have h := hs _ hk v

  have hcomp : (algebraMap R (FiniteAdeleRing R K) s * algebraMap K (FiniteAdeleRing R K) k) v
      = algebraMap K (v.adicCompletion K) (algebraMap R K s * k) := by
    rw [map_mul]
    rfl
  rw [hcomp, HeightOneSpectrum.mem_adicCompletionIntegers] at h

  have hval : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K s * k))
      = v.valuation K (algebraMap R K s * k) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap R K s * k)
  rw [hval] at h
  exact h

private theorem exists_ne_zero_forall_exists_coe_eq_mul_of_isCompact
    (F : Type*) [Field F] [NumberField F]
    {C : Set (FiniteAdeleRing (NumberField.RingOfIntegers F) F)} (hC : IsCompact C) :
    ∃ s : NumberField.RingOfIntegers F, s ≠ 0 ∧ ∀ ξ : F,
      algebraMap F (FiniteAdeleRing (NumberField.RingOfIntegers F) F) ξ ∈ C →
        ∃ a : NumberField.RingOfIntegers F, (a : F) = (s : F) * ξ := by
  obtain ⟨s, hs0, hs⟩ := exists_ne_zero_forall_mem_range_of_isCompact (NumberField.RingOfIntegers F) F hC
  refine ⟨s, hs0, fun ξ hξ => ?_⟩
  obtain ⟨a, ha⟩ := hs ξ hξ
  exact ⟨a, ha⟩

end FiniteIntegrality

section ArchCutoff

open NumberField Metric
open scoped Classical

variable (F : Type) [Field F] [NumberField F]

omit [NumberField F] in

private theorem continuous_archEntries : Continuous (AutomorphicForm.archEntries F) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F).comp
    (Units.continuous_val.matrix_elem i j)

private theorem exists_contDiff_hasCompactSupport_eq_comp_archEntries
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hfa : AutomorphicForm.IsArchTestFactor F fa) :
    ∃ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ ∀ g, fa g = Φ (AutomorphicForm.archEntries F g) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩ := hfa

  obtain ⟨r, hr⟩ := ((hsupp.isCompact.image (continuous_archEntries F)).isBounded).subset_closedBall
    (0 : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F)
  let χ : ContDiffBump (0 : Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) :=
    ⟨max r 1, max r 1 + 1, lt_max_of_lt_right one_pos, lt_add_one _⟩

  refine ⟨fun x => ContDiffBump.toFun χ x • Φ x, χ.contDiff.smul hΦ, χ.hasCompactSupport.smul_right,
    fun g => ?_⟩
  show fa g = ContDiffBump.toFun χ (AutomorphicForm.archEntries F g) • Φ (AutomorphicForm.archEntries F g)
  by_cases hg : fa g = 0
  ·
    rw [show Φ (AutomorphicForm.archEntries F g) = 0 from (hfaΦ g).symm.trans hg, smul_zero]
    exact hg
  ·
    have hmem : AutomorphicForm.archEntries F g ∈ closedBall (0 : Fin 2 → Fin 2 → _) χ.rIn :=
      closedBall_subset_closedBall (le_max_left r 1) (hr ⟨g, subset_tsupport _ hg, rfl⟩)
    rw [χ.one_of_mem_closedBall hmem, one_smul]
    exact hfaΦ g

end ArchCutoff

section SliceDecay

open MeasureTheory Set NumberField NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm
open NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicFourier
open scoped SchwartzMap Classical
attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)
local notation "μ𝔸" => NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F
local notation "G" => AdelicGL2 (𝓞 F) F

private def slice (f : G → ℂ) (κ γ : G) : 𝔸 → ℂ :=
  fun s => f (κ⁻¹ * γ * (unipotentGL2 s * κ))

private def SliceDecayOn (ψ : AddChar 𝔸 ℂ) (f : G → ℂ) (Θ : Set (G × G)) : Prop :=
  ∃ s : 𝓞 F, s ≠ 0 ∧ ∀ M : ℕ, ∃ B : ℝ, ∀ θ ∈ Θ, ∀ (α : 𝔸ˣ) (t : ℝ), 1 ≤ t →
    (α : 𝔸).2 = 1 → (∀ v : InfinitePlace F, ‖(α : 𝔸).1 v‖ = t) → ∀ ξ : F, ξ ≠ 0 →
      ‖fourierIntegral ψ μ𝔸 (slice F f θ.1 θ.2) ((α : 𝔸) * ι ξ)‖
          ≤ B * ∏ w : InfinitePlace F, ((1 + t * w ξ) ^ M)⁻¹ ∧
      (fourierIntegral ψ μ𝔸 (slice F f θ.1 θ.2) ((α : 𝔸) * ι ξ) ≠ 0 →
        ∃ a : 𝓞 F, (a : F) = (s : F) * ξ)

private def SliceTensorOn (f : G → ℂ) (Θ : Set (G × G))
    (g : G → G → 𝓢(mixedEmbedding.mixedSpace F, ℂ))
    (h : G → G → FiniteAdeleRing (𝓞 F) F → ℂ) : Prop :=
  ∀ θ ∈ Θ, IsLocallyConstant (h θ.1 θ.2) ∧ HasCompactSupport (h θ.1 θ.2) ∧
    slice F f θ.1 θ.2
      = fun x => g θ.1 θ.2 (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * h θ.1 θ.2 x.2

private def ArchDecayOn (ψ : AddChar 𝔸 ℂ) (Θ : Set (G × G))
    (g : G → G → 𝓢(mixedEmbedding.mixedSpace F, ℂ)) : Prop :=
  ∀ M : ℕ, ∃ A : ℝ, ∀ θ ∈ Θ, ∀ (α : 𝔸ˣ) (t : ℝ), 1 ≤ t →
    (α : 𝔸).2 = 1 → (∀ v : InfinitePlace F, ‖(α : 𝔸).1 v‖ = t) → ∀ ξ : F, ξ ≠ 0 →
      ‖fourierIntegral
          (ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
            (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
          volume (g θ.1 θ.2 : mixedEmbedding.mixedSpace F → ℂ)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F ((α : 𝔸) * ι ξ).1)‖
        ≤ A * ∏ w : InfinitePlace F, ((1 + t * w ξ) ^ M)⁻¹

private def FinSupportOn [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] (ψ : AddChar 𝔸 ℂ)
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) (Θ : Set (G × G))
    (h : G → G → FiniteAdeleRing (𝓞 F) F → ℂ) : Prop :=
  ∃ C : Set (FiniteAdeleRing (𝓞 F) F), IsCompact C ∧ ∃ Bf : ℝ, ∀ θ ∈ Θ,
    ∀ y : FiniteAdeleRing (𝓞 F) F,
      ‖fourierIntegral
          (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
          ν (h θ.1 θ.2) y‖ ≤ Bf ∧
      (fourierIntegral
          (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
          ν (h θ.1 θ.2) y ≠ 0 → y ∈ C)

private theorem sliceDecayOn_of_tensor
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ)
    (f : G → ℂ) {Θ : Set (G × G)}
    {g : G → G → 𝓢(mixedEmbedding.mixedSpace F, ℂ)}
    {h : G → G → FiniteAdeleRing (𝓞 F) F → ℂ}
    (htensor : SliceTensorOn F f Θ g h) (harch : ArchDecayOn F ψ Θ g)
    (hfin : FinSupportOn F ψ ν Θ h) :
    SliceDecayOn F ψ f Θ := by
  have hψu : ∀ a : 𝔸, ‖ψ a‖ = 1 := norm_apply_eq_one_of_isGlobalAddChar F hψ
  obtain ⟨C, hC, Bf, hfinB⟩ := hfin
  obtain ⟨s, hs0, hsC⟩ :=
    exists_ne_zero_forall_exists_coe_eq_mul_of_isCompact F hC
  refine ⟨s, hs0, fun M => ?_⟩
  obtain ⟨A, hA⟩ := harch M
  set c : ℂ := (((μ𝔸) (adelicBox F)).toReal : ℂ) /
      ((ZLattice.covolume (mixedEmbedding.integerLattice F) volume : ℂ)
        * ((ν (AdelicBox.integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)) with hcdef
  refine ⟨‖c‖ * A * Bf, ?_⟩
  intro θ hθ α t ht hαf hαa ξ hξ
  obtain ⟨hlc, hcs, hΦ⟩ := htensor θ hθ
  have hT : ∀ w : 𝔸, fourierIntegral ψ μ𝔸 (slice F f θ.1 θ.2) w
      = c * fourierIntegral
            (ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
              (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
            volume (g θ.1 θ.2 : mixedEmbedding.mixedSpace F → ℂ)
            (InfiniteAdeleRing.ringEquiv_mixedSpace F w.1)
          * fourierIntegral
            (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
            ν (h θ.1 θ.2) w.2 := by
    intro w
    rw [hΦ]
    exact fourierIntegral_pureTensor_eq F μ𝔸 ν hψ.continuous hψu (g θ.1 θ.2) hlc hcs w
  have hw2 : ((α : 𝔸) * ι ξ).2 = algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ := by
    show (α : 𝔸).2 * (ι ξ).2 = _
    rw [hαf, one_mul]
    rfl
  obtain ⟨hYb, hYC⟩ := hfinB θ hθ ((α : 𝔸) * ι ξ).2
  refine ⟨?_, fun hne => ?_⟩
  · rw [hT, norm_mul, norm_mul]
    have hX := hA θ hθ α t ht hαf hαa ξ hξ
    refine (mul_le_mul (mul_le_mul_of_nonneg_left hX (norm_nonneg _)) hYb (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans hX))).trans_eq ?_
    ring
  · rw [hT] at hne
    exact hsC ξ (hw2 ▸ hYC (right_ne_zero_of_mul hne))

end SliceDecay

section SliceTensor

open MeasureTheory Set NumberField NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm NumberField.AdelicLevel
open scoped SchwartzMap Classical

section Matrices

variable {R : Type*} [CommRing R]

private def e01 : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]

private theorem unipotentGL2_val_eq (w : R) :
    (unipotentGL2 w : Matrix (Fin 2) (Fin 2) R) = 1 + w • e01 := by
  ext i j
  rw [unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [e01]

private def sliceDirMat (k γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R :=
  ((k⁻¹ * γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) * (e01 * (k : Matrix (Fin 2) (Fin 2) R))

private theorem val_conj_unipotent (k γ : GL (Fin 2) R) (w : R) :
    ((k⁻¹ * γ * (unipotentGL2 w * k) : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
      = ((k⁻¹ * γ * k : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) + w • sliceDirMat k γ := by
  simp only [sliceDirMat, Units.val_mul, unipotentGL2_val_eq, Matrix.add_mul, Matrix.one_mul,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]

private theorem eq_zero_of_smul_sliceDirMat_eq_zero (k γ : GL (Fin 2) R) {w : R}
    (h : w • sliceDirMat k γ = 0) : w = 0 := by
  have h1 : ((k⁻¹ * γ * (unipotentGL2 w * k) : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)
      = ((k⁻¹ * γ * k : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) := by
    rw [val_conj_unipotent, h, add_zero]
  have h2 : unipotentGL2 w * k = k := mul_left_cancel (Units.ext h1)
  have h3 : unipotentGL2 w = 1 := mul_right_cancel (h2.trans (one_mul k).symm)
  have h4 := congrArg (fun M : GL (Fin 2) R => (M : Matrix (Fin 2) (Fin 2) R) 0 1) h3
  simpa [unipotentGL2_coe] using h4

private theorem unipotentGL2_inv (w : R) : (unipotentGL2 w)⁻¹ = unipotentGL2 (-w) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

private theorem continuous_unipotentGL2 [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (fun y : R => unipotentGL2 y) := by
  have hval : Continuous (fun y : R => ((unipotentGL2 y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R)) := by
    refine continuous_matrix fun i j => ?_
    simp only [unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  refine Units.continuous_iff.2 ⟨hval, ?_⟩
  simp only [unipotentGL2_inv]
  exact hval.comp continuous_neg

end Matrices

section Arch

variable (F : Type) [Field F] [NumberField F]

local notation "F∞" => InfiniteAdeleRing F
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "e∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F

private def sliceCentre (k γ : GL (Fin 2) F∞) : Fin 2 → Fin 2 → E∞ := archEntries F (k⁻¹ * γ * k)

private def sliceLin (k γ : GL (Fin 2) F∞) : E∞ →L[ℝ] (Fin 2 → Fin 2 → E∞) :=
  LinearMap.toContinuousLinearMap
    (LinearMap.pi fun i => LinearMap.pi fun j => LinearMap.mulRight ℝ (e∞ (sliceDirMat k γ i j)))

private theorem sliceLin_apply (k γ : GL (Fin 2) F∞) (v : E∞) (i j : Fin 2) :
    sliceLin F k γ v i j = v * e∞ (sliceDirMat k γ i j) := by
  simp [sliceLin]

private theorem archEntries_conj_unipotent (k γ : GL (Fin 2) F∞) (w : F∞) :
    archEntries F (k⁻¹ * γ * (unipotentGL2 w * k)) = sliceCentre F k γ + sliceLin F k γ (e∞ w) := by
  funext i j
  rw [archEntries_apply, val_conj_unipotent, Pi.add_apply, Pi.add_apply, sliceLin_apply, sliceCentre,
    archEntries_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul]

private theorem sliceLin_injective (k γ : GL (Fin 2) F∞) : Function.Injective (sliceLin F k γ) := by
  refine (injective_iff_map_eq_zero (sliceLin F k γ)).2 fun v hv => ?_
  have hv' : v = e∞ ((e∞).symm v) := ((e∞).apply_symm_apply v).symm
  have hw : (e∞).symm v • sliceDirMat k γ = 0 := by
    ext i j
    apply (e∞).injective
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, ← sliceLin_apply, ← hv', hv, Matrix.zero_apply,
      map_zero]
    rfl
  rw [hv', eq_zero_of_smul_sliceDirMat_eq_zero k γ hw, map_zero]

private theorem glArch_unipotentGL2 (x : AdeleRing (𝓞 F) F) :
    glArch (𝓞 F) F (unipotentGL2 x) = unipotentGL2 x.1 := by
  apply Units.ext
  ext i j
  rw [glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

private theorem glFin_unipotentGL2 (x : AdeleRing (𝓞 F) F) :
    glFin (𝓞 F) F (unipotentGL2 x) = unipotentGL2 x.2 := by
  apply Units.ext
  ext i j
  rw [glFin_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

end Arch

section Family

variable {F : Type} [Field F] [NumberField F]
variable {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f)

local notation "F∞" => InfiniteAdeleRing F
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "e∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F

private def archFactor : GL (Fin 2) F∞ → ℂ := hf.choose

private def finFactor : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ := hf.choose_spec.choose

private theorem isArchTestFactor_archFactor : IsArchTestFactor F (archFactor hf) :=
  hf.choose_spec.choose_spec.1

private theorem isFinTestFactor_finFactor : IsFinTestFactor F (finFactor hf) :=
  hf.choose_spec.choose_spec.2.1

private theorem apply_eq_archFactor_mul_finFactor (g : AdelicGL2 (𝓞 F) F) :
    f g = archFactor hf (glArch (𝓞 F) F g) * finFactor hf (glFin (𝓞 F) F g) :=
  hf.choose_spec.choose_spec.2.2 g

private def entryFn : (Fin 2 → Fin 2 → E∞) → ℂ :=
  (exists_contDiff_hasCompactSupport_eq_comp_archEntries F (isArchTestFactor_archFactor hf)).choose

private theorem contDiff_entryFn : ContDiff ℝ (⊤ : ℕ∞) (entryFn hf) :=
  (exists_contDiff_hasCompactSupport_eq_comp_archEntries F (isArchTestFactor_archFactor hf)).choose_spec.1

private theorem hasCompactSupport_entryFn : HasCompactSupport (entryFn hf) :=
  (exists_contDiff_hasCompactSupport_eq_comp_archEntries F
    (isArchTestFactor_archFactor hf)).choose_spec.2.1

private theorem archFactor_eq_entryFn (g : GL (Fin 2) F∞) : archFactor hf g = entryFn hf (archEntries F g) :=
  (exists_contDiff_hasCompactSupport_eq_comp_archEntries F
    (isArchTestFactor_archFactor hf)).choose_spec.2.2 g

private def sliceArch (κ γ : AdelicGL2 (𝓞 F) F) : 𝓢(E∞, ℂ) where
  toFun v := entryFn hf
    (sliceCentre F (glArch (𝓞 F) F κ) (glArch (𝓞 F) F γ)
      + sliceLin F (glArch (𝓞 F) F κ) (glArch (𝓞 F) F γ) v)
  smooth' := (contDiff_entryFn hf).comp
    (contDiff_const.add (sliceLin F (glArch (𝓞 F) F κ) (glArch (𝓞 F) F γ)).contDiff)
  decay' := by
    intro a n
    obtain ⟨-, hC⟩ :=
      exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport
        (P := Unit) (contDiff_entryFn hf) (hasCompactSupport_entryFn hf) isCompact_singleton
        (c := fun _ => sliceCentre F (glArch (𝓞 F) F κ) (glArch (𝓞 F) F γ))
        (ℓ := fun _ => sliceLin F (glArch (𝓞 F) F κ) (glArch (𝓞 F) F γ))
        continuousOn_const continuousOn_const (fun _ _ => sliceLin_injective F _ _)
    obtain ⟨C, hC'⟩ := hC a n
    exact ⟨C, fun v => hC' () (Set.mem_singleton _) v⟩

private theorem sliceArch_apply (κ γ : AdelicGL2 (𝓞 F) F) (v : E∞) :
    sliceArch hf κ γ v = archFactor hf ((glArch (𝓞 F) F κ)⁻¹ * glArch (𝓞 F) F γ
      * (unipotentGL2 ((e∞).symm v) * glArch (𝓞 F) F κ)) := by
  rw [archFactor_eq_entryFn, archEntries_conj_unipotent, RingEquiv.apply_symm_apply]
  rfl

private def sliceFin (κ γ : AdelicGL2 (𝓞 F) F) : FiniteAdeleRing (𝓞 F) F → ℂ :=
  fun y => finFactor hf ((glFin (𝓞 F) F κ)⁻¹ * glFin (𝓞 F) F γ
    * (unipotentGL2 y * glFin (𝓞 F) F κ))

private theorem continuous_conj_unipotentGL2 {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (a b : GL (Fin 2) R) : Continuous (fun y : R => a * (unipotentGL2 y * b)) :=
  continuous_const.mul (continuous_unipotentGL2.mul continuous_const)

private theorem isLocallyConstant_sliceFin (κ γ : AdelicGL2 (𝓞 F) F) :
    IsLocallyConstant (sliceFin hf κ γ) :=
  (isFinTestFactor_finFactor hf).1.comp_continuous (continuous_conj_unipotentGL2 _ _)

private theorem entry_unconj {R : Type*} [CommRing R] (a b : GL (Fin 2) R) (y : R) :
    ((a⁻¹ * (a * (unipotentGL2 y * b)) * b⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 = y := by
  rw [show a⁻¹ * (a * (unipotentGL2 y * b)) * b⁻¹ = unipotentGL2 y by group, unipotentGL2_coe]
  rfl

private theorem continuous_readOff {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (a b : GL (Fin 2) R) :
    Continuous fun M : GL (Fin 2) R => ((a⁻¹ * M * b⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 1 :=
  (Units.continuous_val.comp ((continuous_const.mul continuous_id).mul continuous_const)).matrix_elem 0 1

private theorem hasCompactSupport_sliceFin (κ γ : AdelicGL2 (𝓞 F) F) :
    HasCompactSupport (sliceFin hf κ γ) := by
  refine HasCompactSupport.intro
    ((isFinTestFactor_finFactor hf).2.isCompact.image
      (continuous_readOff ((glFin (𝓞 F) F κ)⁻¹ * glFin (𝓞 F) F γ) (glFin (𝓞 F) F κ)))
    fun y hy => ?_
  by_contra hne
  exact hy ⟨(glFin (𝓞 F) F κ)⁻¹ * glFin (𝓞 F) F γ * (unipotentGL2 y * glFin (𝓞 F) F κ),
    subset_tsupport _ hne, entry_unconj _ _ y⟩

private theorem sliceTensorOn (Θ : Set (AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F)) :
    SliceTensorOn F f Θ (sliceArch hf) (sliceFin hf) := by
  intro θ _
  refine ⟨isLocallyConstant_sliceFin hf θ.1 θ.2, hasCompactSupport_sliceFin hf θ.1 θ.2,
    funext fun x => ?_⟩
  show slice F f θ.1 θ.2 x
    = sliceArch hf θ.1 θ.2 (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) * sliceFin hf θ.1 θ.2 x.2
  rw [sliceArch_apply, RingEquiv.symm_apply_apply]
  simp only [slice, sliceFin, apply_eq_archFactor_mul_finFactor hf, map_mul, map_inv,
    glArch_unipotentGL2, glFin_unipotentGL2]

end Family

end SliceTensor

section FourierDecay

open MeasureTheory Real VectorFourier
open scoped FourierTransform

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

private theorem pow_mul_norm_fourierIntegral_le_of_coercive (L : V →L[ℝ] W →L[ℝ] ℝ)
    {μ : Measure V} [μ.IsAddHaarMeasure] {f : V → E} {n : ℕ} (hf : ContDiff ℝ n f)
    (h'f : ∀ j : ℕ, j ≤ n → Integrable (fun v => ‖iteratedFDeriv ℝ j f v‖) μ)
    {c : ℝ} (hc : 0 ≤ c) (hL : ∀ w : W, ∃ v : V, ‖v‖ ≤ 1 ∧ c * ‖w‖ ≤ ‖L v w‖) (w : W) :
    (c * ‖w‖) ^ n * ‖fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖
      ≤ 2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂μ := by
  obtain ⟨v, hv1, hvw⟩ := hL w
  have h'f' : ∀ (k j : ℕ), (k : ℕ∞) ≤ (0 : ℕ) → (j : ℕ∞) ≤ (n : ℕ) →
      Integrable (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ j f x‖) μ := by
    intro k j hk hj
    have hk0 : k = 0 := by exact_mod_cast (nonpos_iff_eq_zero.mp (by exact_mod_cast hk))
    subst hk0
    simpa using h'f j (by exact_mod_cast hj)
  have key := pow_mul_norm_iteratedFDeriv_fourierIntegral_le L (K := (0 : ℕ)) (N := (n : ℕ))
    (hf := hf) h'f' (k := 0) (n := n) le_rfl le_rfl v w
  rw [norm_iteratedFDeriv_zero, pow_zero, mul_one] at key
  have hsum : ∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (n + 1),
        ∫ x, ‖x‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 f x‖ ∂μ
      = ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
    rw [Finset.sum_product, zero_add, Finset.range_one, Finset.sum_singleton]
    simp
  rw [hsum] at key
  have hS : 0 ≤ ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun x => norm_nonneg _
  calc (c * ‖w‖) ^ n * ‖fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖
      ≤ |L v w| ^ n * ‖fourierIntegral 𝐞 μ L.toLinearMap₁₂ f w‖ := by
        gcongr
        exact hvw.trans_eq (Real.norm_eq_abs _)
    _ ≤ ‖v‖ ^ n * (2 * 0 + 2) ^ n
          * ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
        simpa using key
    _ ≤ 1 ^ n * (2 * 0 + 2) ^ n
          * ∑ j ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ j f x‖ ∂μ := by
        gcongr
    _ = 2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ v, ‖iteratedFDeriv ℝ j f v‖ ∂μ := by norm_num

end FourierDecay

section TraceCoercive

open Finset

private theorem trace_pi_apply {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] [Fintype ι] (x : ι → S) :
    Algebra.trace R (ι → S) x = ∑ i, Algebra.trace R S (x i) := by
  classical
  let b := Module.Free.chooseBasis R S
  rw [Algebra.trace_eq_matrix_trace (Pi.basis fun _ : ι => b) x]
  simp_rw [Algebra.trace_eq_matrix_trace b]
  simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_apply,
    Pi.basis_repr, Pi.mul_apply, Pi.single_eq_same]
  exact Fintype.sum_sigma (fun ik : (Σ _ : ι, Module.Free.ChooseBasisIndex R S) =>
    b.repr (x ik.1 * b ik.2) ik.2)

private theorem trace_realProdComplex_apply {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (w : (ι₁ → ℝ) × (ι₂ → ℂ)) :
    Algebra.trace ℝ ((ι₁ → ℝ) × (ι₂ → ℂ)) w = ∑ r, w.1 r + ∑ c, 2 * (w.2 c).re := by
  rw [Algebra.trace_prod_apply, trace_pi_apply, trace_pi_apply]
  simp only [Algebra.trace_self_apply, Algebra.trace_complex_apply]

section CLM

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

private def bilinFormCLM (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (V →L[ℝ] ℝ)).toLinearMap ∘ₗ B)

@[scoped simp] private theorem bilinFormCLM_apply (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v w : V) :
    bilinFormCLM V B v w = B v w := rfl

private theorem toLinearMap₁₂_bilinFormCLM (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    (bilinFormCLM V B).toLinearMap₁₂ = B := by
  ext v w
  rfl

end CLM

private theorem re_conj_mul_self (z : ℂ) : (starRingEnd ℂ z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem traceForm_coercive {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (w : (ι₁ → ℝ) × (ι₂ → ℂ)) :
    ∃ v : (ι₁ → ℝ) × (ι₂ → ℂ), ‖v‖ ≤ 1 ∧
      1 * ‖w‖ ≤ ‖Algebra.traceForm ℝ ((ι₁ → ℝ) × (ι₂ → ℂ)) v w‖ := by

  set S : ℝ := ∑ r, w.1 r ^ 2 + ∑ c, 2 * ‖w.2 c‖ ^ 2 with hS
  have hS1 : 0 ≤ ∑ r, w.1 r ^ 2 := Finset.sum_nonneg fun r _ => sq_nonneg _
  have hS2 : 0 ≤ ∑ c, 2 * ‖w.2 c‖ ^ 2 :=
    Finset.sum_nonneg fun c _ => mul_nonneg zero_le_two (sq_nonneg _)
  have hS0 : 0 ≤ S := add_nonneg hS1 hS2

  have h1 : ‖w.1‖ ≤ Real.sqrt S := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).2 fun r => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    calc w.1 r ^ 2 ≤ ∑ r, w.1 r ^ 2 :=
          Finset.single_le_sum (f := fun r => w.1 r ^ 2) (fun i _ => sq_nonneg _) (mem_univ r)
      _ ≤ S := le_add_of_nonneg_right hS2
  have h2 : ‖w.2‖ ≤ Real.sqrt S := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg S)).2 fun c => ?_
    refine Real.le_sqrt_of_sq_le ?_
    calc ‖w.2 c‖ ^ 2 ≤ 2 * ‖w.2 c‖ ^ 2 := by nlinarith [sq_nonneg ‖w.2 c‖]
      _ ≤ ∑ c, 2 * ‖w.2 c‖ ^ 2 :=
          Finset.single_le_sum (f := fun c => 2 * ‖w.2 c‖ ^ 2)
            (fun i _ => mul_nonneg zero_le_two (sq_nonneg _)) (mem_univ c)
      _ ≤ S := le_add_of_nonneg_left hS1
  have hw : ‖w‖ ≤ Real.sqrt S := by
    rw [Prod.norm_def]; exact max_le h1 h2
  have hww : ‖w‖ * ‖w‖ ≤ S := by
    calc ‖w‖ * ‖w‖ ≤ Real.sqrt S * Real.sqrt S :=
          mul_le_mul hw hw (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = S := Real.mul_self_sqrt hS0

  set v₀ : (ι₁ → ℝ) × (ι₂ → ℂ) := (w.1, fun c => starRingEnd ℂ (w.2 c)) with hv₀
  have hv₀_norm : ‖v₀‖ ≤ ‖w‖ := by
    rw [Prod.norm_def, Prod.norm_def]
    refine max_le_max le_rfl ?_
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun c => ?_
    show ‖starRingEnd ℂ (w.2 c)‖ ≤ ‖w.2‖
    rw [Complex.norm_conj]
    exact norm_le_pi_norm (w.2) c
  have htr : Algebra.trace ℝ ((ι₁ → ℝ) × (ι₂ → ℂ)) (v₀ * w) = S := by
    rw [trace_realProdComplex_apply]
    simp only [hv₀, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, re_conj_mul_self, hS]
    congr 1
    exact Finset.sum_congr rfl fun r _ => by ring
  refine ⟨‖w‖⁻¹ • v₀, ?_, ?_⟩
  ·
    rw [norm_smul, norm_inv, norm_norm]
    calc ‖w‖⁻¹ * ‖v₀‖ ≤ ‖w‖⁻¹ * ‖w‖ :=
          mul_le_mul_of_nonneg_left hv₀_norm (inv_nonneg.2 (norm_nonneg _))
      _ = ‖w‖ / ‖w‖ := inv_mul_eq_div _ _
      _ ≤ 1 := div_self_le_one _
  ·
    rw [one_mul, Algebra.traceForm_apply, smul_mul_assoc, map_smul, smul_eq_mul, htr,
      Real.norm_of_nonneg (mul_nonneg (inv_nonneg.2 (norm_nonneg _)) hS0)]
    rcases (norm_nonneg w).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · exact (le_inv_mul_iff₀ hpos).2 hww

open scoped Classical in
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding in

private theorem traceForm_mixedSpace_coercive (F : Type*) [Field F] [NumberField F] (w : mixedSpace F) :
    ∃ v : mixedSpace F, ‖v‖ ≤ 1 ∧
      1 * ‖w‖ ≤ ‖bilinFormCLM (mixedSpace F) (Algebra.traceForm ℝ (mixedSpace F)) v w‖ := by
  simpa only [bilinFormCLM_apply] using traceForm_coercive w

end TraceCoercive

section ArchFourierTrace

open MeasureTheory

private theorem fourierIntegral_eq_vectorFourier_traceForm
    {A : Type*} [CommRing A] [Algebra ℝ A] [MeasurableSpace A]
    (ψ : AddChar A ℂ) (hψ : ∀ a : A, ψ a = ((Real.fourierChar (Algebra.trace ℝ A a) : Circle) : ℂ))
    (μ : Measure A) (f : A → ℂ) (w : A) :
    NumberField.AdelicFourier.fourierIntegral ψ μ f w
      = VectorFourier.fourierIntegral Real.fourierChar μ (Algebra.traceForm ℝ A) f w := by
  simp only [NumberField.AdelicFourier.fourierIntegral, VectorFourier.fourierIntegral, hψ,
    Circle.smul_def, smul_eq_mul, Algebra.traceForm_apply, map_neg]

end ArchFourierTrace

section ArchDecay

open MeasureTheory Set NumberField NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm NumberField.AdelicLevel NumberField.AdelicFourier
open scoped SchwartzMap Classical

private theorem one_add_pow_le {x : ℝ} (hx : 0 ≤ x) (N : ℕ) : (1 + x) ^ N ≤ 2 ^ N * (x ^ N + 1) := by
  have h2 : 1 + x ≤ 2 * max x 1 := by
    rcases le_total x 1 with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  calc (1 + x) ^ N ≤ (2 * max x 1) ^ N := pow_le_pow_left₀ (by positivity) h2 N
    _ = 2 ^ N * (max x 1) ^ N := mul_pow 2 (max x 1) N
    _ ≤ 2 ^ N * (x ^ N + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rcases le_total x 1 with h | h
        · rw [max_eq_right h, one_pow]; linarith [pow_nonneg hx N]
        · rw [max_eq_left h]; linarith

section Places

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)
local notation "F∞" => InfiniteAdeleRing F
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "e∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F

private theorem norm_apply_le_norm_ringEquiv (x : F∞) (w : InfinitePlace F) : ‖x w‖ ≤ ‖e∞ x‖ := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply, Prod.norm_def]
  rcases w.isReal_or_isComplex with hw | hw
  · refine le_trans ?_ (le_max_left _ _)
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) (x w)]
    exact norm_le_pi_norm
      (fun v : {w : InfinitePlace F // w.IsReal} =>
        InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v.1)) ⟨w, hw⟩
  · refine le_trans ?_ (le_max_right _ _)
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) (x w)]
    exact norm_le_pi_norm
      (fun v : {w : InfinitePlace F // w.IsComplex} =>
        InfinitePlace.Completion.extensionEmbedding v.1 (x v.1)) ⟨w, hw⟩

omit [NumberField F] in

private theorem norm_algebraMap_completion (w : InfinitePlace F) (ξ : F) :
    ‖algebraMap F w.Completion ξ‖ = w ξ := by
  rw [show algebraMap F w.Completion ξ = (((WithAbs.equiv w.1).symm ξ : WithAbs w.1) : w.Completion)
    from rfl, InfinitePlace.Completion.norm_coe]
  rfl

private theorem norm_archMul_apply (α : 𝔸ˣ) (t : ℝ) (hαa : ∀ v : InfinitePlace F, ‖(α : 𝔸).1 v‖ = t)
    (ξ : F) (w : InfinitePlace F) : ‖((α : 𝔸) * ι ξ).1 w‖ = t * w ξ := by
  rw [show ((α : 𝔸) * ι ξ).1 w = (α : 𝔸).1 w * algebraMap F w.Completion ξ from rfl, norm_mul, hαa w,
    norm_algebraMap_completion]

private theorem prod_one_add_mul_pow_le (α : 𝔸ˣ) (t : ℝ) (ht : 1 ≤ t)
    (hαa : ∀ v : InfinitePlace F, ‖(α : 𝔸).1 v‖ = t) (ξ : F) (M : ℕ) :
    ∏ w : InfinitePlace F, (1 + t * w ξ) ^ M
      ≤ (1 + ‖e∞ ((α : 𝔸) * ι ξ).1‖) ^ (M * Fintype.card (InfinitePlace F)) := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  calc ∏ w : InfinitePlace F, (1 + t * w ξ) ^ M
      ≤ ∏ _w : InfinitePlace F, (1 + ‖e∞ ((α : 𝔸) * ι ξ).1‖) ^ M := by
        refine Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_
        refine pow_le_pow_left₀ (by positivity) ?_ M
        rw [← norm_archMul_apply F α t hαa ξ w]
        exact add_le_add le_rfl (norm_apply_le_norm_ringEquiv F _ w)
    _ = (1 + ‖e∞ ((α : 𝔸) * ι ξ).1‖) ^ (M * Fintype.card (InfinitePlace F)) := by
        rw [Finset.prod_const, Finset.card_univ, pow_mul]

end Places

section Affine

variable (F : Type) [Field F] [NumberField F]

local notation "F∞" => InfiniteAdeleRing F
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "e∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F

private theorem continuous_conj {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous fun q : GL (Fin 2) R × GL (Fin 2) R => q.1⁻¹ * q.2 * q.1 :=
  (continuous_fst.inv.mul continuous_snd).mul continuous_fst

private theorem continuous_sliceDirMat_apply {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (i j : Fin 2) :
    Continuous fun q : GL (Fin 2) R × GL (Fin 2) R => sliceDirMat q.1 q.2 i j := by
  have h1 : Continuous fun q : GL (Fin 2) R × GL (Fin 2) R =>
      ((q.1⁻¹ * q.2 : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) :=
    Units.continuous_val.comp (continuous_fst.inv.mul continuous_snd)
  have h2 : Continuous fun q : GL (Fin 2) R × GL (Fin 2) R => e01 * (q.1 : Matrix (Fin 2) (Fin 2) R) :=
    continuous_const.mul (Units.continuous_val.comp continuous_fst)
  exact (h1.mul h2).matrix_elem i j

omit [NumberField F] in
private theorem continuous_sliceCentre :
    Continuous fun q : GL (Fin 2) F∞ × GL (Fin 2) F∞ => sliceCentre F q.1 q.2 :=
  (continuous_archEntries F).comp continuous_conj

private theorem continuous_sliceLin :
    Continuous fun q : GL (Fin 2) F∞ × GL (Fin 2) F∞ => sliceLin F q.1 q.2 := by
  refine continuous_clm_apply.2 fun v => continuous_pi fun i => continuous_pi fun j => ?_
  simp only [sliceLin_apply]
  exact continuous_const.mul
    ((NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F).comp
      (continuous_sliceDirMat_apply i j))

end Affine

section Uniform

variable {F : Type} [Field F] [NumberField F]
variable {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f)

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)
local notation "F∞" => InfiniteAdeleRing F
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "e∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F
local notation "G" => AdelicGL2 (𝓞 F) F

private theorem coe_sliceArch (κ γ : G) :
    ⇑(sliceArch hf κ γ) = fun v => entryFn hf
      (sliceCentre F (glArch (𝓞 F) F κ) (glArch (𝓞 F) F γ)
        + sliceLin F (glArch (𝓞 F) F κ) (glArch (𝓞 F) F γ) v) :=
  rfl

private theorem isCompact_image_glArch_pair {Θ : Set (G × G)} (hΘ : IsCompact Θ) :
    IsCompact ((fun θ : G × G => (glArch (𝓞 F) F θ.1, glArch (𝓞 F) F θ.2)) '' Θ) :=
  hΘ.image (((continuous_glArch (𝓞 F) F).comp continuous_fst).prodMk
    ((continuous_glArch (𝓞 F) F).comp continuous_snd))

private theorem uniform_support_and_bounds {Θ : Set (G × G)} (hΘ : IsCompact Θ) :
    (∃ S : Set E∞, IsCompact S ∧ ∀ θ ∈ Θ, tsupport (⇑(sliceArch hf θ.1 θ.2)) ⊆ S) ∧
      ∀ j : ℕ, ∃ C : ℝ, ∀ θ ∈ Θ, ∀ v : E∞, ‖iteratedFDeriv ℝ j (⇑(sliceArch hf θ.1 θ.2)) v‖ ≤ C := by
  obtain ⟨hS, hC⟩ :=
    exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport
      (contDiff_entryFn hf) (hasCompactSupport_entryFn hf) (isCompact_image_glArch_pair hΘ)
      (c := fun q : GL (Fin 2) F∞ × GL (Fin 2) F∞ => sliceCentre F q.1 q.2)
      (ℓ := fun q : GL (Fin 2) F∞ × GL (Fin 2) F∞ => sliceLin F q.1 q.2)
      (continuous_sliceCentre F).continuousOn (continuous_sliceLin F).continuousOn
      (fun q _ => sliceLin_injective F q.1 q.2)
  refine ⟨?_, fun j => ?_⟩
  · obtain ⟨S, hS, hsub⟩ := hS
    refine ⟨S, hS, fun θ hθ => ?_⟩
    rw [coe_sliceArch]
    exact hsub (glArch (𝓞 F) F θ.1, glArch (𝓞 F) F θ.2) ⟨θ, hθ, rfl⟩
  · obtain ⟨C, hC'⟩ := hC 0 j
    refine ⟨C, fun θ hθ v => ?_⟩
    have h := hC' (glArch (𝓞 F) F θ.1, glArch (𝓞 F) F θ.2) ⟨θ, hθ, rfl⟩ v
    rw [pow_zero, one_mul] at h
    rw [coe_sliceArch]
    exact h

private theorem integral_norm_iteratedFDeriv_le {Θ : Set (AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F)} (hΘ : IsCompact Θ)
    (j : ℕ) :
    ∃ C : ℝ, ∀ θ ∈ Θ,
      Integrable (fun v => ‖iteratedFDeriv ℝ j (⇑(sliceArch hf θ.1 θ.2)) v‖) volume ∧
        ∫ v, ‖iteratedFDeriv ℝ j (⇑(sliceArch hf θ.1 θ.2)) v‖ ≤ C := by
  obtain ⟨⟨S, hS, hsub⟩, hC⟩ := uniform_support_and_bounds hf hΘ
  obtain ⟨C, hC'⟩ := hC j
  refine ⟨C * volume.real S, fun θ hθ => ?_⟩
  have hcs : HasCompactSupport (⇑(sliceArch hf θ.1 θ.2)) :=
    IsCompact.of_isClosed_subset hS (isClosed_tsupport _) (hsub θ hθ)
  have hcont : Continuous fun v => iteratedFDeriv ℝ j (⇑(sliceArch hf θ.1 θ.2)) v :=
    ((sliceArch hf θ.1 θ.2).smooth ⊤).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hint : Integrable (fun v => ‖iteratedFDeriv ℝ j (⇑(sliceArch hf θ.1 θ.2)) v‖) volume :=
    (hcont.norm).integrable_of_hasCompactSupport (hcs.iteratedFDeriv j).norm
  refine ⟨hint, ?_⟩

  have hzero : ∀ v, v ∉ S → ‖iteratedFDeriv ℝ j (⇑(sliceArch hf θ.1 θ.2)) v‖ = 0 := by
    intro v hv
    rw [norm_eq_zero]
    exact image_eq_zero_of_notMem_tsupport fun h =>
      hv (hsub θ hθ (tsupport_iteratedFDeriv_subset j h))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  refine (Real.le_norm_self _).trans ?_
  refine norm_setIntegral_le_of_norm_le_const hS.measure_lt_top fun v _ => ?_
  rw [norm_norm]
  exact hC' θ hθ v

private theorem pow_mul_norm_fourierIntegral_le {Θ : Set (AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F)}
    (hΘ : IsCompact Θ) (N : ℕ) {ψ : AddChar 𝔸 ℂ}
    (hψa : ∀ a : E∞,
      ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom) a
          = ((Real.fourierChar (Algebra.trace ℝ E∞ a) : Circle) : ℂ)) :
    ∃ B : ℝ, ∀ θ ∈ Θ, ∀ η : E∞,
      ‖η‖ ^ N * ‖fourierIntegral
          (ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
            (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
          volume (⇑(sliceArch hf θ.1 θ.2)) η‖ ≤ B := by
  choose C hC using fun j => integral_norm_iteratedFDeriv_le hf hΘ j
  refine ⟨2 ^ N * ∑ j ∈ Finset.range (N + 1), C j, fun θ hθ η => ?_⟩
  rw [fourierIntegral_eq_vectorFourier_traceForm _ hψa volume (⇑(sliceArch hf θ.1 θ.2)) η,
    ← toLinearMap₁₂_bilinFormCLM E∞ (Algebra.traceForm ℝ E∞)]
  have key := pow_mul_norm_fourierIntegral_le_of_coercive
    (bilinFormCLM E∞ (Algebra.traceForm ℝ E∞)) (μ := volume) (n := N)
    ((sliceArch hf θ.1 θ.2).smooth N) (fun j _ => (hC j θ hθ).1) zero_le_one
    (traceForm_mixedSpace_coercive F) η
  rw [one_mul] at key
  refine key.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => (hC j θ hθ).2) ?_)
  positivity

private theorem one_add_norm_pow_mul_norm_fourierIntegral_le {Θ : Set (AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F)}
    (hΘ : IsCompact Θ) (N : ℕ) {ψ : AddChar 𝔸 ℂ}
    (hψa : ∀ a : E∞,
      ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom) a
          = ((Real.fourierChar (Algebra.trace ℝ E∞ a) : Circle) : ℂ)) :
    ∃ B : ℝ, ∀ θ ∈ Θ, ∀ η : E∞,
      (1 + ‖η‖) ^ N * ‖fourierIntegral
          (ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
            (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
          volume (⇑(sliceArch hf θ.1 θ.2)) η‖ ≤ B := by
  obtain ⟨BN, hBN⟩ := pow_mul_norm_fourierIntegral_le hf hΘ N hψa
  obtain ⟨B0, hB0⟩ := pow_mul_norm_fourierIntegral_le hf hΘ 0 hψa
  refine ⟨2 ^ N * (BN + B0), fun θ hθ η => ?_⟩
  have hN := hBN θ hθ η
  have h0 := hB0 θ hθ η
  rw [pow_zero, one_mul] at h0
  have hX := norm_nonneg (fourierIntegral
    (ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
    volume (⇑(sliceArch hf θ.1 θ.2)) η)
  calc (1 + ‖η‖) ^ N * _ ≤ 2 ^ N * (‖η‖ ^ N + 1) * _ :=
        mul_le_mul_of_nonneg_right (one_add_pow_le (norm_nonneg η) N) hX
    _ = 2 ^ N * (‖η‖ ^ N * _ + _) := by ring
    _ ≤ 2 ^ N * (BN + B0) := mul_le_mul_of_nonneg_left (add_le_add hN h0) (by positivity)

end Uniform

section Main

variable {F : Type} [Field F] [NumberField F]
variable {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f)

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "e∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F

private theorem archDecayOn {Θ : Set (AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F)} (hΘ : IsCompact Θ)
    {ψ : AddChar 𝔸 ℂ}
    (hψa : ∀ a : E∞,
      ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom) a
          = ((Real.fourierChar (Algebra.trace ℝ E∞ a) : Circle) : ℂ)) :
    ArchDecayOn F ψ Θ (sliceArch hf) := by
  intro M
  obtain ⟨B, hB⟩ :=
    one_add_norm_pow_mul_norm_fourierIntegral_le hf hΘ (M * Fintype.card (InfinitePlace F)) hψa
  refine ⟨B, ?_⟩
  intro θ hθ α t ht hαf hαa ξ hξ
  have key := hB θ hθ (e∞ ((α : 𝔸) * ι ξ).1)
  have hprod := prod_one_add_mul_pow_le F α t ht hαa ξ M
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hpos : 0 < ∏ w : InfinitePlace F, (1 + t * w ξ) ^ M :=
    Finset.prod_pos fun w _ => pow_pos (by positivity) M
  rw [Finset.prod_inv_distrib]
  refine (le_mul_inv_iff₀ hpos).2 ?_
  calc _ * ∏ w : InfinitePlace F, (1 + t * w ξ) ^ M
      ≤ _ * (1 + ‖e∞ ((α : 𝔸) * ι ξ).1‖) ^ (M * Fintype.card (InfinitePlace F)) :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = (1 + ‖e∞ ((α : 𝔸) * ι ξ).1‖) ^ (M * Fintype.card (InfinitePlace F)) * _ := mul_comm _ _
    _ ≤ B := key

end Main

end ArchDecay

section FinSupport

open MeasureTheory Set NumberField NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm NumberField.AdelicLevel
open NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicFourier
open scoped SchwartzMap Classical
attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "𝔸f" => FiniteAdeleRing (𝓞 F) F
local notation "F∞" => InfiniteAdeleRing F
local notation "E∞" => mixedEmbedding.mixedSpace F
local notation "e∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F
local notation "μ𝔸" => NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F

private def stdBump : ContDiffBump (0 : E∞) := ⟨1, 2, one_pos, one_lt_two⟩

private def testFn : E∞ → ℂ := fun v => ((ContDiffBump.toFun (stdBump F) v : ℝ) : ℂ)

private theorem contDiff_testFn : ContDiff ℝ (⊤ : ℕ∞) (testFn F) :=
  Complex.ofRealCLM.contDiff.comp (stdBump F).contDiff

private theorem hasCompactSupport_testFn : HasCompactSupport (testFn F) :=
  (stdBump F).hasCompactSupport.comp_left Complex.ofReal_zero

private theorem integral_testFn_ne_zero : ∫ v, testFn F v ≠ 0 := by
  unfold testFn
  rw [integral_complex_ofReal, Ne, Complex.ofReal_eq_zero]
  exact ((stdBump F).integral_pos (μ := volume)).ne'

private def testSchwartz : 𝓢(E∞, ℂ) where
  toFun v := testFn F ((0 : E∞) + ContinuousLinearMap.id ℝ E∞ v)
  smooth' := (contDiff_testFn F).comp (contDiff_const.add (ContinuousLinearMap.id ℝ E∞).contDiff)
  decay' := by
    intro a n
    obtain ⟨-, hC⟩ :=
      exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport
        (P := Unit) (contDiff_testFn F) (hasCompactSupport_testFn F) isCompact_singleton
        (c := fun _ => (0 : E∞)) (ℓ := fun _ => ContinuousLinearMap.id ℝ E∞)
        continuousOn_const continuousOn_const (fun _ _ => Function.injective_id)
    obtain ⟨C, hC'⟩ := hC a n
    exact ⟨C, fun v => hC' () (Set.mem_singleton _) v⟩

private theorem testSchwartz_apply (v : E∞) : testSchwartz F v = testFn F v := by
  show testFn F ((0 : E∞) + v) = _
  rw [zero_add]

private theorem fourierIntegral_testSchwartz_zero (ψA : AddChar E∞ ℂ) :
    fourierIntegral ψA volume (⇑(testSchwartz F)) 0 = ∫ v, testFn F v := by
  simp only [fourierIntegral, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul,
    testSchwartz_apply]

variable {F}

private theorem bounded_and_hasCompactSupport_of_mem_schwartzBruhat {Φ : 𝔸 → ℂ}
    (hΦ : Φ ∈ schwartzBruhat F) :
    (∃ B : ℝ, ∀ y : 𝔸f, ‖Φ ((0 : F∞), y)‖ ≤ B) ∧ HasCompactSupport (fun y : 𝔸f => Φ ((0 : F∞), y)) := by
  refine schwartzBruhat_induction (p := fun Φ _ =>
    (∃ B : ℝ, ∀ y : 𝔸f, ‖Φ ((0 : F∞), y)‖ ≤ B) ∧ HasCompactSupport (fun y : 𝔸f => Φ ((0 : F∞), y)))
    ?_ ?_ ?_ ?_ hΦ
  · rintro _ ⟨g, h, hlc, hcs, rfl⟩
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hlc.continuous
    refine ⟨⟨‖g (e∞ 0)‖ * C, fun y => ?_⟩, ?_⟩
    · show ‖g (e∞ 0) * h y‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg _)
    · show HasCompactSupport (fun y => g (e∞ 0) * h y)
      exact hcs.mul_left (f := fun _ => g (e∞ 0))
  · refine ⟨⟨0, fun y => ?_⟩, ?_⟩
    · rw [show (0 : 𝔸 → ℂ) ((0 : F∞), y) = 0 from rfl, norm_zero]
    · exact HasCompactSupport.intro isCompact_empty fun _ _ => rfl
  · rintro Φ₁ Φ₂ - - ⟨⟨B₁, hB₁⟩, hc₁⟩ ⟨⟨B₂, hB₂⟩, hc₂⟩
    refine ⟨⟨B₁ + B₂, fun y => ?_⟩, hc₁.add hc₂⟩
    exact (norm_add_le _ _).trans (add_le_add (hB₁ y) (hB₂ y))
  · rintro c Φ - ⟨⟨B, hB⟩, hc⟩
    refine ⟨⟨‖c‖ * B, fun y => ?_⟩, hc.smul_left (f := fun _ => c)⟩
    show ‖c • Φ ((0 : F∞), y)‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hB y) (norm_nonneg _)

private theorem bounded_and_hasCompactSupport_finTransform
    [MeasurableSpace 𝔸f] [BorelSpace 𝔸f] (ν : Measure 𝔸f) [ν.IsAddHaarMeasure]
    {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ)
    {h : 𝔸f → ℂ} (hlc : IsLocallyConstant h) (hcs : HasCompactSupport h) :
    (∃ B : ℝ, ∀ y : 𝔸f,
      ‖fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f)) ν h y‖ ≤ B) ∧
      HasCompactSupport
        (fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f)) ν h) := by
  have hψu : ∀ a : 𝔸, ‖ψ a‖ = 1 := norm_apply_eq_one_of_isGlobalAddChar F hψ

  have hmem : (fun x : 𝔸 => testSchwartz F (e∞ x.1) * h x.2) ∈ schwartzBruhat F :=
    mem_schwartzBruhat_of_mem_pureTensorSet (tensor_mem_pureTensorSet (testSchwartz F) h hlc hcs)
  obtain ⟨⟨B, hB⟩, hcsF⟩ := bounded_and_hasCompactSupport_of_mem_schwartzBruhat
    (fourierIntegral_mem_schwartzBruhat F μ𝔸 hψ hmem)

  set c : ℂ := (((μ𝔸) (adelicBox F)).toReal : ℂ) /
      ((ZLattice.covolume (mixedEmbedding.integerLattice F) volume : ℂ)
        * ((ν (AdelicBox.integralFiniteAdeles (𝓞 F) F)).toReal : ℂ)) with hcdef
  set I : ℂ := fourierIntegral
      (ψ.compAddMonoidHom ((AddMonoidHom.inl (InfiniteAdeleRing F) 𝔸f).comp
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom))
      volume (⇑(testSchwartz F)) (e∞ 0) with hIdef
  have hc0 : c ≠ 0 := by
    have h1 : ((μ𝔸) (adelicBox F)).toReal ≠ 0 := ENNReal.toReal_ne_zero.2
      ⟨(measure_adelicBox_pos F μ𝔸).ne', (measure_adelicBox_lt_top F μ𝔸).ne⟩
    have h2 : ZLattice.covolume (mixedEmbedding.integerLattice F) volume ≠ 0 :=
      (ZLattice.covolume_pos (mixedEmbedding.integerLattice F) volume).ne'
    have h0O : (0 : 𝔸f) ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F := fun v => by
      rw [show (0 : 𝔸f) v = 0 from rfl]
      exact zero_mem _
    have h3 : (ν (AdelicBox.integralFiniteAdeles (𝓞 F) F)).toReal ≠ 0 := ENNReal.toReal_ne_zero.2
      ⟨((AdelicBox.isOpen_integralFiniteAdeles F).measure_pos ν ⟨0, h0O⟩).ne',
        (AdelicBox.isCompact_integralFiniteAdeles F).measure_lt_top.ne⟩
    rw [hcdef]
    exact div_ne_zero (Complex.ofReal_ne_zero.2 h1)
      (mul_ne_zero (Complex.ofReal_ne_zero.2 h2) (Complex.ofReal_ne_zero.2 h3))
  have hI0 : I ≠ 0 := by
    rw [hIdef, map_zero, fourierIntegral_testSchwartz_zero]
    exact integral_testFn_ne_zero F
  have hcI : c * I ≠ 0 := mul_ne_zero hc0 hI0

  have hX : ∀ y : 𝔸f,
      fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f)) ν h y
        = (c * I)⁻¹ * fourierIntegral ψ μ𝔸 (fun x : 𝔸 => testSchwartz F (e∞ x.1) * h x.2)
            ((0 : F∞), y) := by
    intro y
    have h91 : fourierIntegral ψ μ𝔸 (fun x : 𝔸 => testSchwartz F (e∞ x.1) * h x.2) ((0 : F∞), y)
        = c * I * fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f))
            ν h y :=
      fourierIntegral_pureTensor_eq F μ𝔸 ν hψ.continuous hψu (testSchwartz F) hlc hcs ((0 : F∞), y)
    rw [h91, inv_mul_cancel_left₀ hcI]
  refine ⟨⟨‖(c * I)⁻¹‖ * B, fun y => ?_⟩, ?_⟩
  · rw [hX y, norm_mul]
    exact mul_le_mul_of_nonneg_left (hB y) (norm_nonneg _)
  · rw [show fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f)) ν h
        = fun y => (c * I)⁻¹ * fourierIntegral ψ μ𝔸 (fun x : 𝔸 => testSchwartz F (e∞ x.1) * h x.2)
            ((0 : F∞), y) from funext hX]
    exact hcsF.mul_left (f := fun _ => (c * I)⁻¹)

variable {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f)

private theorem sliceFin_eq (κ γ : AdelicGL2 (𝓞 F) F) :
    sliceFin hf κ γ = fun y => finFactor hf
      ((glFin (𝓞 F) F κ)⁻¹ * glFin (𝓞 F) F γ * unipotentGL2 y * glFin (𝓞 F) F κ) := by
  funext y
  simp only [sliceFin, mul_assoc]

private theorem finite_image_sliceFin {Θ : Set (AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F)} (hΘ : IsCompact Θ) :
    ((fun θ : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => sliceFin hf θ.1 θ.2) '' Θ).Finite := by
  haveI : CompactSpace Θ := isCompact_iff_compactSpace.mp hΘ
  have hΛ := (isFinTestFactor_finFactor hf).1.isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport
    (isFinTestFactor_finFactor hf).2 (unipotentGL2 (R := 𝔸f))
  have hκ : Continuous fun θ : Θ =>
      ((glFin (𝓞 F) F (θ : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F).1)⁻¹
          * glFin (𝓞 F) F (θ : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F).2,
        glFin (𝓞 F) F (θ : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F).1) :=
    (((continuous_glFin (𝓞 F) F).comp (continuous_fst.comp continuous_subtype_val)).inv.mul
        ((continuous_glFin (𝓞 F) F).comp (continuous_snd.comp continuous_subtype_val))).prodMk
      ((continuous_glFin (𝓞 F) F).comp (continuous_fst.comp continuous_subtype_val))
  refine ((hΛ.comp_continuous hκ).range_finite).subset ?_
  rintro _ ⟨θ, hθ, rfl⟩
  refine ⟨⟨θ, hθ⟩, ?_⟩
  show _ = sliceFin hf θ.1 θ.2
  rw [sliceFin_eq]
  rfl

private theorem finSupportOn [MeasurableSpace 𝔸f] [BorelSpace 𝔸f] (ν : Measure 𝔸f) [ν.IsAddHaarMeasure]
    {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ)
    {Θ : Set (AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F)} (hΘ : IsCompact Θ) :
    FinSupportOn F ψ ν Θ (sliceFin hf) := by
  set S : Set (𝔸f → ℂ) :=
    (fun θ : AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => sliceFin hf θ.1 θ.2) '' Θ with hSdef
  have hSfin : S.Finite := finite_image_sliceFin hf hΘ
  have hmemS : ∀ θ ∈ Θ, sliceFin hf θ.1 θ.2 ∈ S := by
    intro θ hθ
    rw [hSdef]
    exact ⟨θ, hθ, rfl⟩
  have hS : ∀ h ∈ S, IsLocallyConstant h ∧ HasCompactSupport h := by
    intro h hh
    rw [hSdef] at hh
    obtain ⟨θ, -, rfl⟩ := hh
    exact ⟨isLocallyConstant_sliceFin hf θ.1 θ.2, hasCompactSupport_sliceFin hf θ.1 θ.2⟩
  let β : (𝔸f → ℂ) → ℝ := fun h =>
    if hh : IsLocallyConstant h ∧ HasCompactSupport h then
      Classical.choose (bounded_and_hasCompactSupport_finTransform ν hψ hh.1 hh.2).1 else 0
  have hβ : ∀ h : 𝔸f → ℂ, ∀ hh : IsLocallyConstant h ∧ HasCompactSupport h, ∀ y : 𝔸f,
      ‖fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f)) ν h y‖
        ≤ β h := by
    intro h hh y
    have : β h = Classical.choose (bounded_and_hasCompactSupport_finTransform ν hψ hh.1 hh.2).1 :=
      dif_pos hh
    rw [this]
    exact Classical.choose_spec (bounded_and_hasCompactSupport_finTransform ν hψ hh.1 hh.2).1 y
  refine ⟨⋃ h ∈ S, tsupport
      (fourierIntegral (ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) 𝔸f)) ν h),
    hSfin.isCompact_biUnion fun h hh =>
      (bounded_and_hasCompactSupport_finTransform ν hψ (hS h hh).1 (hS h hh).2).2,
    ∑ h ∈ hSfin.toFinset, max (β h) 0, fun θ hθ y => ⟨?_, fun hne => ?_⟩⟩
  · refine (hβ _ ⟨isLocallyConstant_sliceFin hf θ.1 θ.2, hasCompactSupport_sliceFin hf θ.1 θ.2⟩ y).trans ?_
    exact (le_max_left _ _).trans
      (Finset.single_le_sum (fun h _ => le_max_right _ _) (hSfin.mem_toFinset.2 (hmemS θ hθ)))
  · exact Set.mem_biUnion (hmemS θ hθ) (subset_tsupport _ hne)

end FinSupport

section Assembly

open MeasureTheory Set NumberField NumberField.InfinitePlace IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel
open NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicFourier
open scoped SchwartzMap Classical
attribute [local instance] NumberField.AdelicHaar.adeleBorel
  NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)
local notation "μ𝔸" => NumberField.AdelicHaar.adelicAddHaar (𝓞 F) F
local notation "G" => AdelicGL2 (𝓞 F) F
local notation "E∞" => mixedEmbedding.mixedSpace F

private theorem unipotentGL2_mul_diagGL2 {R : Type*} [CommRing R] (t₁ t₂ : Rˣ) (s : R) :
    unipotentGL2 s * diagGL2 t₁ t₂ = diagGL2 t₁ t₂ * unipotentGL2 (((sliceScale t₁ t₂ : Rˣ) : R) * s) := by
  apply Units.ext
  have hT : (t₁ : R) * ((t₁⁻¹ : Rˣ) : R) = 1 := Units.mul_inv t₁
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, sliceScale, Units.val_mul]
  linear_combination (-(s * (t₂ : R))) * hT

private theorem diagGL2_inv_mul_unipotentGL2_mul_diagGL2 {R : Type*} [CommRing R] (t₁ t₂ : Rˣ) (s : R) :
    (diagGL2 t₁ t₂)⁻¹ * unipotentGL2 s * diagGL2 t₁ t₂
      = unipotentGL2 (((sliceScale t₁ t₂ : Rˣ) : R) * s) := by
  rw [mul_assoc, unipotentGL2_mul_diagGL2, inv_mul_cancel_left]

private theorem diagGL2_one_inv_mul_unipotentGL2_mul_diagGL2_one {R : Type*} [CommRing R] (σ : Rˣ) (s : R) :
    (diagGL2 1 σ)⁻¹ * unipotentGL2 s * diagGL2 1 σ = unipotentGL2 ((σ : R) * s) := by
  rw [diagGL2_inv_mul_unipotentGL2_mul_diagGL2]
  simp [sliceScale]

private theorem unipotentGL2_inv_mul_unipotentGL2_mul_unipotentGL2 {R : Type*} [CommRing R] (w s : R) :
    (unipotentGL2 w)⁻¹ * unipotentGL2 s * unipotentGL2 w = unipotentGL2 s := by
  rw [unipotentGL2_inv, ← unipotentGL2_add, ← unipotentGL2_add, neg_add_cancel_comm]

private theorem inv_mul_unipotentGL2_mul_mul (w : 𝔸) (t₁ t₂ : 𝔸ˣ) (k : G) (s : 𝔸) (z : G) :
    (unipotentGL2 w * diagGL2 t₁ t₂ * k)⁻¹ * unipotentGL2 s * (unipotentGL2 w * diagGL2 t₁ t₂ * k * z)
      = k⁻¹ * unipotentGL2 (((sliceScale t₁ t₂ : 𝔸ˣ) : 𝔸) * s) * k * z := by
  rw [show (unipotentGL2 w * diagGL2 t₁ t₂ * k)⁻¹ * unipotentGL2 s
          * (unipotentGL2 w * diagGL2 t₁ t₂ * k * z)
        = k⁻¹ * ((diagGL2 t₁ t₂)⁻¹ * ((unipotentGL2 w)⁻¹ * unipotentGL2 s * unipotentGL2 w)
            * diagGL2 t₁ t₂) * k * z by group,
    unipotentGL2_inv_mul_unipotentGL2_mul_unipotentGL2, diagGL2_inv_mul_unipotentGL2_mul_diagGL2]

private theorem stdAddChar_arch (a : E∞) :
    (StandardAddChar.stdAddChar F).compAddMonoidHom
        ((AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).comp
          (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toAddMonoidHom) a
      = ((Real.fourierChar (Algebra.trace ℝ E∞ a) : Circle) : ℂ) := by
  have h := StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace F
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a)
  rw [RingEquiv.apply_symm_apply] at h
  exact h

private theorem sliceDecayOn_of_isCompact {f : G → ℂ} (hf : IsFactorizableTestFn F f)
    {Θ : Set (G × G)} (hΘ : IsCompact Θ) :
    SliceDecayOn F (StandardAddChar.stdAddChar F) f Θ := by
  borelize (FiniteAdeleRing (𝓞 F) F)
  exact sliceDecayOn_of_tensor F Measure.addHaar (StandardAddChar.isGlobalAddChar_stdAddChar F) f
    (sliceTensorOn hf Θ) (archDecayOn hf hΘ (stdAddChar_arch F))
    (finSupportOn hf Measure.addHaar (StandardAddChar.isGlobalAddChar_stdAddChar F) hΘ)

private theorem norm_tsum_subtype_le (φ : F → ℂ) (n : F → ℝ) {H : ℝ} (hH0 : 0 < H) {r : F} (hr0 : r ≠ 0)
    (hφ : ∀ ξ : F, ‖φ ξ‖ = H * n (r * ξ)) {B₀ : ℝ} (hB₀ : 0 ≤ B₀) (Cl : ℝ) (M N : ℕ) (T : ℝ)
    (good : F → Prop)
    (hn : ∀ ζ : F, ζ ≠ 0 →
      n ζ ≤ B₀ * ∏ w : InfinitePlace F, ((1 + T * w ζ) ^ M)⁻¹ ∧ (n ζ ≠ 0 → good ζ))
    (hLS : ∀ V : Finset F, (∀ ζ ∈ V, ζ ≠ 0 ∧ good ζ) →
      ∑ ζ ∈ V, ∏ w : InfinitePlace F, ((1 + T * w ζ) ^ M)⁻¹ ≤ Cl * (H ^ (N + 1))⁻¹) :
    ‖∑' ξ : {ξ : F // ξ ≠ 0}, φ ξ‖ ≤ B₀ * Cl * H⁻¹ ^ N := by
  classical
  set b : {ξ : F // ξ ≠ 0} → ℝ := fun ξ => H * n (r * ξ) with hbdef
  have hb0 : ∀ ξ, 0 ≤ b ξ := fun ξ => by
    rw [hbdef]
    exact (norm_nonneg (φ ξ)).trans (hφ ξ).le
  have hpt : ∀ ξ : {ξ : F // ξ ≠ 0}, ‖φ ξ‖ ≤ b ξ := fun ξ => by
    rw [hbdef]
    exact (hφ ξ).le
  have hpartial : ∀ U : Finset {ξ : F // ξ ≠ 0}, ∑ ξ ∈ U, b ξ ≤ B₀ * Cl * H⁻¹ ^ N := by
    intro U
    set v : Finset F := U.image fun ξ : {ξ : F // ξ ≠ 0} => r * (ξ : F) with hvdef
    have h1 : ∑ ξ ∈ U, b ξ = H * ∑ ζ ∈ v, n ζ := by
      rw [hvdef, Finset.sum_image fun a _ a' _ h => Subtype.ext (mul_left_cancel₀ hr0 h),
        Finset.mul_sum]
    have hv0 : ∀ ζ ∈ v, ζ ≠ 0 := by
      intro ζ hζ
      obtain ⟨ξ, -, rfl⟩ := Finset.mem_image.1 hζ
      exact mul_ne_zero hr0 ξ.2
    have h2 : ∑ ζ ∈ v, n ζ = ∑ ζ ∈ v.filter good, n ζ :=
      (Finset.sum_filter_of_ne fun ζ hζ hne => (hn ζ (hv0 ζ hζ)).2 hne).symm
    have h3 : ∑ ζ ∈ v.filter good, n ζ
        ≤ B₀ * ∑ ζ ∈ v.filter good, ∏ w : InfinitePlace F, ((1 + T * w ζ) ^ M)⁻¹ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun ζ hζ => (hn ζ (hv0 ζ (Finset.mem_filter.1 hζ).1)).1
    have h4 : ∑ ζ ∈ v.filter good, ∏ w : InfinitePlace F, ((1 + T * w ζ) ^ M)⁻¹
        ≤ Cl * (H ^ (N + 1))⁻¹ :=
      hLS (v.filter good) fun ζ hζ =>
        ⟨hv0 ζ (Finset.mem_filter.1 hζ).1, (Finset.mem_filter.1 hζ).2⟩
    have hkey : H * (H ^ (N + 1))⁻¹ = H⁻¹ ^ N := by
      rw [inv_pow, pow_succ, mul_inv, mul_comm (H ^ N)⁻¹, ← mul_assoc, mul_inv_cancel₀ hH0.ne',
        one_mul]
    calc ∑ ξ ∈ U, b ξ = H * ∑ ζ ∈ v, n ζ := h1
      _ ≤ H * (B₀ * (Cl * (H ^ (N + 1))⁻¹)) := by
          rw [h2]
          exact mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left h4 hB₀)) hH0.le
      _ = B₀ * Cl * H⁻¹ ^ N := by rw [← hkey]; ring
  have hbsum : Summable b := summable_of_sum_le hb0 hpartial
  exact (tsum_of_norm_bounded hbsum.hasSum hpt).trans (Real.tsum_le_of_sum_le hb0 hpartial)

private theorem conj_regroup {Γ : Type*} [Group Γ] (k d m z : Γ) :
    k⁻¹ * (d⁻¹ * m * d) * k * z = k⁻¹ * d⁻¹ * m * (d * k * z) := by
  group

private theorem translate_regroup {Γ : Type*} [Group Γ] (k a b z : Γ) :
    (k * (k⁻¹ * b * k * z))⁻¹ * (k * (k⁻¹ * b * k * z) * k⁻¹) * (a * (k * (k⁻¹ * b * k * z)))
      = k⁻¹ * (a * b) * k * z := by
  group

private theorem scale_slice_mem_pureTensorSet {f : G → ℂ} (hf : IsFactorizableTestFn F f) (k z : G)
    (σ : 𝔸ˣ) :
    (fun t : 𝔸 => f (k⁻¹ * unipotentGL2 ((σ : 𝔸) * t) * k * z)) ∈ pureTensorSet F := by
  have h : (fun t : 𝔸 => f (k⁻¹ * unipotentGL2 ((σ : 𝔸) * t) * k * z))
      = fun t : 𝔸 => f (k⁻¹ * (diagGL2 1 σ)⁻¹ * unipotentGL2 t * (diagGL2 1 σ * k * z)) :=
    funext fun t => congrArg f
      ((congrArg (fun m : G => k⁻¹ * m * k * z)
          (diagGL2_one_inv_mul_unipotentGL2_mul_diagGL2_one σ t).symm).trans
        (conj_regroup k (diagGL2 1 σ) (unipotentGL2 t) z))
  rw [h]
  exact AutomorphicForm.IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet F hf _ _

private theorem scale_slice_eq_slice (f : G → ℂ) (k z : G) (σ : 𝔸ˣ) (u₀ : 𝔸) :
    (fun t : 𝔸 => f (k⁻¹ * unipotentGL2 ((σ : 𝔸) * t) * k * z))
      = fun t : 𝔸 => slice F f (k * (k⁻¹ * unipotentGL2 u₀ * k * z))
          (k * (k⁻¹ * unipotentGL2 u₀ * k * z) * k⁻¹) ((σ : 𝔸) * t + -u₀) := by
  funext t
  simp only [slice]
  rw [translate_regroup, ← unipotentGL2_add ((σ : 𝔸) * t + -u₀) u₀, neg_add_cancel_right]

private theorem inv_distribHaarChar_scale (σ α : 𝔸ˣ) (q : Fˣ)
    (hσ : σ = α⁻¹ * Units.map (algebraMap F 𝔸 : F →* 𝔸) q) (hαf : (α : 𝔸).2 = 1) {T : ℝ}
    (hαa : ∀ v : InfinitePlace F, ‖(α : 𝔸).1 v‖ = T) :
    ((distribHaarChar 𝔸 σ : ℝ))⁻¹ = T ^ Module.finrank ℚ F := by
  have hq1 : distribHaarChar 𝔸 (Units.map (algebraMap F 𝔸 : F →* 𝔸) q) = 1 :=
    NumberField.AdeleRing.distribHaarChar_algebraMap F q
  have htn : ∏ v : InfinitePlace F, T ^ v.mult = T ^ Module.finrank ℚ F := by
    rw [Finset.prod_pow_eq_pow_sum, sum_mult_eq]
  rw [hσ, map_mul, map_inv, hq1, mul_one, NNReal.coe_inv, inv_inv,
    NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one F α hαf, ← htn]
  exact Finset.prod_congr rfl fun v _ => by rw [hαa v]

private theorem inv_scale_mul_algebraMap (σ α : 𝔸ˣ) (q : Fˣ)
    (hσ : σ = α⁻¹ * Units.map (algebraMap F 𝔸 : F →* 𝔸) q) (ξ : F) :
    ((σ⁻¹ : 𝔸ˣ) : 𝔸) * ι ξ = (α : 𝔸) * ι (((q⁻¹ : Fˣ) : F) * ξ) := by
  rw [hσ, mul_inv_rev, inv_inv, ← map_inv (Units.map (algebraMap F 𝔸 : F →* 𝔸)) q]
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, map_mul]
  ring

private theorem exists_bound_tsum_sub_average_conj
    (f : G → ℂ) (hf : IsFactorizableTestFn F f) {K₀ : Set G} (hK₀ : IsCompact K₀) (N : ℕ) :
    ∃ C : ℝ, ∀ k ∈ K₀, ∀ (z : G) (σ α : 𝔸ˣ) (q : Fˣ) (T : ℝ),
      σ = α⁻¹ * Units.map (algebraMap F 𝔸 : F →* 𝔸) q → (α : 𝔸).2 = 1 →
      (∀ v : InfinitePlace F, ‖(α : 𝔸).1 v‖ = T) → 1 ≤ T →
        ‖(∑' β : F, f (k⁻¹ * unipotentGL2 ((σ : 𝔸) * ι β) * k * z))
            - (((μ𝔸) (adelicBox F)).toReal : ℂ)⁻¹ *
                ∫ t, f (k⁻¹ * unipotentGL2 ((σ : 𝔸) * t) * k * z) ∂μ𝔸‖
          ≤ C * (T ^ Module.finrank ℚ F)⁻¹ ^ N := by
  classical
  have hsupp : HasCompactSupport f :=
    (AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf).2
  set Θ : Set (G × G) := (fun p : G × G => (p.1 * p.2, p.1 * p.2 * p.1⁻¹)) '' (K₀ ×ˢ tsupport f)
    with hΘdef
  have hΘ : IsCompact Θ :=
    (hK₀.prod hsupp.isCompact).image ((continuous_fst.mul continuous_snd).prodMk
      ((continuous_fst.mul continuous_snd).mul continuous_fst.inv))
  obtain ⟨s, hs, hdec⟩ := sliceDecayOn_of_isCompact F hf hΘ
  set ψ : AddChar 𝔸 ℂ := StandardAddChar.stdAddChar F with hψdef
  have hψ : IsGlobalAddChar F ψ := StandardAddChar.isGlobalAddChar_stdAddChar F
  have hψu : ∀ a : 𝔸, ‖ψ a‖ = 1 := norm_apply_eq_one_of_isGlobalAddChar F hψ
  obtain ⟨M, Cl, hCl0, hLS⟩ := exists_sum_prod_inv_one_add_mul_pow_le F hs (N + 1)
  obtain ⟨B, hB⟩ := hdec M
  set B₀ : ℝ := max B 0 with hB₀def
  have hB₀ : 0 ≤ B₀ := le_max_right _ _
  have hBB₀ : B ≤ B₀ := le_max_left _ _
  refine ⟨‖(((μ𝔸) (adelicBox F)).toReal : ℂ)⁻¹‖ * (B₀ * Cl),
    fun k hk z σ α q T hσ hαf hαa hT1 => ?_⟩
  have hT0 : 0 < T := one_pos.trans_le hT1
  set H : ℝ := T ^ Module.finrank ℚ F with hHdef
  have hH1 : 1 ≤ H := one_le_pow₀ hT1
  have hH0 : 0 < H := one_pos.trans_le hH1
  have htn : ∏ v : InfinitePlace F, T ^ v.mult = H := by
    rw [Finset.prod_pow_eq_pow_sum, sum_mult_eq]
  have hRHS0 : 0 ≤ B₀ * Cl * H⁻¹ ^ N :=
    mul_nonneg (mul_nonneg hB₀ hCl0) (pow_nonneg (inv_nonneg.2 hH0.le) N)
  set Φ : 𝔸 → ℂ := fun t => f (k⁻¹ * unipotentGL2 ((σ : 𝔸) * t) * k * z) with hΦdef
  have hΦSB : Φ ∈ schwartzBruhat F :=
    mem_schwartzBruhat_of_mem_pureTensorSet (scale_slice_mem_pureTensorSet F hf k z σ)
  show ‖(∑' β : F, Φ (ι β)) - (((μ𝔸) (adelicBox F)).toReal : ℂ)⁻¹ * ∫ t, Φ t ∂μ𝔸‖
    ≤ ‖(((μ𝔸) (adelicBox F)).toReal : ℂ)⁻¹‖ * (B₀ * Cl) * H⁻¹ ^ N
  rw [tsum_sub_inv_measure_mul_integral_eq_inv_measure_mul_tsum_fourierIntegral_ne_zero F μ𝔸 hψ hΦSB,
    norm_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  by_cases h0 : ∀ v : 𝔸, f (k⁻¹ * unipotentGL2 v * k * z) = 0
  · have hΦ0 : Φ = 0 := funext fun t => h0 _
    rw [hΦ0]
    simp only [fourierIntegral, Pi.zero_apply, mul_zero, integral_zero, tsum_zero, norm_zero]
    exact hRHS0
  obtain ⟨u₀, hu₀⟩ := not_forall.1 h0
  set z' : G := k⁻¹ * unipotentGL2 u₀ * k * z with hz'def
  have hz' : z' ∈ tsupport f := subset_tsupport _ hu₀
  have hθ : (k * z', k * z' * k⁻¹) ∈ Θ := by
    rw [hΘdef]
    exact ⟨(k, z'), Set.mk_mem_prod hk hz', rfl⟩
  have hΦeq : Φ = fun t => slice F f (k * z') (k * z' * k⁻¹) ((σ : 𝔸) * t + -u₀) :=
    scale_slice_eq_slice F f k z σ u₀
  have hδ : ((distribHaarChar 𝔸 σ : ℝ))⁻¹ = H := inv_distribHaarChar_scale F σ α q hσ hαf hαa
  have hr0 : ((q⁻¹ : Fˣ) : F) ≠ 0 := (q⁻¹).ne_zero
  refine norm_tsum_subtype_le F (fun ξ => fourierIntegral ψ μ𝔸 Φ (ι ξ))
    (fun ζ => ‖fourierIntegral ψ μ𝔸 (slice F f (k * z') (k * z' * k⁻¹)) ((α : 𝔸) * ι ζ)‖)
    hH0 hr0 ?_ hB₀ Cl M N T (fun ζ => ∃ a : 𝓞 F, (a : F) = (s : F) * ζ) ?_ ?_
  · intro ξ
    show ‖fourierIntegral ψ μ𝔸 Φ (ι ξ)‖
      = H * ‖fourierIntegral ψ μ𝔸 (slice F f (k * z') (k * z' * k⁻¹))
          ((α : 𝔸) * ι (((q⁻¹ : Fˣ) : F) * ξ))‖
    rw [← inv_scale_mul_algebraMap F σ α q hσ ξ, ← hδ, hΦeq]
    exact norm_fourierIntegral_affine F μ𝔸 ψ hψu (slice F f (k * z') (k * z' * k⁻¹)) σ (-u₀) (ι ξ)
  · intro ζ hζ
    obtain ⟨h1, h2⟩ := hB _ hθ α T hT1 hαf hαa ζ hζ
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right hBB₀ (Finset.prod_nonneg fun w _ => by positivity)),
      fun hne => h2 (norm_ne_zero_iff.1 hne)⟩
  · intro V hV
    have h := hLS (fun _ => T) (fun _ => hT0) (by rw [htn]; exact hH1) V hV
    rwa [htn] at h

end Assembly

end UnipotentKernelDecay
p2m_reactivate "P2MW.S_AutomorphicForm_norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn.UnipotentKernelDecay"

theorem solution
    (K : Type) [Field K] [NumberField K]
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : IsFactorizableTestFn K f) (c u : ℝ) (N : ℕ) :
    ∃ C : ℝ, ∀ x ∈ integralWindowedSiegelSet K c u,
      1 ≤ archHeight K (glArch (𝓞 K) K x) →
      ∀ (y : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        ‖(∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
          - (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
            ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K)‖
          ≤ C * (archHeight K (glArch (𝓞 K) K x))⁻¹ ^ N := by
  obtain ⟨K₀, hK₀, hstr⟩ :=
    UnipotentKernelDecay.exists_eq_unipotent_mul_diag_mul_mem_of_one_le_archHeight K c u
  obtain ⟨C, hC⟩ := UnipotentKernelDecay.exists_bound_tsum_sub_average_conj K f hf hK₀ N
  refine ⟨C, fun x hx hH y => ?_⟩
  obtain ⟨w, t₁, t₂, k, α, q, T, hk, hxe, hσ, hαf, hαa, hT1, hTH⟩ := hstr x hx hH
  have hconj : ∀ s : AdeleRing (𝓞 K) K, x⁻¹ * unipotentGL2 s * y
      = k⁻¹ * unipotentGL2
            (((UnipotentKernelDecay.sliceScale t₁ t₂ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * s)
          * k * (x⁻¹ * y) := by
    intro s
    have h := UnipotentKernelDecay.inv_mul_unipotentGL2_mul_mul K w t₁ t₂ k s (x⁻¹ * y)
    rwa [← hxe, mul_inv_cancel_left] at h
  simp_rw [hconj]
  rw [← hTH]
  exact hC k hk (x⁻¹ * y) (UnipotentKernelDecay.sliceScale t₁ t₂) α q T hσ hαf hαa hT1

end
p2m_reactivate "P2MW.S_AutomorphicForm_norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn.UnipotentKernelDecay"

end S_AutomorphicForm_norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn
end P2MW
export P2MW.S_AutomorphicForm_norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn (solution)
