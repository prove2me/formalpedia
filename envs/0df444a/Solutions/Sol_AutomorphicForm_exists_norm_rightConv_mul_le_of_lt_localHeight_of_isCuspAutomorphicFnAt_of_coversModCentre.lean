-- Prove2me | solution 1 for AutomorphicForm.exists_norm_rightConv_mul_le_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6fc4ef53-cdc7-50ad-8e3c-fdd1670f62dc

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply
import Theorems.Thm_AutomorphicForm_norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn
import Theorems.Thm_AutomorphicForm_norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_norm_rightConv_mul_le_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering MeasureTheory

open scoped ProbabilityTheory ENNReal NNReal

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace HighCuspEnds

private theorem globalPoints_unipotentGL2 (K : Type) [Field K] [NumberField K] (k : K) :
    globalPoints (𝓞 K) K (unipotentGL2 k) = unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change algebraMap K (AdeleRing (𝓞 K) K) ((unipotentGL2 k : Matrix (Fin 2) (Fin 2) K) i j)
    = (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) k) : Matrix (Fin 2) (Fin 2) _) i j
  rw [unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem h0_bound (K : Type) [Field K] [NumberField K]
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c') (T₀ : ℝ) :
    ∃ Ccap : ℝ, ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      (∃ w : InfinitePlace K, Ccap < localHeight (archComponent K w (glArch (𝓞 K) K s))) →
        T₀ < archHeight K (glArch (𝓞 K) K s) := by
  set m : ℝ := min 1 c' with hm
  have hm0 : 0 < m := lt_min one_pos hc'
  have hm1 : m ≤ 1 := min_le_left _ _
  set P : ℝ := ∏ v : InfinitePlace K, m ^ v.mult with hP
  have hP0 : 0 < P := Finset.prod_pos fun v _ => pow_pos hm0 _
  refine ⟨max 1 ((|T₀| + 1) / P), fun s hs hw => ?_⟩
  obtain ⟨w, hw⟩ := hw
  have hs' := mem_centreCutSiegelSet_iff.mp hs
  have hlow : ∀ v : InfinitePlace K, m ≤ localHeight (archComponent K v (glArch (𝓞 K) K s)) :=
    fun v => (min_le_right _ _).trans (hs'.2.1 v)
  have hlw1 : 1 ≤ localHeight (archComponent K w (glArch (𝓞 K) K s)) := (le_max_left _ _).trans hw.le

  have hprod : localHeight (archComponent K w (glArch (𝓞 K) K s)) * P
      ≤ archHeight K (glArch (𝓞 K) K s) := by
    classical
    have hEq : localHeight (archComponent K w (glArch (𝓞 K) K s)) * P
        = ∏ v : InfinitePlace K, (m ^ v.mult *
            if v = w then localHeight (archComponent K w (glArch (𝓞 K) K s)) else 1) := by
      rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ w, if_pos (Finset.mem_univ w), mul_comm]
    rw [hEq]
    show _ ≤ ∏ v : InfinitePlace K, localHeight (archComponent K v (glArch (𝓞 K) K s)) ^ v.mult
    refine Finset.prod_le_prod (fun v _ => ?_) (fun v _ => ?_)
    · refine mul_nonneg (pow_nonneg hm0.le _) ?_
      split_ifs
      · exact zero_le_one.trans hlw1
      · exact zero_le_one
    · split_ifs with hv
      · subst hv
        calc m ^ v.mult * localHeight (archComponent K v (glArch (𝓞 K) K s))
            ≤ 1 ^ v.mult * localHeight (archComponent K v (glArch (𝓞 K) K s)) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hm0.le hm1 _) (zero_le_one.trans hlw1)
          _ = localHeight (archComponent K v (glArch (𝓞 K) K s)) ^ 1 := by rw [one_pow, one_mul, pow_one]
          _ ≤ localHeight (archComponent K v (glArch (𝓞 K) K s)) ^ v.mult :=
              pow_le_pow_right₀ hlw1 NumberField.InfinitePlace.mult_pos
      · rw [mul_one]
        exact pow_le_pow_left₀ hm0.le (hlow v) _
  have hT : |T₀| + 1 ≤ localHeight (archComponent K w (glArch (𝓞 K) K s)) * P := by
    have h1 : (|T₀| + 1) / P ≤ localHeight (archComponent K w (glArch (𝓞 K) K s)) :=
      (le_max_right _ _).trans hw.le
    rwa [div_le_iff₀ hP0] at h1
  calc T₀ ≤ |T₀| := le_abs_self _
    _ < |T₀| + 1 := lt_add_one _
    _ ≤ _ := hT.trans hprod

private theorem r1_loc_unipotentGL2_apply {L : Type*} [NormedField L] (t : L) :
    ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 0 = 1 ∧
    ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 0 1 = t ∧
    ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
    ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) 1 1 = 1 :=
  ⟨by rw [unipotentGL2_coe]; rfl, by rw [unipotentGL2_coe]; rfl,
    by rw [unipotentGL2_coe]; rfl, by rw [unipotentGL2_coe]; rfl⟩

private theorem r1_loc_conj_sub_one_apply {L : Type*} [NormedField L] (g : GL (Fin 2) L) (t : L)
    (i j : Fin 2) :
    ((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
        - (1 : Matrix (Fin 2) (Fin 2) L) i j
      = t * ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i 0
          * (g : Matrix (Fin 2) (Fin 2) L) 1 j := by
  obtain ⟨hN00, hN01, hN10, hN11⟩ := r1_loc_unipotentGL2_apply (L := L) t
  have hval : ((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
          * ((unipotentGL2 t : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
          * (g : Matrix (Fin 2) (Fin 2) L) := by
    rw [Units.val_mul, Units.val_mul]
  have hone : (1 : Matrix (Fin 2) (Fin 2) L)
      = ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) * (g : Matrix (Fin 2) (Fin 2) L) :=
    (Units.inv_mul g).symm
  rw [hval, hone]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hN00, hN01, hN10, hN11]
  ring

private theorem r1_loc_norm_inv_apply_zero {L : Type*} [NormedField L] (g : GL (Fin 2) L)
    (i : Fin 2) :
    ‖((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i 0‖
      = ‖(g : Matrix (Fin 2) (Fin 2) L).det‖⁻¹ * ‖(g : Matrix (Fin 2) (Fin 2) L).adjugate i 0‖ := by
  have hcoe : ((g⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)
      = ((g : Matrix (Fin 2) (Fin 2) L))⁻¹ := Matrix.coe_units_inv g
  rw [hcoe, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, norm_smul, norm_inv]

private theorem r1_loc_real_bound {T D x y R : ℝ} (hT : 0 ≤ T) (hD : 0 < D) (hxy : x * y ≤ R) :
    T * (D⁻¹ * x) * y ≤ T / (D / R) := by
  rw [div_div_eq_mul_div, le_div_iff₀ hD]
  calc T * (D⁻¹ * x) * y * D = T * (x * y) * (D⁻¹ * D) := by ring
    _ = T * (x * y) := by rw [inv_mul_cancel₀ hD.ne', mul_one]
    _ ≤ T * R := mul_le_mul_of_nonneg_left hxy hT

private theorem r1_norm_conj_unipotentGL2_sub_one_apply_le {L : Type*} [NormedField L]
    (g : GL (Fin 2) L) (t : L) (i j : Fin 2) :
    ‖((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
        - (1 : Matrix (Fin 2) (Fin 2) L) i j‖ ≤ ‖t‖ / localHeight g := by
  have hdet0 : (g : Matrix (Fin 2) (Fin 2) L).det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero g
  have hdetpos : 0 < ‖(g : Matrix (Fin 2) (Fin 2) L).det‖ := by
    rw [norm_pos_iff]
    exact hdet0
  have hA := sq_nonneg (‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ - ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖)
  have hB := sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖
  have hC := sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖
  rw [r1_loc_conj_sub_one_apply g t i j, norm_mul, norm_mul, r1_loc_norm_inv_apply_zero g i]
  refine r1_loc_real_bound (norm_nonneg t) hdetpos ?_
  rw [Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j
  · show ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ * ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
    nlinarith [hA, hB, hC]
  · show ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ * ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
    nlinarith [hA, hB, hC]
  · show ‖-(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ * ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
    rw [norm_neg]
    nlinarith [hA, hB, hC]
  · show ‖-(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ * ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖
      ≤ ‖(g : Matrix (Fin 2) (Fin 2) L) 1 0‖ ^ 2 + ‖(g : Matrix (Fin 2) (Fin 2) L) 1 1‖ ^ 2
    rw [norm_neg]
    nlinarith [hA, hB, hC]

private theorem r1_norm_conj_unipotentGL2_apply_le {L : Type*} [NormedField L]
    (g : GL (Fin 2) L) (t : L) {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (hcg : c ≤ localHeight g) (ht : ‖t‖ ≤ r) (i j : Fin 2) :
    ‖((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j‖ ≤ 1 + r / c := by
  have hsub := r1_norm_conj_unipotentGL2_sub_one_apply_le g t i j
  have hone : ‖(1 : Matrix (Fin 2) (Fin 2) L) i j‖ ≤ 1 := by
    rw [Matrix.one_apply]
    split_ifs
    · exact norm_one.le
    · exact norm_zero.trans_le zero_le_one
  have hdiv : ‖t‖ / localHeight g ≤ r / c := div_le_div₀ hr ht hc hcg
  calc ‖((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j‖
      = ‖(((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
          - (1 : Matrix (Fin 2) (Fin 2) L) i j) + (1 : Matrix (Fin 2) (Fin 2) L) i j‖ := by
        rw [sub_add_cancel]
    _ ≤ ‖((g⁻¹ * unipotentGL2 t * g : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L) i j
          - (1 : Matrix (Fin 2) (Fin 2) L) i j‖ + ‖(1 : Matrix (Fin 2) (Fin 2) L) i j‖ :=
        norm_add_le _ _
    _ ≤ r / c + 1 := add_le_add (hsub.trans hdiv) hone
    _ = 1 + r / c := add_comm _ _

private theorem r1_unipotentGL2_inv {R : Type*} [CommRing R] (x : R) :
    (unipotentGL2 x)⁻¹ = unipotentGL2 (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

section Adelic

variable (K : Type) [Field K] [NumberField K]

private theorem r1_archComponent_glArch_unipotentGL2 (w : InfinitePlace K) (b : AdeleRing (𝓞 K) K) :
    archComponent K w (glArch (𝓞 K) K (unipotentGL2 b)) = unipotentGL2 (b.1 w) := by
  ext i j
  rw [archComponent_apply, glArch_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> rfl

private theorem r1_arch_entry_norm_le {c' u' d₁' d₂' rB : ℝ} (hc' : 0 < c') (hrB : 0 ≤ rB)
    {s : GL (Fin 2) (AdeleRing (𝓞 K) K)} (hs : s ∈ centreCutSiegelSet K c' u' d₁' d₂')
    {b : AdeleRing (𝓞 K) K} (hb : ∀ w : InfinitePlace K, ‖b.1 w‖ ≤ rB)
    (w : InfinitePlace K) (i j : Fin 2) :
    ‖(((s⁻¹ * unipotentGL2 b * s : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 w‖ ≤ 1 + rB / c' := by
  have hlh : c' ≤ localHeight (archComponent K w (glArch (𝓞 K) K s)) :=
    (mem_centreCutSiegelSet_iff.mp hs).2.1 w
  have hconj : archComponent K w (glArch (𝓞 K) K (s⁻¹ * unipotentGL2 b * s))
      = (archComponent K w (glArch (𝓞 K) K s))⁻¹ * unipotentGL2 (b.1 w)
          * archComponent K w (glArch (𝓞 K) K s) := by
    simp only [map_mul, map_inv, r1_archComponent_glArch_unipotentGL2]
  have hentry : (((s⁻¹ * unipotentGL2 b * s : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 w
      = (archComponent K w (glArch (𝓞 K) K (s⁻¹ * unipotentGL2 b * s)) :
          Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl
  rw [hentry, hconj]
  exact r1_norm_conj_unipotentGL2_apply_le _ _ hc' hrB hlh (hb w) i j

private theorem r1_glFin_unipotentGL2_mem {b : AdeleRing (𝓞 K) K}
    (hb : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    glFin (𝓞 K) K (unipotentGL2 b) ∈ finiteIntegralGL2 (𝓞 K) K := by
  have hneg : (-b).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    rw [show (-b).2 = -b.2 from rfl, neg_eq_zero_sub]
    exact AdelicLevel.sub_mem_integralFiniteAdeles AdelicLevel.zero_mem_integralFiniteAdeles hb
  rw [mem_finiteIntegralGL2_iff, ← map_inv, r1_unipotentGL2_inv]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [glFin_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · exact AdelicLevel.one_mem_integralFiniteAdeles
    · exact hb
    · exact AdelicLevel.zero_mem_integralFiniteAdeles
    · exact AdelicLevel.one_mem_integralFiniteAdeles
  · rw [glFin_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j
    · exact AdelicLevel.one_mem_integralFiniteAdeles
    · exact hneg
    · exact AdelicLevel.zero_mem_integralFiniteAdeles
    · exact AdelicLevel.one_mem_integralFiniteAdeles

private theorem r1_fin_entry_mem {s : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (hs : glFin (𝓞 K) K s ∈ finiteIntegralGL2 (𝓞 K) K) {b : AdeleRing (𝓞 K) K}
    (hb : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) (i j : Fin 2) :
    (((s⁻¹ * unipotentGL2 b * s : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2
      ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  have hm : glFin (𝓞 K) K (s⁻¹ * unipotentGL2 b * s) ∈ finiteIntegralGL2 (𝓞 K) K := by
    rw [map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem (inv_mem hs) (r1_glFin_unipotentGL2_mem K hb)) hs
  have h := (mem_finiteIntegralGL2_iff.mp hm).1 i j
  rwa [glFin_apply] at h

private theorem r1_isCompact_closure_box : IsCompact (closure (adelicBox K)) := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset K
  exact hC.closure_of_subset hsub

private theorem r1_exists_box_bound :
    ∃ rB : ℝ, 0 ≤ rB ∧ ∀ b ∈ closure (adelicBox K), ∀ w : InfinitePlace K, ‖b.1 w‖ ≤ rB := by
  have hcont : Continuous fun b : AdeleRing (𝓞 K) K => ∑ w : InfinitePlace K, ‖b.1 w‖ :=
    continuous_finsetSum _ fun w _ => ((continuous_archEval K w).comp continuous_fst).norm
  obtain ⟨r, hr⟩ := (r1_isCompact_closure_box K).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max r 0, le_max_right _ _, fun b hb w => ?_⟩
  refine le_trans (Finset.single_le_sum (f := fun v : InfinitePlace K => ‖b.1 v‖)
    (fun v _ => norm_nonneg _) (Finset.mem_univ w)) ?_
  exact ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans (hr b hb))).trans (le_max_left _ _)

private theorem r1_snd_mem_of_mem_closure_box {b : AdeleRing (𝓞 K) K}
    (hb : b ∈ closure (adelicBox K)) : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
  have hcl : IsClosed {y : AdeleRing (𝓞 K) K | y.2 ∈ AdelicBox.integralFiniteAdeles (𝓞 K) K} :=
    (AdelicBox.isClosed_integralFiniteAdeles K).preimage continuous_snd
  exact closure_minimal (fun y hy => hy.2) hcl hb

private def r1_adeleBall (r : ℝ) : Set (AdeleRing (𝓞 K) K) :=
  {y | (∀ w : InfinitePlace K, ‖y.1 w‖ ≤ r) ∧ y.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K}

private theorem r1_mem_adeleBall {r : ℝ} {y : AdeleRing (𝓞 K) K} :
    y ∈ r1_adeleBall K r ↔
      (∀ w : InfinitePlace K, ‖y.1 w‖ ≤ r) ∧ y.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K :=
  Iff.rfl

private theorem r1_isCompact_adeleBall (r : ℝ) : IsCompact (r1_adeleBall K r) := by
  haveI : ∀ v : InfinitePlace K, ProperSpace v.Completion := fun v =>
    NumberField.AdelicBox.properSpace_completion K v
  have hS : IsCompact {x : InfiniteAdeleRing K | ∀ v, ‖x v‖ ≤ r} := by
    have : {x : InfiniteAdeleRing K | ∀ v, ‖x v‖ ≤ r} =
        Set.pi Set.univ fun v : InfinitePlace K => Metric.closedBall (0 : v.Completion) r := by
      ext x
      exact ⟨fun h v _ => mem_closedBall_zero_iff.mpr (h v),
        fun h v => mem_closedBall_zero_iff.mp (h v (Set.mem_univ v))⟩
    rw [this]
    exact isCompact_univ_pi fun v => isCompact_closedBall (0 : v.Completion) r
  have : IsCompact ({x : InfiniteAdeleRing K | ∀ v, ‖x v‖ ≤ r} ×ˢ
      AdelicLevel.integralFiniteAdeles (𝓞 K) K) :=
    hS.prod (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 K) K)
  exact this

private def r1_matBall (r : ℝ) : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) :=
  Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => r1_adeleBall K r

private def r1_Omega (r : ℝ) : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
  Units.embedProduct (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) ⁻¹'
    (r1_matBall K r ×ˢ (MulOpposite.op '' r1_matBall K r))

private theorem r1_isCompact_Omega (r : ℝ) : IsCompact (r1_Omega K r) := by
  have hM : IsCompact (r1_matBall K r) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => r1_isCompact_adeleBall K r
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hM.prod (hM.image MulOpposite.continuous_op))

private theorem r1_mem_Omega {r : ℝ} {m : GL (Fin 2) (AdeleRing (𝓞 K) K)}
    (h₁ : ∀ i j, (m : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j ∈ r1_adeleBall K r)
    (h₂ : ∀ i j, ((m⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j ∈ r1_adeleBall K r) :
    m ∈ r1_Omega K r := by
  rw [r1_Omega, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod]
  exact ⟨Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => h₁ i j,
    ⟨((m⁻¹ : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)),
      Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => h₂ i j, rfl⟩⟩

private theorem r1_conj_mem_Omega {c' u' d₁' d₂' rB : ℝ} (hc' : 0 < c') (hrB : 0 ≤ rB)
    {s : GL (Fin 2) (AdeleRing (𝓞 K) K)} (hs : s ∈ centreCutSiegelSet K c' u' d₁' d₂')
    {b : AdeleRing (𝓞 K) K} (hb₁ : ∀ w : InfinitePlace K, ‖b.1 w‖ ≤ rB)
    (hb₂ : b.2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K) :
    s⁻¹ * unipotentGL2 b * s ∈ r1_Omega K (1 + rB / c') := by
  have hs₁ : glFin (𝓞 K) K s ∈ finiteIntegralGL2 (𝓞 K) K := (mem_centreCutSiegelSet_iff.mp hs).1
  have hnb₁ : ∀ w : InfinitePlace K, ‖(-b).1 w‖ ≤ rB := fun w => by
    rw [show (-b).1 w = -(b.1 w) from rfl, norm_neg]
    exact hb₁ w
  have hnb₂ : (-b).2 ∈ AdelicLevel.integralFiniteAdeles (𝓞 K) K := by
    rw [show (-b).2 = -b.2 from rfl, neg_eq_zero_sub]
    exact AdelicLevel.sub_mem_integralFiniteAdeles AdelicLevel.zero_mem_integralFiniteAdeles hb₂
  have hinv : (s⁻¹ * unipotentGL2 b * s)⁻¹ = s⁻¹ * unipotentGL2 (-b) * s := by
    simp only [mul_inv_rev, inv_inv, r1_unipotentGL2_inv, mul_assoc]
  refine r1_mem_Omega K (fun i j => (r1_mem_adeleBall K).mpr ⟨fun w => ?_, ?_⟩)
    (fun i j => (r1_mem_adeleBall K).mpr ?_)
  · exact r1_arch_entry_norm_le K hc' hrB hs hb₁ w i j
  · exact r1_fin_entry_mem K hs₁ hb₂ i j
  · rw [hinv]
    exact ⟨fun w => r1_arch_entry_norm_le K hc' hrB hs hnb₁ w i j, r1_fin_entry_mem K hs₁ hnb₂ i j⟩

private theorem r1_exists_absorbing {c' u' d₁' d₂' : ℝ} (hc' : 0 < c')
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C) :
    ∃ E : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)), IsCompact E ∧
      ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
        Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
            unipotentGL2 t * s * c) (closure (adelicBox K)) C
          ⊆ (fun y => s * y) '' E := by
  obtain ⟨rB, hrB, hbox⟩ := r1_exists_box_bound K
  refine ⟨Set.image2 (fun m c => m * c) (r1_Omega K (1 + rB / c')) C, ?_, fun s hs x hx => ?_⟩
  · rw [← Set.image_prod]
    exact ((r1_isCompact_Omega K _).prod hC).image (continuous_fst.mul continuous_snd)
  · obtain ⟨b, hb, c, hc, rfl⟩ := Set.mem_image2.mp hx
    refine ⟨s⁻¹ * unipotentGL2 b * s * c, Set.mem_image2_of_mem
      (r1_conj_mem_Omega K hc' hrB hs (hbox b hb) (r1_snd_mem_of_mem_closure_box K hb)) hc, ?_⟩
    show s * (s⁻¹ * unipotentGL2 b * s * c) = unipotentGL2 b * s * c
    simp only [← mul_assoc, mul_inv_cancel, one_mul]

end Adelic

private theorem r1_bound (K : Type) [Field K] [NumberField K]
    (c' u' d₁' d₂' : ℝ) (hc' : 0 < c')
    {C : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hC : IsCompact C) :
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      adelicGLHaar (Fin 2) (𝓞 K) K
          (Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
            unipotentGL2 t * s * c) (closure (adelicBox K)) C)
        ≤ ENNReal.ofReal M₀ := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  obtain ⟨E, hE, hsub⟩ := r1_exists_absorbing K (u' := u') (d₁' := d₁') (d₂' := d₂') hc' hC
  have hEtop : adelicGLHaar (Fin 2) (𝓞 K) K E ≠ ⊤ := hE.measure_lt_top.ne
  refine ⟨(adelicGLHaar (Fin 2) (𝓞 K) K E).toReal, ENNReal.toReal_nonneg, fun s hs => ?_⟩
  rw [ENNReal.ofReal_toReal hEtop]
  calc adelicGLHaar (Fin 2) (𝓞 K) K
        (Set.image2 (fun (t : AdeleRing (𝓞 K) K) (c : GL (Fin 2) (AdeleRing (𝓞 K) K)) =>
          unipotentGL2 t * s * c) (closure (adelicBox K)) C)
      ≤ adelicGLHaar (Fin 2) (𝓞 K) K ((fun y => s * y) '' E) := measure_mono (hsub s hs)
    _ = adelicGLHaar (Fin 2) (𝓞 K) K E := by
        rw [Set.image_mul_left, measure_preimage_mul]

private theorem cs_bound (K : Type) [Field K] [NumberField K]
    (φ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (s : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (W R : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (CN M M₀ H : ℝ) (A : ℕ) (hM₀ : 0 ≤ M₀) (hH : 1 ≤ H)
    (hcont : Continuous φ) (hL2 : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict W))
    (hU : ‖∫ y, φ y * g (s⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖
      ≤ CN * H⁻¹ ^ A * ∫ y in R, ‖φ y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
    (hL1 : ∫⁻ y in R, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ ENNReal.ofReal (M * H ^ A) *
        ∫⁻ y in W, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K))
    (hμR : adelicGLHaar (Fin 2) (𝓞 K) K R ≤ ENNReal.ofReal M₀) :
    ‖∫ y, φ y * g (s⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖
      ≤ |CN| * Real.sqrt M₀ * Real.sqrt (|M| *
        (∫⁻ y in W, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)).toReal) := by

  set IW : ℝ≥0∞ := ∫⁻ y in W, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hIW
  set IR : ℝ≥0∞ := ∫⁻ y in R, (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) with hIR
  have hH0 : 0 < H := lt_of_lt_of_le one_pos hH
  have hHA : 0 ≤ H⁻¹ ^ A := pow_nonneg (inv_nonneg.mpr hH0.le) A

  have hIW_top : IW ≠ ⊤ := by
    have h2 := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (two_ne_zero)
      (ENNReal.ofNat_ne_top (n := 2)) hL2.eLpNorm_lt_top
    have hEq : IW = ∫⁻ y in W, ‖φ y‖ₑ ^ (2 : ℝ≥0∞).toReal ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
      rw [hIW, ENNReal.toReal_ofNat]
      refine lintegral_congr fun y => ?_
      rw [ENNReal.rpow_two, enorm_eq_nnnorm]
    rw [hEq]
    exact h2.ne

  have hIR_le : IR ≤ ENNReal.ofReal (|M| * H ^ A) * IW :=
    hL1.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_abs_self M) (pow_nonneg hH0.le A))) le_rfl)
  have hprod_top : ENNReal.ofReal (|M| * H ^ A) * IW ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIW_top
  have hIR_top : IR ≠ ⊤ := ne_top_of_le_ne_top hprod_top hIR_le
  have hIR_real : IR.toReal ≤ |M| * H ^ A * IW.toReal := by
    have h := ENNReal.toReal_mono hprod_top hIR_le
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h

  have hmeas : AEMeasurable (fun y => (‖φ y‖₊ : ℝ≥0∞)) ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict R) :=
    (hcont.enorm).measurable.aemeasurable
  have hCS : ∫⁻ y in R, (‖φ y‖₊ : ℝ≥0∞) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      ≤ (adelicGLHaar (Fin 2) (𝓞 K) K R) ^ (1 / (2 : ℝ)) * IR ^ (1 / (2 : ℝ)) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict R)
      Real.HolderConjugate.two_two (f := fun _ => (1 : ℝ≥0∞)) (g := fun y => (‖φ y‖₊ : ℝ≥0∞))
      aemeasurable_const hmeas
    simp only [Pi.mul_apply, one_mul, ENNReal.rpow_two, one_pow, lintegral_const,
      Measure.restrict_apply_univ] at h
    rw [hIR]
    exact h

  have hJ : ∫ y in R, ‖φ y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = (∫⁻ y in R, (‖φ y‖₊ : ℝ≥0∞) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => norm_nonneg _)
      hcont.norm.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun y => ?_
    rw [ofReal_norm, enorm_eq_nnnorm]
  have hμR_real : (adelicGLHaar (Fin 2) (𝓞 K) K R).toReal ≤ M₀ := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hμR
    rwa [ENNReal.toReal_ofReal hM₀] at h
  have hμR_top : adelicGLHaar (Fin 2) (𝓞 K) K R ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hμR
  have hJ_le : ∫ y in R, ‖φ y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) ≤ Real.sqrt M₀ * Real.sqrt IR.toReal := by
    rw [hJ]
    have hfin : (adelicGLHaar (Fin 2) (𝓞 K) K R) ^ (1 / (2 : ℝ)) * IR ^ (1 / (2 : ℝ)) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hμR_top)
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hIR_top)
    have h := ENNReal.toReal_mono hfin hCS
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow,
      ← Real.sqrt_eq_rpow] at h
    exact h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hμR_real) (Real.sqrt_nonneg _))

  have hx0 : 0 ≤ H⁻¹ ^ A * Real.sqrt (H ^ A) := mul_nonneg hHA (Real.sqrt_nonneg _)
  have hsq : (H⁻¹ ^ A * Real.sqrt (H ^ A)) ^ 2 = H⁻¹ ^ A := by
    rw [mul_pow, Real.sq_sqrt (pow_nonneg hH0.le A), ← pow_mul, mul_two, pow_add, mul_assoc,
      ← mul_pow, inv_mul_cancel₀ hH0.ne', one_pow, mul_one]
  have hsq1 : (H⁻¹ ^ A * Real.sqrt (H ^ A)) ^ 2 ≤ 1 := by
    rw [hsq]
    exact pow_le_one₀ (inv_nonneg.mpr hH0.le) (inv_le_one_of_one_le₀ hH)
  have hx1 : H⁻¹ ^ A * Real.sqrt (H ^ A) ≤ 1 := (pow_le_one_iff_of_nonneg hx0 two_ne_zero).mp hsq1

  have hJ0 : 0 ≤ ∫ y in R, ‖φ y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := integral_nonneg fun _ => norm_nonneg _
  have hpre : 0 ≤ |CN| * Real.sqrt M₀ * Real.sqrt (|M| * IW.toReal) :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  calc ‖∫ y, φ y * g (s⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖
      ≤ CN * H⁻¹ ^ A * ∫ y in R, ‖φ y‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := hU
    _ ≤ |CN| * H⁻¹ ^ A * (Real.sqrt M₀ * Real.sqrt IR.toReal) :=
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self CN) hHA) hJ0).trans
          (mul_le_mul_of_nonneg_left hJ_le (mul_nonneg (abs_nonneg _) hHA))
    _ ≤ |CN| * H⁻¹ ^ A * (Real.sqrt M₀ * Real.sqrt (|M| * H ^ A * IW.toReal)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hIR_real)
          (Real.sqrt_nonneg _)) (mul_nonneg (abs_nonneg _) hHA)
    _ = |CN| * Real.sqrt M₀ * Real.sqrt (|M| * IW.toReal) * (H⁻¹ ^ A * Real.sqrt (H ^ A)) := by
        rw [show |M| * H ^ A * IW.toReal = H ^ A * (|M| * IW.toReal) by ring,
          Real.sqrt_mul (pow_nonneg hH0.le A)]
        ring
    _ ≤ |CN| * Real.sqrt M₀ * Real.sqrt (|M| * IW.toReal) * 1 :=
        mul_le_mul_of_nonneg_left hx1 hpre
    _ = |CN| * Real.sqrt M₀ * Real.sqrt (|M| * IW.toReal) := mul_one _

private theorem a1_core
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) χ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hf : IsFactorizableTestFn K f)
    (c' u' d₁' d₂' : ℝ) (t : AdelicGL2 (𝓞 K) K) (hc' : 0 < c') (hd₁' : 0 < d₁') :
    ∃ Ccap C : ℝ, ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      (∃ w : InfinitePlace K, Ccap < localHeight (archComponent K w (glArch (𝓞 K) K s))) →
        ‖rightConv K φ f (s * t)‖ ≤ C := by
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

  have hft : IsFactorizableTestFn K (fun y => f (t⁻¹ * y)) :=
    isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn K f hf t
  obtain ⟨hft_cont, hft_supp⟩ :=
    continuous_and_hasCompactSupport_of_isFactorizableTestFn K (fun y => f (t⁻¹ * y)) hft

  have hls := ((lsXiMemberAt_iff (𝓞 K) K _ _ _ _ φ).mp hφ.1).1
  have hL2 := ((lsXiMemberAt_iff (𝓞 K) K _ _ _ _ φ).mp hφ.1).2
  have hφc : IsCuspidalFn ((adelicAddHaar (𝓞 K) K)[|adelicBox K]) unipotentGL2 φ := hφ.2

  let χ₀ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ := χ
  have hls₀ : IsLsXiFunction (𝓞 K) K ⊤ χ₀ φ := hls

  have hφN : ∀ (β : K) (y : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y) = φ y := by
    intro β y
    have h := hls.left_invariant (unipotentGL2 β) y
    rwa [globalPoints_unipotentGL2] at h

  have hφi : LocallyIntegrable φ (adelicGLHaar (Fin 2) (𝓞 K) K) := hcont.locallyIntegrable

  obtain ⟨T₁, A, M, hL1⟩ :=
    setLIntegral_nnnorm_sq_le_mul_archHeight_pow_mul_setLIntegral_of_isLsXiFunction_of_coversModCentre
      K c u d₁ d₂ T hd hcov χ₀ φ hls₀ hcont hft_supp.isCompact c' u' d₁' d₂' hc' hd₁'

  obtain ⟨CN, hP1⟩ :=
    norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn
      K (fun y => f (t⁻¹ * y)) hft 0 u' A

  obtain ⟨Ccap, hH0⟩ := h0_bound K c' u' d₁' d₂' hc' (max T₁ 1)
  obtain ⟨M₀, hM₀, hμR⟩ := r1_bound K c' u' d₁' d₂' hc' hft_supp.isCompact
  refine ⟨Ccap, |CN| * Real.sqrt M₀ * Real.sqrt (|M| *
      (∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
        (‖φ y‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K)).toReal), fun s hs hw => ?_⟩

  have hH : max T₁ 1 < archHeight K (glArch (𝓞 K) K s) := hH0 s hs hw
  have hT₁ : T₁ < archHeight K (glArch (𝓞 K) K s) := lt_of_le_of_lt (le_max_left _ _) hH
  have h1 : 1 ≤ archHeight K (glArch (𝓞 K) K s) := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hH)

  have hs' := mem_centreCutSiegelSet_iff.mp hs
  have hs_int : s ∈ integralWindowedSiegelSet K 0 u' := by
    simp only [integralWindowedSiegelSet, Set.mem_setOf_eq]
    exact ⟨hs'.1, le_of_lt (archHeight_pos K _), hs'.2.2.1⟩

  have hPy := hP1 s hs_int h1
  have hU := norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn K φ (fun y => f (t⁻¹ * y)) s
    hφN hφi hφc hft_cont hft_supp (CN * (archHeight K (glArch (𝓞 K) K s))⁻¹ ^ A) hPy

  rw [rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply K φ f s t]
  have hsub : rightConv K φ (fun y => f (t⁻¹ * y)) s
      = ∫ y, φ y * (fun y => f (t⁻¹ * y)) (s⁻¹ * y) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
    rw [rightConv_apply]
    have h := integral_mul_left_eq_self (μ := adelicGLHaar (Fin 2) (𝓞 K) K)
      (fun y => φ y * (fun y => f (t⁻¹ * y)) (s⁻¹ * y)) s
    simp only [inv_mul_cancel_left] at h
    exact h
  rw [hsub]

  exact cs_bound K φ (fun y => f (t⁻¹ * y)) s
    (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) _ CN M M₀ _ A hM₀ h1 hcont hL2
    hU (hL1 s hs hT₁) (hμR s hs)

end HighCuspEnds

end

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (χ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsCuspAutomorphicFnAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) χ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hf : IsFactorizableTestFn K f)
    (c' u' d₁' d₂' : ℝ) (t : AdelicGL2 (𝓞 K) K) (hc' : 0 < c') (hd₁' : 0 < d₁') :
    ∃ Ccap C : ℝ, ∀ s ∈ centreCutSiegelSet K c' u' d₁' d₂',
      (∃ w : InfinitePlace K, Ccap < localHeight (archComponent K w (glArch (𝓞 K) K s))) →
        ‖rightConv K φ f (s * t)‖ ≤ C :=
  HighCuspEnds.a1_core K c u d₁ d₂ T hd hcov χ φ hφ hcont f hf c' u' d₁' d₂' t hc' hd₁'

end S_AutomorphicForm_exists_norm_rightConv_mul_le_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre
end P2MW
export P2MW.S_AutomorphicForm_exists_norm_rightConv_mul_le_of_lt_localHeight_of_isCuspAutomorphicFnAt_of_coversModCentre (solution)
