-- Prove2me | solution 1 for AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a8cb65e4-ee90-5b5c-8225-a66522228c32

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup
import Theorems.Thm_AutomorphicForm_exists_pos_forall_prod_norm_sub_one_pow_mul_eq_and_weighted_eq_mul_prod_norm_pow_mul_integral_integral_of_scalar_mul_diagUnits2
import Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_integral_conj_diagUnits2_mul_unipotentGL2_eq_of_isCompact
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_mul_log_norm_one_sub_sq_add_norm_sq_eq_add_norm_mul_of_isReal
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_integral_mul_log_norm_one_sub_sq_add_norm_sq_eq_add_norm_sq_mul_log_mul_of_isComplex
import Theorems.Thm_AutomorphicForm_contDiff_and_hasCompactSupport_prod_norm_archEval_pow_rpow_mul_of_tsupport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply"
p2m_attr_erase "simp" "LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 8192

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped ENNReal
open LanglandsTunnell.CubicInduction (diagUnits2)

attribute [local instance] AutomorphicForm.centralizerBorel

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace DiscK

open AutomorphicForm Topology

variable (K : Type) [Field K] [NumberField K]

scoped instance secondCountable_completion (w : InfinitePlace K) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

scoped instance secondCountable_Koo : SecondCountableTopology (InfiniteAdeleRing K) :=
  inferInstanceAs (SecondCountableTopology ((w : InfinitePlace K) → w.Completion))

scoped instance secondCountable_units : SecondCountableTopology (InfiniteAdeleRing K)ˣ := by
  haveI : SecondCountableTopology (InfiniteAdeleRing K)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance locallyCompact_units : LocallyCompactSpace (InfiniteAdeleRing K)ˣ :=
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance secondCountable_GL : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

scoped instance locallyCompact_GL : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing K)) := by
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

scoped instance measurableSpace_GL : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.glBorelOf _
scoped instance borelSpace_GL : BorelSpace (GL (Fin 2) (InfiniteAdeleRing K)) := AutomorphicForm.borelSpace_glBorelOf _

abbrev Kc : Subgroup (GL (Fin 2) (InfiniteAdeleRing K)) :=
  ⨅ w : InfinitePlace K, (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent K w)

scoped instance (priority := high) measurableSpace_Kc : MeasurableSpace (Kc K) := borel _
scoped instance borelSpace_Kc : BorelSpace (Kc K) := ⟨rfl⟩
scoped instance secondCountable_Kc : SecondCountableTopology (Kc K) := TopologicalSpace.Subtype.secondCountableTopology _
scoped instance compactSpace_Kc : CompactSpace (Kc K) :=
  isCompact_iff_compactSpace.mp
    (NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup K).2

theorem diagUnits2_eq_scalar_mul (a t : (InfiniteAdeleRing K)ˣ) :
    diagUnits2 a (a * t) = Matrix.GeneralLinearGroup.scalar (Fin 2) (a * t) * diagUnits2 t⁻¹ 1 := by
  refine Units.ext ?_
  rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_conj_diagUnits2 (p q : (InfiniteAdeleRing K)ˣ) (y : InfiniteAdeleRing K) :
    AutomorphicForm.unipotentGL2 (-y) * diagUnits2 p q * AutomorphicForm.unipotentGL2 y =
      diagUnits2 p q * AutomorphicForm.unipotentGL2 (y - ((p⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * (q : InfiniteAdeleRing K) * y) := by
  refine Units.ext ?_
  simp only [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, AutomorphicForm.unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · rw [mul_sub, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
    ring

section PerPlace

variable {F : Type*} [NormedField F]

open AutomorphicForm.WindowedSiegel

theorem val_weyl_mul (x w' : GL (Fin 2) F) (hw : (w' : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) :
    ((w' * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![(x : Matrix (Fin 2) (Fin 2) F) 1 0, (x : Matrix (Fin 2) (Fin 2) F) 1 1;
         (x : Matrix (Fin 2) (Fin 2) F) 0 0, (x : Matrix (Fin 2) (Fin 2) F) 0 1] := by
  rw [Units.val_mul, hw]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem localHeight_mul_localHeight_weyl_mul (x w' : GL (Fin 2) F)
    (hw : (w' : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) :
    localHeight x * localHeight (w' * x) =
      (topNormSq (x : Matrix (Fin 2) (Fin 2) F) * rowNormSq (x : Matrix (Fin 2) (Fin 2) F) /
        ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ ^ 2)⁻¹ := by
  have hx := val_weyl_mul x w' hw
  have hdet : 0 < ‖(x : Matrix (Fin 2) (Fin 2) F).det‖ :=
    norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero x)
  have hrow : 0 < rowNormSq (x : Matrix (Fin 2) (Fin 2) F) := rowNormSq_pos x
  have htop : 0 < topNormSq (x : Matrix (Fin 2) (Fin 2) F) := by
    have h := rowNormSq_pos (w' * x)
    rw [hx] at h
    unfold rowNormSq at h
    unfold topNormSq
    simpa using h
  have hdet' : (((w' * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).det = -(x : Matrix (Fin 2) (Fin 2) F).det := by
    rw [hx, Matrix.det_fin_two_of, Matrix.det_fin_two]
    ring
  have hrow' : rowNormSq ((w' * x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = topNormSq (x : Matrix (Fin 2) (Fin 2) F) := by
    rw [hx]; unfold rowNormSq topNormSq; simp
  unfold localHeight
  rw [hdet', norm_neg, hrow']
  field_simp

theorem localHeight_mul_localHeight_weyl_mul_of_val (g w' : GL (Fin 2) F) (p q y : F) (hp : p ≠ 0) (hq : q ≠ 0)
    (hg : (g : Matrix (Fin 2) (Fin 2) F) = !![p, p * y; 0, q])
    (hw : (w' : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) :
    localHeight g * localHeight (w' * g) = (1 + ‖y‖ ^ 2)⁻¹ := by
  rw [localHeight_mul_localHeight_weyl_mul g w' hw, hg]
  unfold topNormSq rowNormSq
  have hp' : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
  have hq' : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  simp [Matrix.det_fin_two_of, norm_mul]
  field_simp

end PerPlace

abbrev wK : GL (Fin 2) (InfiniteAdeleRing K) := AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)

theorem val_wK : ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) : GL (Fin 2) (InfiniteAdeleRing K)) :
    Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) = !![0, 1; 1, 0] := by
  ext i j
  rw [AdelicLevel.glArch_apply]
  change (algebraMap K (AdeleRing (𝓞 K) K)
      (((AutomorphicForm.gl2Weyl : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j)).1 = _
  fin_cases i <;> fin_cases j <;> simp [AutomorphicForm.gl2Weyl] <;> rfl

theorem val_archComponent_wK (v : InfinitePlace K) :
    ((archComponent K v (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)) : GL (Fin 2) v.Completion) :
      Matrix (Fin 2) (Fin 2) v.Completion) = !![0, 1; 1, 0] := by
  ext i j
  rw [archComponent_apply, val_wK]
  fin_cases i <;> fin_cases j <;> simp <;> rfl

def archWeight (x : GL (Fin 2) (InfiniteAdeleRing K)) : ℝ :=
  -Real.log (AutomorphicForm.WindowedSiegel.archHeight K x)
    - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
        (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * x))

theorem weight_top_eq_archWeight :
    (fun x : GL (Fin 2) (InfiniteAdeleRing K) =>
            (∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) *
            Real.log
              (AutomorphicForm.WindowedSiegel.topNormSq
                  ((NumberField.AdelicLevel.archComponent K w x : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) *
                AutomorphicForm.WindowedSiegel.rowNormSq
                  ((NumberField.AdelicLevel.archComponent K w x : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion) /
                ‖((NumberField.AdelicLevel.archComponent K w x : GL (Fin 2) w.Completion) :
                    Matrix (Fin 2) (Fin 2) w.Completion).det‖ ^ 2))) =
    (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
            -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
              - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
                  (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y))) := by
  funext x
  unfold AutomorphicForm.WindowedSiegel.archHeight
  rw [Real.log_prod (fun v _ => (pow_pos (AutomorphicForm.WindowedSiegel.localHeight_pos _) _).ne'),
    Real.log_prod (fun v _ => (pow_pos (AutomorphicForm.WindowedSiegel.localHeight_pos _) _).ne'),
    neg_sub_left, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Real.log_pow, Real.log_pow, ← mul_add, ← mul_neg, map_mul,
    ← Real.log_mul (AutomorphicForm.WindowedSiegel.localHeight_pos _).ne'
      (AutomorphicForm.WindowedSiegel.localHeight_pos _).ne',
    ← Real.log_inv]
  congr 1
  conv_rhs => rw [mul_comm]
  rw [localHeight_mul_localHeight_weyl_mul _ _ (val_archComponent_wK K v), inv_inv]

theorem archWeight_mul_rowIsometry (x : GL (Fin 2) (InfiniteAdeleRing K)) {k : GL (Fin 2) (InfiniteAdeleRing K)}
    (hk : ∀ v : InfinitePlace K, AutomorphicForm.WindowedSiegel.IsRowIsometry (archComponent K v k)) :
    archWeight K (x * k) = archWeight K x := by
  unfold archWeight
  rw [← mul_assoc, AutomorphicForm.WindowedSiegel.archHeight_mul_rowIsometry K x hk,
    AutomorphicForm.WindowedSiegel.archHeight_mul_rowIsometry K _ hk]

theorem isRowIsometry_of_mem_iInf {k : GL (Fin 2) (InfiniteAdeleRing K)}
    (hk : k ∈ (⨅ w : InfinitePlace K,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (NumberField.AdelicLevel.archComponent K w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing K))))
    (v : InfinitePlace K) :
    AutomorphicForm.WindowedSiegel.IsRowIsometry (archComponent K v k) := by
  rw [Subgroup.mem_iInf] at hk
  exact Subgroup.mem_comap.mp (hk v)

theorem unit_apply_ne_zero (p : (InfiniteAdeleRing K)ˣ) (v : InfinitePlace K) : (p : InfiniteAdeleRing K) v ≠ 0 := by
  intro h
  have h1 : (p : InfiniteAdeleRing K) v * ((p⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v = 1 := by
    have h2 := congrArg (fun z : InfiniteAdeleRing K => z v) p.mul_inv
    exact h2
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem val_archComponent_diagUnits2_mul_unipotentGL2 (p q : (InfiniteAdeleRing K)ˣ) (y : InfiniteAdeleRing K)
    (v : InfinitePlace K) :
    ((archComponent K v (diagUnits2 p q * AutomorphicForm.unipotentGL2 y) : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion) =
      !![(p : InfiniteAdeleRing K) v, (p : InfiniteAdeleRing K) v * y v; 0, (q : InfiniteAdeleRing K) v] := by
  ext i j
  rw [archComponent_apply, Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, AutomorphicForm.unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> rfl

theorem archWeight_diagUnits2_mul_unipotentGL2 (p q : (InfiniteAdeleRing K)ˣ) (y : InfiniteAdeleRing K) :
    archWeight K (diagUnits2 p q * AutomorphicForm.unipotentGL2 y) =
      ∑ w : InfinitePlace K, (w.mult : ℝ) * Real.log (1 + ‖y w‖ ^ 2) := by
  unfold archWeight AutomorphicForm.WindowedSiegel.archHeight
  rw [Real.log_prod (fun v _ => (pow_pos (AutomorphicForm.WindowedSiegel.localHeight_pos _) _).ne'),
    Real.log_prod (fun v _ => (pow_pos (AutomorphicForm.WindowedSiegel.localHeight_pos _) _).ne'),
    neg_sub_left, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Real.log_pow, Real.log_pow, ← mul_add, ← mul_neg, map_mul,
    ← Real.log_mul (AutomorphicForm.WindowedSiegel.localHeight_pos _).ne'
      (AutomorphicForm.WindowedSiegel.localHeight_pos _).ne',
    ← Real.log_inv]
  congr 1
  rw [mul_comm, localHeight_mul_localHeight_weyl_mul_of_val _ _ _ _ _ (unit_apply_ne_zero K p v)
    (unit_apply_ne_zero K q v) (val_archComponent_diagUnits2_mul_unipotentGL2 K p q y v) (val_archComponent_wK K v),
    inv_inv]

theorem scalar_mul_diagUnits2 (u' s : (InfiniteAdeleRing K)ˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) u' * diagUnits2 s 1 = diagUnits2 (u' * s) u' := by
  refine Units.ext ?_
  rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.mul_apply, Fin.sum_univ_two]

theorem archWeight_scalar_diagUnits2_unipotent_mul (u' s : (InfiniteAdeleRing K)ˣ) (y : InfiniteAdeleRing K)
    (k : GL (Fin 2) (InfiniteAdeleRing K))
    (hk : k ∈ (⨅ w : InfinitePlace K,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (NumberField.AdelicLevel.archComponent K w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing K)))) :
    archWeight K (Matrix.GeneralLinearGroup.scalar (Fin 2) u' * diagUnits2 s 1 * AutomorphicForm.unipotentGL2 y * k) =
      ∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval K w y‖ ^ 2) := by
  rw [archWeight_mul_rowIsometry K _ (isRowIsometry_of_mem_iInf K hk), scalar_mul_diagUnits2,
    archWeight_diagUnits2_mul_unipotentGL2]
  rfl

theorem continuous_localHeight {F : Type*} [NormedField F] :
    Continuous (fun g : GL (Fin 2) F => AutomorphicForm.WindowedSiegel.localHeight g) := by
  unfold AutomorphicForm.WindowedSiegel.localHeight AutomorphicForm.WindowedSiegel.rowNormSq
  refine Continuous.div ?_ ?_ (fun g => (AutomorphicForm.WindowedSiegel.rowNormSq_pos g).ne')
  · exact (Units.continuous_val.matrix_det).norm
  · exact ((Units.continuous_val.matrix_elem 1 0).norm.pow 2).add ((Units.continuous_val.matrix_elem 1 1).norm.pow 2)

theorem continuous_archHeight : Continuous (AutomorphicForm.WindowedSiegel.archHeight K) := by
  unfold AutomorphicForm.WindowedSiegel.archHeight
  exact continuous_finsetProd _ fun v _ => (continuous_localHeight.comp (continuous_archComponent K v)).pow _

theorem continuous_archWeight : Continuous (archWeight K) := by
  unfold archWeight
  refine ((continuous_archHeight K).log fun x => (AutomorphicForm.WindowedSiegel.archHeight_pos K x).ne').neg.sub ?_
  exact ((continuous_archHeight K).comp (continuous_const.mul continuous_id)).log
    fun x => (AutomorphicForm.WindowedSiegel.archHeight_pos K _).ne'

def omega (y : InfiniteAdeleRing K) : ℝ :=
  ∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval K w y‖ ^ 2)

theorem continuous_omega : Continuous (omega K) := by
  unfold omega
  refine continuous_finsetSum _ fun w _ => continuous_const.mul ?_
  exact (continuous_const.add (((continuous_archEval K w).norm).pow 2)).log fun y =>
    ne_of_gt (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _))

theorem archWeight_iwasawa (u' t' : (InfiniteAdeleRing K)ˣ) (y : InfiniteAdeleRing K)
    (k : GL (Fin 2) (InfiniteAdeleRing K)) (hk : k ∈ Kc K) :
    archWeight K (Matrix.GeneralLinearGroup.scalar (Fin 2) u' * diagUnits2 t' 1 * AutomorphicForm.unipotentGL2 y * k) =
      omega K y :=
  archWeight_scalar_diagUnits2_unipotent_mul K u' t' y k hk

theorem isUnit_one_sub_of_isRegularSemisimple (a t : (InfiniteAdeleRing K)ˣ)
    (h : AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t))) :
    IsUnit ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) := by
  unfold AutomorphicForm.IsRegularSemisimple at h
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.trace_fin_two_of, Matrix.det_fin_two_of] at h
  have e : ((a : InfiniteAdeleRing K) + ((a * t : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) ^ 2 -
      4 * ((a : InfiniteAdeleRing K) * ((a * t : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) - 0 * 0) =
      ((a : InfiniteAdeleRing K) * ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))) ^ 2 := by
    push_cast; ring
  rw [e, isUnit_pow_iff two_ne_zero] at h
  exact isUnit_of_mul_isUnit_right h

theorem inv_apply_ne_one_of_isRegularSemisimple (a t : (InfiniteAdeleRing K)ˣ)
    (h : AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t))) (w : InfinitePlace K) :
    ((t⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w ≠ 1 := by
  intro h1
  have hu := isUnit_one_sub_of_isRegularSemisimple K a t h
  have hw := ((@Pi.isUnit_iff (InfinitePlace K) (fun w => w.Completion) _ _).mp hu) w
  have hmul : ((t⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w * (t : InfiniteAdeleRing K) w = 1 :=
    congrArg (fun x : InfiniteAdeleRing K => x w) t.inv_mul
  rw [h1, one_mul] at hmul
  have : ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) w = 0 := by
    show (1 : InfiniteAdeleRing K) w - (t : InfiniteAdeleRing K) w = 0
    rw [hmul]; exact sub_self _
  rw [this] at hw
  exact not_isUnit_zero hw

scoped instance isHaarMeasure_archHaarK : (AutomorphicForm.archHaarK K).IsHaarMeasure := by
  unfold AutomorphicForm.archHaarK
  infer_instance

open scoped Classical in
theorem measure_side
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    (τ₀ : Measure (InfiniteAdeleRing K × InfiniteAdeleRing K))
    (lam : Measure (InfiniteAdeleRing K)) [lam.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∃ Ψ : (Fin 3 → NumberField.mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ HasCompactSupport Ψ ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport Ψ, ∃ q ∈ Ca,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ), AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t)) →
      ∀ (v : (InfiniteAdeleRing K)ˣ), (v : InfiniteAdeleRing K) = 1 - (t : InfiniteAdeleRing K) →
      ∀ (τ : Measure (Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
        τ.IsHaarMeasure →
        Measure.map
            (fun x : Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
              ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
                ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
                InfiniteAdeleRing K × InfiniteAdeleRing K))
            τ = τ₀ →
      ∀ J I : ℂ,
        AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K) (archWeight K)
          (diagUnits2 a (a * t)) τ fa J →
        AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K)
          (diagUnits2 a (a * t)) τ fa I →
        (((∏ w : InfinitePlace K, ‖((t⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w - 1‖ ^ w.mult : ℝ) : ℂ) * I =
          (c : ℂ) * ((∏ w : InfinitePlace K, ‖((t⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) *
            ∫ x, Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
                     NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
                     NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] ∂lam) ∧
        (((∏ w : InfinitePlace K, ‖((t⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w - 1‖ ^ w.mult : ℝ) : ℂ) * J =
          (c : ℂ) * ((∏ w : InfinitePlace K, ‖((t⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) *
            ∫ x, Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K),
                     NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K),
                     NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] *
              ((omega K (((v⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * x) : ℝ) : ℂ) ∂lam) := by
  classical
  obtain ⟨ρ, hρ, hpin⟩ :=
    AutomorphicForm.exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq K τ₀
  haveI := hρ
  let κ : Measure (Kc K) := Measure.haar
  have hκ : κ.IsHaarMeasure := by infer_instance
  obtain ⟨c, hc, hW⟩ :=
    AutomorphicForm.exists_pos_forall_prod_norm_sub_one_pow_mul_eq_and_weighted_eq_mul_prod_norm_pow_mul_integral_integral_of_scalar_mul_diagUnits2
      K (AutomorphicForm.archHaarK K) (isHaarMeasure_archHaarK K) lam ρ κ hκ
  obtain ⟨Ψ, hΨs, hΨc, hΨu, hΨ⟩ :=
    AutomorphicForm.exists_contDiff_hasCompactSupport_forall_integral_conj_diagUnits2_mul_unipotentGL2_eq_of_isCompact K fa hfa κ hκ
  refine ⟨c, hc, Ψ, hΨs, hΨc, hΨu, ?_⟩
  intro a t hreg v hv τ hτ hmap J I hJ hI
  have hsch := hpin a (a * t) hreg τ hτ hmap
  have hu := inv_apply_ne_one_of_isRegularSemisimple K a t hreg
  have hv' : (v : InfiniteAdeleRing K) = 1 - (((t⁻¹)⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) := by
    rw [inv_inv]; exact hv
  have e := diagUnits2_eq_scalar_mul K a t
  clear hmap
  revert τ hτ hsch hJ hI
  rw [e]
  intro τ hτ hJ hI hsch
  obtain ⟨hI', hJ'⟩ := hW fa hfa (omega K) (continuous_omega K) (archWeight K) (continuous_archWeight K)
    (fun u' t' y k hk => archWeight_iwasawa K u' t' y k hk) t⁻¹ (a * t) hu v hv' τ hsch
  have eI := hI' I hI
  have eJ := hJ' J hJ
  simp_rw [← e] at eI eJ
  simp_rw [hΨ] at eI eJ
  exact ⟨eI, eJ⟩

theorem inv_apply_eq (t : (InfiniteAdeleRing K)ˣ) (w : InfinitePlace K) :
    ((t⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w = ((t : InfiniteAdeleRing K) w)⁻¹ :=
  eq_inv_of_mul_eq_one_left (congrArg (fun x : InfiniteAdeleRing K => x w) t.inv_mul)

theorem norm_inv_apply (t : (InfiniteAdeleRing K)ˣ) (w : InfinitePlace K) :
    ‖((t⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w‖ = ‖(t : InfiniteAdeleRing K) w‖⁻¹ := by
  rw [inv_apply_eq, norm_inv]

theorem norm_inv_apply_sub_one (t : (InfiniteAdeleRing K)ˣ) (w : InfinitePlace K) :
    ‖((t⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w - 1‖ =
      ‖(t : InfiniteAdeleRing K) w‖⁻¹ *
        ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ := by
  have ht : (t : InfiniteAdeleRing K) w ≠ 0 := unit_apply_ne_zero K t w
  rw [inv_apply_eq, ← norm_inv, ← norm_mul]
  congr 1
  show ((t : InfiniteAdeleRing K) w)⁻¹ - 1 = ((t : InfiniteAdeleRing K) w)⁻¹ * ((1 : InfiniteAdeleRing K) w - (t : InfiniteAdeleRing K) w)
  have h1 : (1 : InfiniteAdeleRing K) w = 1 := rfl
  rw [h1, mul_sub, mul_one, inv_mul_cancel₀ ht]

theorem omega_inv_mul (v : (InfiniteAdeleRing K)ˣ) (x : InfiniteAdeleRing K) :
    omega K (((v⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * x) =
      (∑ w : InfinitePlace K, (w.mult : ℝ) *
          Real.log (‖NumberField.AdelicLevel.archEval K w (v : InfiniteAdeleRing K)‖ ^ 2 +
            ‖NumberField.AdelicLevel.archEval K w x‖ ^ 2)) -
        ∑ w : InfinitePlace K, (w.mult : ℝ) * (2 * Real.log ‖NumberField.AdelicLevel.archEval K w (v : InfiniteAdeleRing K)‖) := by
  unfold omega
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← mul_sub]
  congr 1
  have hv0 : ‖NumberField.AdelicLevel.archEval K w (v : InfiniteAdeleRing K)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (unit_apply_ne_zero K v w)
  have hvpos : 0 < ‖NumberField.AdelicLevel.archEval K w (v : InfiniteAdeleRing K)‖ :=
    norm_pos_iff.mpr (unit_apply_ne_zero K v w)
  have e : NumberField.AdelicLevel.archEval K w (((v⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * x) =
      (NumberField.AdelicLevel.archEval K w (v : InfiniteAdeleRing K))⁻¹ * NumberField.AdelicLevel.archEval K w x := by
    rw [map_mul]
    congr 1
    exact inv_apply_eq K v w
  rw [e, norm_mul, norm_inv]
  have e2 : (1 : ℝ) + (‖NumberField.AdelicLevel.archEval K w (v : InfiniteAdeleRing K)‖⁻¹ *
        ‖NumberField.AdelicLevel.archEval K w x‖) ^ 2 =
      (‖NumberField.AdelicLevel.archEval K w (v : InfiniteAdeleRing K)‖ ^ 2 + ‖NumberField.AdelicLevel.archEval K w x‖ ^ 2) /
        ‖NumberField.AdelicLevel.archEval K w (v : InfiniteAdeleRing K)‖ ^ 2 := by
    field_simp
  rw [e2, Real.log_div (add_pos_of_pos_of_nonneg (pow_pos hvpos 2) (sq_nonneg _)).ne' (pow_pos hvpos 2).ne',
    Real.log_pow]
  push_cast
  ring

theorem prodP_eq (t : (InfiniteAdeleRing K)ˣ) :
    (∏ w : InfinitePlace K, ‖((t⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w - 1‖ ^ w.mult) =
      (∏ w : InfinitePlace K, ‖((t⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w‖ ^ w.mult) *
        ∏ w : InfinitePlace K,
          ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ w.mult := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← mul_pow, norm_inv_apply_sub_one, norm_inv_apply]

theorem prodQ_eq (t : (InfiniteAdeleRing K)ˣ) :
    (∏ w : InfinitePlace K, ‖((t⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w‖ ^ w.mult) =
      (∏ w : InfinitePlace K, ‖(t : InfiniteAdeleRing K) w‖ ^ w.mult)⁻¹ := by
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [norm_inv_apply, inv_pow]

theorem nu_eq (t : (InfiniteAdeleRing K)ˣ) :
    (∏ w : NumberField.InfinitePlace K,
        (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ /
            Real.sqrt ‖NumberField.AdelicLevel.archEval K w (t : InfiniteAdeleRing K)‖) ^ w.mult) =
      (∏ w : InfinitePlace K,
          ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ w.mult) *
        (∏ w : InfinitePlace K, ‖(t : InfiniteAdeleRing K) w‖ ^ w.mult) ^ (-(1 / 2 : ℝ)) := by
  have hS : ∀ w : InfinitePlace K,
      Real.sqrt ‖NumberField.AdelicLevel.archEval K w (t : InfiniteAdeleRing K)‖ ^ w.mult =
        (‖(t : InfiniteAdeleRing K) w‖ ^ w.mult) ^ (1 / 2 : ℝ) := by
    intro w
    rw [NumberField.AdelicLevel.archEval_apply, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (norm_nonneg _), mul_comm, Real.rpow_mul (norm_nonneg _), Real.rpow_natCast]
  simp_rw [div_pow, hS]
  rw [Finset.prod_div_distrib,
    Real.finset_prod_rpow _ _ (fun w _ => pow_nonneg (norm_nonneg _) _),
    Real.rpow_neg (Finset.prod_nonneg fun w _ => pow_nonneg (norm_nonneg _) _), div_eq_mul_inv]

theorem hasCompactSupport_finset_sum {X : Type*} [TopologicalSpace X] {ι' : Type*} (s : Finset ι')
    (f : ι' → X → ℂ) (hf : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact HasCompactSupport.zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self i s)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem notMem_tsupport_finset_sum {X : Type*} [TopologicalSpace X] {ι' : Type*} (s : Finset ι')
    (f : ι' → X → ℂ) (p : X) (hp : ∀ i ∈ s, p ∉ tsupport (f i)) :
    p ∉ tsupport (fun x => ∑ i ∈ s, f i x) := by
  rw [notMem_tsupport_iff_eventuallyEq]
  have h : ∀ i ∈ s, f i =ᶠ[nhds p] 0 := fun i hi => notMem_tsupport_iff_eventuallyEq.mp (hp i hi)
  have := (Filter.eventually_all_finset s).mpr h
  filter_upwards [this] with x hx
  simp only [Pi.zero_apply]
  exact Finset.sum_eq_zero fun i hi => by have := hx i hi; simpa using this

theorem isUnit_of_eq_vec (p : Fin 2 → NumberField.mixedEmbedding.mixedSpace K)
    (q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)
    (h : p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
              NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) :
    IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧
      IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1)) := by
  subst h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, RingEquiv.symm_apply_apply]
  exact ⟨Units.isUnit _, Units.isUnit _⟩

open scoped Classical in

def kink (w : InfinitePlace K) (t : (InfiniteAdeleRing K)ˣ) : ℝ :=
  if w.IsReal then ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖
  else ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
    Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖

def Rfac (p : Fin 2 → NumberField.mixedEmbedding.mixedSpace K) : ℂ :=
  ((((∏ w : NumberField.InfinitePlace K,
      ‖NumberField.AdelicLevel.archEval K w ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ ^ w.mult) ^
        (-(1 / 2 : ℝ)) : ℝ) : ℂ))

theorem Rfac_vec (t a : (InfiniteAdeleRing K)ˣ) :
    Rfac K ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] =
      (((∏ w : InfinitePlace K, ‖(t : InfiniteAdeleRing K) w‖ ^ w.mult) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
  unfold Rfac
  simp only [Matrix.cons_val_zero, RingEquiv.symm_apply_apply]
  rfl

open scoped Classical in

theorem per_place
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (lam : Measure (InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (Ψ : (Fin 3 → NumberField.mixedEmbedding.mixedSpace K) → ℂ) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hΨc : HasCompactSupport Ψ)
    (hΨu : ∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport Ψ, ∃ q ∈ Ca,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K))
    (w : NumberField.InfinitePlace K) :
    ∃ A B : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧ HasCompactSupport A ∧ HasCompactSupport B ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport A ∪ tsupport B, ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ),
        Integrable (fun x : InfiniteAdeleRing K =>
          Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x]) lam ∧
        Integrable (fun x : InfiniteAdeleRing K =>
          Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] *
            ((Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
                ‖NumberField.AdelicLevel.archEval K w x‖ ^ 2) : ℝ) : ℂ)) lam ∧
        ∫ x, Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] *
            ((Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
                ‖NumberField.AdelicLevel.archEval K w x‖ ^ 2) : ℝ) : ℂ) ∂lam =
          A ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] + ((kink K w t : ℝ) : ℂ) * B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by
  by_cases hw : w.IsReal
  · obtain ⟨A, B, h1, h2, h3, h4, h5, h6⟩ :=
      AutomorphicForm.exists_contDiff_hasCompactSupport_integral_mul_log_norm_one_sub_sq_add_norm_sq_eq_add_norm_mul_of_isReal
        K lam Ψ hΨ hΨc hΨu w hw
    refine ⟨A, B, h1, h2, h3, h4, h5, fun a t => ⟨(h6 a t).1, (h6 a t).2.1, ?_⟩⟩
    rw [(h6 a t).2.2]
    unfold kink
    rw [if_pos hw]
  · have hw' : w.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw
    obtain ⟨A, B, h1, h2, h3, h4, h5, h6⟩ :=
      AutomorphicForm.exists_contDiff_hasCompactSupport_integral_mul_log_norm_one_sub_sq_add_norm_sq_eq_add_norm_sq_mul_log_mul_of_isComplex
        K lam Ψ hΨ hΨc hΨu w hw'
    refine ⟨A, B, h1, h2, h3, h4, h5, fun a t => ⟨(h6 a t).1, (h6 a t).2.1, ?_⟩⟩
    rw [(h6 a t).2.2]
    unfold kink
    rw [if_neg hw]

end DiscK
p2m_reactivate "P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex.DiscK"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex.DiscK"

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

attribute [local instance] AutomorphicForm.centralizerBorel

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : AutomorphicForm.IsArchTestFactor K fa)
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (τ₀ : Measure (InfiniteAdeleRing K × InfiniteAdeleRing K)) :
    ∃ (B : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ)
      (C E : NumberField.InfinitePlace K → (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) B ∧ (∀ w, ContDiff ℝ (⊤ : ℕ∞) (C w)) ∧ (∀ w, ContDiff ℝ (⊤ : ℕ∞) (E w)) ∧
      HasCompactSupport B ∧ (∀ w, HasCompactSupport (C w)) ∧ (∀ w, HasCompactSupport (E w)) ∧
      (∀ p : Fin 2 → NumberField.mixedEmbedding.mixedSpace K, (B p ≠ 0 ∨ ∃ w, C w p ≠ 0 ∨ E w p ≠ 0) →
        IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)) ∧ IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1))) ∧

      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport B ∪ ⋃ w, (tsupport (C w) ∪ tsupport (E w)), ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ), AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t)) →
      ∀ (τ : Measure (Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
        τ.IsHaarMeasure →
        Measure.map
            (fun x : Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
              ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
                ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
                InfiniteAdeleRing K × InfiniteAdeleRing K))
            τ = τ₀ →
      ∀ J I : ℂ, AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K)
          (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
            -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
              - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
                  (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y)))
          (diagUnits2 a (a * t)) τ fa J →
        AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K)
          (diagUnits2 a (a * t)) τ fa I →
        ((∏ w : NumberField.InfinitePlace K,
              (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ /
                  Real.sqrt ‖NumberField.AdelicLevel.archEval K w (t : InfiniteAdeleRing K)‖) ^ w.mult : ℝ) : ℂ) * J =
          -2 * ((∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) *
              Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
            (((∏ w : NumberField.InfinitePlace K,
              (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ /
                  Real.sqrt ‖NumberField.AdelicLevel.archEval K w (t : InfiniteAdeleRing K)‖) ^ w.mult : ℝ) : ℂ) * I) +
          B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) :
                ℂ) * C w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex),
              ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
                  Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ :
                  ℝ) : ℂ) *
                E w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by
  classical
  letI mU : MeasurableSpace (InfiniteAdeleRing K)ˣ := borel _
  haveI bU : BorelSpace (InfiniteAdeleRing K)ˣ := ⟨rfl⟩
  obtain ⟨c, hc, Ψ, hΨs, hΨc, hΨu, hms⟩ :=
    DiscK.measure_side K fa hfa τ₀ (Measure.addHaar : Measure (InfiniteAdeleRing K))
  have hpl := fun w => DiscK.per_place K (Measure.addHaar : Measure (InfiniteAdeleRing K)) Ψ hΨs hΨc hΨu w
  choose A B hA hB hAc hBc hCaAB hmain using hpl
  have hCaA : ∀ w, ∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
      ∀ p ∈ tsupport (A w), ∃ q ∈ Ca,
        p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
              NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)] := fun w => by
    obtain ⟨Ca, h1, h2⟩ := hCaAB w
    exact ⟨Ca, h1, fun p hp => h2 p (Set.mem_union_left _ hp)⟩
  have hCaB : ∀ w, ∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
      ∀ p ∈ tsupport (B w), ∃ q ∈ Ca,
        p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
              NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)] := fun w => by
    obtain ⟨Ca, h1, h2⟩ := hCaAB w
    exact ⟨Ca, h1, fun p hp => h2 p (Set.mem_union_right _ hp)⟩
  have hUA := fun w =>
    AutomorphicForm.contDiff_and_hasCompactSupport_prod_norm_archEval_pow_rpow_mul_of_tsupport K (A w) (hA w) (hAc w) (hCaA w)
      (-(1 / 2 : ℝ))
  have hUB := fun w =>
    AutomorphicForm.contDiff_and_hasCompactSupport_prod_norm_archEval_pow_rpow_mul_of_tsupport K (B w) (hB w) (hBc w) (hCaB w)
      (-(1 / 2 : ℝ))
  choose CaA hCaAc hCaAm using fun w => (hUA w).2.2
  choose CaB hCaBc hCaBm using fun w => (hUB w).2.2
  refine ⟨fun p => (c : ℂ) * ∑ w : NumberField.InfinitePlace K, ((w.mult : ℝ) : ℂ) * (DiscK.Rfac K p * A w p),
          fun w p => (c : ℂ) * ((w.mult : ℝ) : ℂ) * (DiscK.Rfac K p * B w p),
          fun w p => (c : ℂ) * ((w.mult : ℝ) : ℂ) * (DiscK.Rfac K p * B w p),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.mul (ContDiff.sum fun w _ => contDiff_const.mul (hUA w).1)
  · intro w; exact contDiff_const.mul (hUB w).1
  · intro w; exact contDiff_const.mul (hUB w).1
  · exact (DiscK.hasCompactSupport_finset_sum _ _ fun w _ => (hUA w).2.1.mul_left).mul_left
  · intro w; exact (hUB w).2.1.mul_left
  · intro w; exact (hUB w).2.1.mul_left
  ·
    intro p hp
    rcases hp with h | ⟨w, h | h⟩
    · have h' : ∑ w : NumberField.InfinitePlace K, ((w.mult : ℝ) : ℂ) * (DiscK.Rfac K p * A w p) ≠ 0 :=
        fun h0 => h (by beta_reduce; rw [h0, mul_zero])
      obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero h'
      have hw' : DiscK.Rfac K p * A w p ≠ 0 := fun h0 => hw (by rw [h0, mul_zero])
      obtain ⟨q, -, hq⟩ := hCaAm w p (subset_tsupport _ hw')
      exact DiscK.isUnit_of_eq_vec K p q hq
    · have hw' : DiscK.Rfac K p * B w p ≠ 0 := fun h0 => h (by beta_reduce; rw [h0, mul_zero])
      obtain ⟨q, -, hq⟩ := hCaBm w p (subset_tsupport _ hw')
      exact DiscK.isUnit_of_eq_vec K p q hq
    · have hw' : DiscK.Rfac K p * B w p ≠ 0 := fun h0 => h (by beta_reduce; rw [h0, mul_zero])
      obtain ⟨q, -, hq⟩ := hCaBm w p (subset_tsupport _ hw')
      exact DiscK.isUnit_of_eq_vec K p q hq
  ·
    refine ⟨⋃ w, (CaA w ∪ CaB w), isCompact_iUnion fun w => (hCaAc w).union (hCaBc w), fun p hp => ?_⟩
    rcases hp with h | h
    · have hex : ∃ w, p ∈ tsupport (fun p => DiscK.Rfac K p * A w p) := by
        by_contra h'
        push Not at h'
        apply DiscK.notMem_tsupport_finset_sum (Finset.univ) (fun w p => ((w.mult : ℝ) : ℂ) * (DiscK.Rfac K p * A w p)) p
          (fun w _ hw => h' w (tsupport_mul_subset_right (f := fun _ => ((w.mult : ℝ) : ℂ)) hw))
        exact tsupport_mul_subset_right (f := fun _ => (c : ℂ)) h
      obtain ⟨w, hw⟩ := hex
      obtain ⟨q, hq, hpq⟩ := hCaAm w p hw
      exact ⟨q, Set.mem_iUnion.mpr ⟨w, Or.inl hq⟩, hpq⟩
    · obtain ⟨w, hw⟩ := Set.mem_iUnion.mp h
      have h1 : p ∈ tsupport (fun p => DiscK.Rfac K p * B w p) := by
        rcases hw with h2 | h2 <;>
          exact tsupport_mul_subset_right (f := fun _ => (c : ℂ) * ((w.mult : ℝ) : ℂ)) h2
      obtain ⟨q, hq, hpq⟩ := hCaBm w p h1
      exact ⟨q, Set.mem_iUnion.mpr ⟨w, Or.inr hq⟩, hpq⟩
  ·
    intro a t hreg τ hτ hmap J I hJ hI
    obtain ⟨v, hv⟩ := DiscK.isUnit_one_sub_of_isRegularSemisimple K a t hreg
    obtain ⟨eI, eJ⟩ := hms a t hreg v hv τ hτ hmap J I hJ hI

    have hΛ : ∀ x : InfiniteAdeleRing K,
        Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] * ((DiscK.omega K (((v⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * x) : ℝ) : ℂ) =
          (∑ w : NumberField.InfinitePlace K, ((w.mult : ℝ) : ℂ) * (Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] * ((Real.log (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 +
                ‖NumberField.AdelicLevel.archEval K w x‖ ^ 2) : ℝ) : ℂ))) -
            ((∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) * (2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖) : ℝ) : ℂ) * Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] := by
      intro x
      rw [DiscK.omega_inv_mul K v x, hv]
      push_cast
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun w _ => by ring
      · exact mul_comm _ _
    have hint := fun w => hmain w a t
    obtain ⟨w0⟩ : Nonempty (NumberField.InfinitePlace K) := inferInstance
    have hIω : ∫ x, Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] * ((DiscK.omega K (((v⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * x) : ℝ) : ℂ)
          ∂(Measure.addHaar : Measure (InfiniteAdeleRing K)) =
        (∑ w : NumberField.InfinitePlace K, ((w.mult : ℝ) : ℂ) * (A w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] + ((DiscK.kink K w t : ℝ) : ℂ) * B w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)])) -
          (((∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) * (2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖)) : ℝ) : ℂ) *
            ∫ x, Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] ∂(Measure.addHaar : Measure (InfiniteAdeleRing K)) := by
      rw [show (fun x => Ψ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K x] * ((DiscK.omega K (((v⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * x) : ℝ) : ℂ)) = _
        from funext hΛ]
      rw [integral_sub (integrable_finsetSum _ fun w _ => ((hint w).2.1).const_mul _) (((hint w0).1).const_mul _),
        integral_finsetSum _ (fun w _ => ((hint w).2.1).const_mul _)]
      congr 1
      · refine Finset.sum_congr rfl fun w _ => ?_
        rw [integral_const_mul, (hint w).2.2]
      · rw [integral_const_mul]
    rw [hIω] at eJ

    have hPQ := DiscK.prodP_eq K t
    have hQN := DiscK.prodQ_eq K t
    have hν := DiscK.nu_eq K t
    have hR := DiscK.Rfac_vec K t a
    have hN : 0 < (∏ w : NumberField.InfinitePlace K, ‖(t : InfiniteAdeleRing K) w‖ ^ w.mult) :=
      Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (DiscK.unit_apply_ne_zero K t w)) _
    have e3 : (∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) * (2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖)) = 2 * (∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
    rw [e3] at eJ
    beta_reduce
    rw [hν]
    simp only [hR]
    have hSA : (∑ w : NumberField.InfinitePlace K, ((w.mult : ℝ) : ℂ) *
        (((((∏ w : NumberField.InfinitePlace K, ‖(t : InfiniteAdeleRing K) w‖ ^ w.mult) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) * A w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)])) =
        ((((∏ w : NumberField.InfinitePlace K, ‖(t : InfiniteAdeleRing K) w‖ ^ w.mult) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) * ∑ w : NumberField.InfinitePlace K, ((w.mult : ℝ) : ℂ) * A w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
    have hSY : (∑ w : NumberField.InfinitePlace K, ((w.mult : ℝ) : ℂ) * (A w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] + ((DiscK.kink K w t : ℝ) : ℂ) * B w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)])) =
        (∑ w : NumberField.InfinitePlace K, ((w.mult : ℝ) : ℂ) * A w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)]) +
          ∑ w : NumberField.InfinitePlace K, ((w.mult : ℝ) : ℂ) * (((DiscK.kink K w t : ℝ) : ℂ) * B w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)]) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun w _ => by ring
    rw [hSY] at eJ
    have hsplit :
        (∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal),
            ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) * ((c : ℂ) * ((w.mult : ℝ) : ℂ) * (((((∏ w : NumberField.InfinitePlace K, ‖(t : InfiniteAdeleRing K) w‖ ^ w.mult) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) * B w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)]))) +
          ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex),
            ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
              ((c : ℂ) * ((w.mult : ℝ) : ℂ) * (((((∏ w : NumberField.InfinitePlace K, ‖(t : InfiniteAdeleRing K) w‖ ^ w.mult) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) * B w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)])) =
        (c : ℂ) * ((((∏ w : NumberField.InfinitePlace K, ‖(t : InfiniteAdeleRing K) w‖ ^ w.mult) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) *
          ∑ w : NumberField.InfinitePlace K, ((w.mult : ℝ) : ℂ) * (((DiscK.kink K w t : ℝ) : ℂ) * B w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)]) := by
      rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun w : NumberField.InfinitePlace K => w.IsReal)]
      congr 1
      · refine Finset.sum_congr rfl fun w hw => ?_
        rw [Finset.mem_filter] at hw
        unfold DiscK.kink; rw [if_pos hw.2]; ring
      · refine Finset.sum_congr (Finset.filter_congr fun w _ => ?_) fun w hw => ?_
        · exact (NumberField.InfinitePlace.not_isReal_iff_isComplex).symm
        · rw [Finset.mem_filter] at hw
          unfold DiscK.kink; rw [if_neg hw.2]; push_cast; ring
    rw [hSA, add_assoc, hsplit]

    have hQ0 : ((∏ w : NumberField.InfinitePlace K, ‖((t⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) ≠ 0 := by
      rw [hQN]; exact_mod_cast (inv_ne_zero hN.ne')
    apply mul_left_cancel₀ hQ0
    rw [hPQ] at eJ eI
    push_cast at eJ eI ⊢
    linear_combination ((((∏ w : NumberField.InfinitePlace K, ‖(t : InfiniteAdeleRing K) w‖ ^ w.mult) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ) * eJ +
      (2 * (∑ w : NumberField.InfinitePlace K, (w.mult : ℂ) * ((Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ)) *
        ((((∏ w : NumberField.InfinitePlace K, ‖(t : InfiniteAdeleRing K) w‖ ^ w.mult) ^ (-(1 / 2 : ℝ))) : ℝ) : ℂ)) * eI

end S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex
end P2MW
export P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_weighted_eq_neg_two_mul_sum_log_mul_orbital_add_sum_real_add_sum_complex (solution)
