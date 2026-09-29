-- Prove2me | solution 1 for AutomorphicForm.exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_twistedWeighted_eq_neg_two_mul_finrank_mul_sum_log_mul_twistedOrbital_add_sum_real_add_sum_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/00b532ac-3c3a-51c5-9cf0-a951b39db54d

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_map_mul_sigmaTensor_sub_mul_addHaar_infiniteAdeleRing_eq_inv_prod_norm_archEval_algebraNorm_sub_pow_mult_smul
import Theorems.Thm_AutomorphicForm_exists_pos_forall_twistedOrbital_archHaarL_diagUnits2_eq_mul_integral_ker_norm_integral_integral_and_twistedWeighted_eq_of_coupled
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_integral_twistedConj_diagUnits2_mul_unipotentGL2_eq
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_mul_of_isReal
import Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_sq_mul_log_mul_of_isComplex
import Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq
import Theorems.Thm_AutomorphicForm_neg_log_archHeight_archIdentGL_sub_log_archHeight_adelicWeyl_mul_eq_sum_mult_mul_log
import Theorems.Thm_AutomorphicForm_contDiff_and_hasCompactSupport_prod_norm_archEval_pow_rpow_mul_of_tsupport
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup
import Theorems.Thm_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace
import Theorems.Thm_NumberField_InfiniteAdeleRing_isEmbedding_units_val
import Theorems.Thm_Algebra_TensorProduct_algebraMap_norm_eq_prod_map_algEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_twistedWeighted_eq_neg_two_mul_finrank_mul_sum_log_mul_twistedOrbital_add_sum_real_add_sum_complex
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 8192
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

noncomputable section

namespace DiscKL

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

end DiscKL
p2m_reactivate "P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_twistedWeighted_eq_neg_two_mul_finrank_mul_sum_log_mul_twistedOrbital_add_sum_real_add_sum_complex.DiscKL"

namespace DiscL

open AutomorphicForm Topology
open scoped Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (σ : L ≃ₐ[K] L)

set_option maxHeartbeats 4000000 in
theorem H0_measures :
    ∃ (mE : MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)) (_ : @BorelSpace (L ⊗[K] InfiniteAdeleRing K) _ mE) (lam : @Measure (L ⊗[K] InfiniteAdeleRing K) mE)
      (_ : @Measure.IsAddHaarMeasure (L ⊗[K] InfiniteAdeleRing K) _ _ mE lam)
      (mEu : MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ) (_ : @BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ _ mEu)
      (θ : @Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker (@Subtype.instMeasurableSpace _ _ mEu))
      (_ : @Measure.IsHaarMeasure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker _ _ (@Subtype.instMeasurableSpace _ _ mEu) θ)
      (κ : @Measure (↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) κ := by
  classical

  haveI : IsTopologicalRing (L ⊗[K] InfiniteAdeleRing K) := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  haveI : T2Space (L ⊗[K] InfiniteAdeleRing K) := (AutomorphicForm.archIdentHomeomorph K L).symm.t2Space
  haveI : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K) :=
    (AutomorphicForm.archIdentHomeomorph K L).isClosedEmbedding.locallyCompactSpace
  letI mE : MeasurableSpace (L ⊗[K] InfiniteAdeleRing K) := borel _
  haveI bE : BorelSpace (L ⊗[K] InfiniteAdeleRing K) := ⟨rfl⟩

  haveI : LocallyCompactSpace (L ⊗[K] InfiniteAdeleRing K)ˣ := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  letI mEu : MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ := borel _
  haveI bEu : BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ := ⟨rfl⟩

  have hNc : Continuous (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) → InfiniteAdeleRing K) := by
    let b : Module.Basis (Fin (Module.finrank K L)) (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) :=
      (Module.finBasis K L).rightBaseChange L
    have hrepr : ∀ k, Continuous fun x : (L ⊗[K] InfiniteAdeleRing K) => b.repr x k := fun k =>
      (continuous_apply k).comp (IsModuleTopology.continuousLinearEquiv b.equivFun).continuous
    have hM : Continuous fun x : (L ⊗[K] InfiniteAdeleRing K) =>
        LinearMap.toMatrix b b (Algebra.lmul (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) x : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K)) := by
      refine continuous_matrix fun k j => ?_
      simp only [LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul]
      exact (hrepr k).comp (continuous_id.mul continuous_const)
    have h := hM.matrix_det
    convert h using 1
    funext x
    rw [Algebra.norm_apply, LinearMap.det_toMatrix]
  have hU : IsClosed (((Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker : Subgroup (L ⊗[K] InfiniteAdeleRing K)ˣ) : Set (L ⊗[K] InfiniteAdeleRing K)ˣ) := by
    have hc : Continuous (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)) :=
      Continuous.units_map _ hNc
    have : (((Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker : Subgroup (L ⊗[K] InfiniteAdeleRing K)ˣ) : Set (L ⊗[K] InfiniteAdeleRing K)ˣ) =
        (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)) ⁻¹' {1} := by
      ext u; simp [MonoidHom.mem_ker]
    rw [this]
    exact (isClosed_singleton).preimage hc
  haveI : LocallyCompactSpace ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker := hU.isClosedEmbedding_subtypeVal.locallyCompactSpace

  letI mK : MeasurableSpace ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := borel _
  haveI bK : BorelSpace ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := ⟨rfl⟩
  have hset : ((⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
      (AutomorphicForm.archIdentGLEquiv K L) ⁻¹' ((⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent L w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing L))) : Set (GL (Fin 2) (InfiniteAdeleRing L))) := by
    ext k
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.coe_comp,
      Function.comp_apply]
    rfl
  have hKc : IsCompact ((⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) : Set (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := by
    rw [hset]
    exact (AutomorphicForm.archIdentGLEquiv K L).toHomeomorph.isCompact_preimage.mpr
      (NumberField.InfiniteAdeleRing.exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup L).2
  haveI : CompactSpace ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := isCompact_iff_compactSpace.mp hKc
  refine ⟨mE, bE, Measure.addHaar, ?_, mEu, bEu, Measure.haar, ?_, Measure.haar, ?_⟩
  all_goals infer_instance

def omegaPlace (w : InfinitePlace K) (y : (L ⊗[K] InfiniteAdeleRing K)) : ℝ :=
  ∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
    (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L y)‖ ^ 2)

def omega (y : (L ⊗[K] InfiniteAdeleRing K)) : ℝ :=
  ∑ w' : NumberField.InfinitePlace L, (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L y)‖ ^ 2)

theorem omega_eq_sum_omegaPlace (y : (L ⊗[K] InfiniteAdeleRing K)) : omega K L y = ∑ w : InfinitePlace K, omegaPlace K L w y := by
  classical
  unfold omega omegaPlace
  exact (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ)
    (g := fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L)) (fun _ _ => Finset.mem_univ _) _).symm

theorem continuous_omega : Continuous (omega K L) := by
  unfold omega
  refine continuous_finset_sum _ fun w _ => continuous_const.mul ?_
  have hc : Continuous (fun y : (L ⊗[K] InfiniteAdeleRing K) => NumberField.AdelicLevel.archEval L w (AutomorphicForm.archIdent K L y)) :=
    (continuous_apply w).comp (AutomorphicForm.archIdentHomeomorph K L).continuous
  exact (continuous_const.add ((hc.norm).pow 2)).log fun y =>
    ne_of_gt (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _))

theorem weight_iwasawa :
    ∀ (u' t' : (L ⊗[K] InfiniteAdeleRing K)ˣ) (y : (L ⊗[K] InfiniteAdeleRing K)) (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)),
      k ∈ (⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) →
      (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
            -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
              - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                  (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                    AutomorphicForm.archIdentGL K L y)))
        (Matrix.GeneralLinearGroup.scalar (Fin 2) u' * diagUnits2 t' 1 * AutomorphicForm.unipotentGL2 y * k) =
      omega K L y := by
  intro u' t' y k hk

  have he1 : AutomorphicForm.archIdentGL K L (Matrix.GeneralLinearGroup.scalar (Fin 2) u') =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
        (Units.map (AutomorphicForm.archIdent K L : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing L) u') := by
    apply Units.ext; ext i j
    fin_cases i <;> fin_cases j <;> simp [AutomorphicForm.archIdentGL, Matrix.GeneralLinearGroup.map]
  have he2 : AutomorphicForm.archIdentGL K L (diagUnits2 t' 1) =
      diagUnits2 (Units.map (AutomorphicForm.archIdent K L : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing L) t') 1 := by
    apply Units.ext; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [AutomorphicForm.archIdentGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2]
  have he3 : AutomorphicForm.archIdentGL K L (AutomorphicForm.unipotentGL2 y) =
      AutomorphicForm.unipotentGL2 (AutomorphicForm.archIdent K L y) := by
    apply Units.ext; ext i j
    fin_cases i <;> fin_cases j <;> simp [AutomorphicForm.archIdentGL, Matrix.GeneralLinearGroup.map, AutomorphicForm.unipotentGL2]
  have hk' : AutomorphicForm.archIdentGL K L k ∈ (⨅ w : InfinitePlace L,
      (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (NumberField.AdelicLevel.archComponent L w) :
        Subgroup (GL (Fin 2) (InfiniteAdeleRing L))) := by
    simp only [Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply] at hk ⊢
    exact hk
  show DiscKL.archWeight L (AutomorphicForm.archIdentGL K L
      (Matrix.GeneralLinearGroup.scalar (Fin 2) u' * diagUnits2 t' 1 * AutomorphicForm.unipotentGL2 y * k)) = omega K L y
  rw [map_mul, map_mul, map_mul, he1, he2, he3, DiscKL.archWeight_scalar_diagUnits2_unipotent_mul L _ _ _ _ hk']
  rfl

theorem continuous_weight :
    Continuous (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
            -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
              - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                  (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                    AutomorphicForm.archIdentGL K L y))) := by
  have hloc : ∀ {F : Type} [NormedField F], Continuous (fun g : GL (Fin 2) F => AutomorphicForm.WindowedSiegel.localHeight g) := by
    intro F _
    unfold AutomorphicForm.WindowedSiegel.localHeight AutomorphicForm.WindowedSiegel.rowNormSq
    refine Continuous.div ?_ ?_ (fun g => (AutomorphicForm.WindowedSiegel.rowNormSq_pos g).ne')
    · exact (Units.continuous_val.matrix_det).norm
    · exact ((Units.continuous_val.matrix_elem 1 0).norm.pow 2).add ((Units.continuous_val.matrix_elem 1 1).norm.pow 2)
  have hH : Continuous (AutomorphicForm.WindowedSiegel.archHeight L) := by
    unfold AutomorphicForm.WindowedSiegel.archHeight
    exact continuous_finset_prod _ fun v _ => (hloc.comp (continuous_archComponent L v)).pow _
  have he : Continuous (AutomorphicForm.archIdentGL K L) := (AutomorphicForm.archIdentGLEquiv K L).continuous
  refine ((hH.comp he).log fun x => (AutomorphicForm.WindowedSiegel.archHeight_pos L _).ne').neg.sub ?_
  exact ((hH.comp (continuous_const.mul he))).log fun x => (AutomorphicForm.WindowedSiegel.archHeight_pos L _).ne'

section HNorm

variable (A : Type) [CommRing A] [Algebra K A]

theorem norm_algEquiv {S T : Type} [Ring S] [Ring T] [Algebra A S] [Algebra A T] (e : S ≃ₐ[A] T) (x : S) :
    Algebra.norm A (e x) = Algebra.norm A x := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : (Algebra.lmul A T (e x) : T →ₗ[A] T) =
      (e.toLinearEquiv : S →ₗ[A] T) ∘ₗ (Algebra.lmul A S x : S →ₗ[A] S) ∘ₗ (e.toLinearEquiv.symm : T →ₗ[A] S) := by
    ext y
    simp [Algebra.coe_lmul_eq_mul]
  rw [h, LinearMap.det_conj]

theorem rcomm_tmul (a : A) (l : L) :
    TensorProduct.RightActions.Algebra.TensorProduct.comm K A L (a ⊗ₜ[K] l) = l ⊗ₜ[K] a := by
  rfl

theorem rcomm_map (g : L ≃ₐ[K] L) (z : A ⊗[K] L) :
    TensorProduct.RightActions.Algebra.TensorProduct.comm K A L (Algebra.TensorProduct.map (AlgHom.id K A) (g : L →ₐ[K] L) z) =
      AutomorphicForm.sigmaTensor K L A g (TensorProduct.RightActions.Algebra.TensorProduct.comm K A L z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a l =>
    rw [Algebra.TensorProduct.map_tmul, rcomm_tmul, rcomm_tmul]
    show (g : L →ₐ[K] L) l ⊗ₜ[K] (AlgHom.id K A) a = (Algebra.TensorProduct.map (g : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)
    rw [Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem algebraMap_norm_eq_prod_sigmaTensor (x : L ⊗[K] A) :
    algebraMap A (L ⊗[K] A) (Algebra.norm A x) = ∏ g : L ≃ₐ[K] L, AutomorphicForm.sigmaTensor K L A g x := by
  classical
  set c := TensorProduct.RightActions.Algebra.TensorProduct.comm K A L with hc
  obtain ⟨z, rfl⟩ : ∃ z, x = c z := ⟨c.symm x, (c.apply_symm_apply x).symm⟩
  rw [norm_algEquiv, ← c.commutes, Algebra.TensorProduct.algebraMap_norm_eq_prod_map_algEquiv K L A z, map_prod]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [hc, rcomm_map]

theorem sigmaTensor_iterate (i : ℕ) (x : L ⊗[K] A) :
    (AutomorphicForm.sigmaTensor K L A σ)^[i] x = AutomorphicForm.sigmaTensor K L A (σ ^ i) x := by
  induction i generalizing x with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      show l ⊗ₜ[K] a = (Algebra.TensorProduct.map ((1 : L ≃ₐ[K] L) : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)
      rw [Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy => rw [map_add, ← hx, ← hy]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, pow_succ']
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul l a =>
      show (Algebra.TensorProduct.map (σ : L →ₐ[K] L) (AlgHom.id K A))
          ((Algebra.TensorProduct.map ((σ ^ n : L ≃ₐ[K] L) : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)) =
        (Algebra.TensorProduct.map ((σ * σ ^ n : L ≃ₐ[K] L) : L →ₐ[K] L) (AlgHom.id K A)) (l ⊗ₜ[K] a)
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]; rfl
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add]

theorem list_prod_range_eq {M : Type} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.prod_range_succ, Finset.prod_range_succ, ih]

theorem orderOf_eq_finrank' (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    orderOf σ = Module.finrank K L := by
  rw [← IsGalois.card_aut_eq_finrank, orderOf_eq_card_of_forall_mem_zpowers hgen, Nat.card_eq_fintype_card]

theorem algebraMap_norm_eq_prod_range (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (x : L ⊗[K] A) :
    algebraMap A (L ⊗[K] A) (Algebra.norm A x) =
      ((List.range (Module.finrank K L)).map fun i => (AutomorphicForm.sigmaTensor K L A σ)^[i] x).prod := by
  classical
  rw [algebraMap_norm_eq_prod_sigmaTensor, list_prod_range_eq]
  have hn : orderOf σ = Module.finrank K L := orderOf_eq_finrank' K L σ hgen
  have hinj : Set.InjOn (fun i : ℕ => σ ^ i) (Finset.range (Module.finrank K L) : Set ℕ) := by
    intro i hi j hj hij
    rw [Finset.coe_range, Set.mem_Iio, ← hn] at hi hj
    exact pow_injOn_Iio_orderOf hi hj hij
  have himg : (Finset.range (Module.finrank K L)).image (fun i : ℕ => σ ^ i) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ← Nat.card_eq_fintype_card,
      IsGalois.card_aut_eq_finrank]
  rw [← himg, Finset.prod_image hinj]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [sigmaTensor_iterate]

end HNorm
p2m_reactivate "P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_twistedWeighted_eq_neg_two_mul_finrank_mul_sum_log_mul_twistedOrbital_add_sum_real_add_sum_complex.DiscKL"

section HNorm2

variable (A : Type) [CommRing A] [Algebra K A]

theorem sigmaGL_diagUnits2 (x y : (L ⊗[K] A)ˣ) :
    AutomorphicForm.sigmaGL K L A σ (diagUnits2 x y) =
      diagUnits2 (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A) x)
        (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A) y) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.sigmaGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2]

omit σ in
theorem diagUnits2_mul (x y x' y' : (L ⊗[K] A)ˣ) :
    diagUnits2 x y * diagUnits2 x' y' = diagUnits2 (x * x') (y * y') := by
  apply Units.ext
  rw [Units.val_mul, LanglandsTunnell.CubicInduction.coe_diagUnits2, LanglandsTunnell.CubicInduction.coe_diagUnits2,
    LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sigmaGL_iterate_diagUnits2 (i : ℕ) (x y : (L ⊗[K] A)ˣ) :
    (AutomorphicForm.sigmaGL K L A σ)^[i] (diagUnits2 x y) =
      diagUnits2 ((Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A))^[i] x)
        ((Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A))^[i] y) := by
  induction i with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, sigmaGL_diagUnits2, Function.iterate_succ_apply',
      Function.iterate_succ_apply']

theorem normString_diagUnits2 (x y : (L ⊗[K] A)ˣ) :
    AutomorphicForm.normString K L A σ (diagUnits2 x y) =
      diagUnits2 (((List.range (Module.finrank K L)).map fun i =>
          (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A))^[i] x).prod)
        (((List.range (Module.finrank K L)).map fun i =>
          (Units.map (AutomorphicForm.sigmaTensor K L A σ : L ⊗[K] A →* L ⊗[K] A))^[i] y).prod) := by
  unfold AutomorphicForm.normString
  induction Module.finrank K L with
  | zero =>
    simp only [List.range_zero, List.map_nil, List.prod_nil]
    apply Units.ext
    rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ n ih => rw [List.prod_range_succ, List.prod_range_succ, List.prod_range_succ, ih, sigmaGL_iterate_diagUnits2,
      diagUnits2_mul]

omit σ in
theorem toTensorGL_diagUnits2 (a b : Aˣ) :
    AutomorphicForm.toTensorGL K L A (diagUnits2 a b) =
      diagUnits2 (Units.map (algebraMap A (L ⊗[K] A) : A →* L ⊗[K] A) a)
        (Units.map (algebraMap A (L ⊗[K] A) : A →* L ⊗[K] A) b) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.toTensorGL, Matrix.GeneralLinearGroup.map, LanglandsTunnell.CubicInduction.coe_diagUnits2,
      TensorProduct.RightActions.algebraMap_eval, Algebra.TensorProduct.includeRight_apply]

omit σ in
theorem val_list_prod_iterate_map (f : L ⊗[K] A →* L ⊗[K] A) (x : (L ⊗[K] A)ˣ) (m : ℕ) :
    ((((List.range m).map fun i => (Units.map f)^[i] x).prod : (L ⊗[K] A)ˣ) : L ⊗[K] A) =
      ((List.range m).map fun i => (⇑f)^[i] (x : L ⊗[K] A)).prod := by
  have hit : ∀ i, (((Units.map f)^[i] x : (L ⊗[K] A)ˣ) : L ⊗[K] A) = (⇑f)^[i] (x : L ⊗[K] A) := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Units.coe_map, ih]
  induction m with
  | zero => simp
  | succ n ih => rw [List.prod_range_succ, List.prod_range_succ, Units.val_mul, ih, hit]

omit σ in
theorem algebraMap_tensor_injective : Function.Injective (algebraMap A (L ⊗[K] A)) := by
  have h : (algebraMap A (L ⊗[K] A) : A → L ⊗[K] A) =
      (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A) := by
    funext a
    rw [TensorProduct.RightActions.algebraMap_eval, Algebra.TensorProduct.includeRight_apply]
  rw [h]
  exact Algebra.TensorProduct.includeRight_injective (algebraMap K L).injective

theorem norm_eq_of_normString_diagUnits2 (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (a b : Aˣ) (α β : (L ⊗[K] A)ˣ)
    (h : AutomorphicForm.normString K L A σ (diagUnits2 α β) = AutomorphicForm.toTensorGL K L A (diagUnits2 a b)) :
    Algebra.norm A (α : L ⊗[K] A) = a ∧ Algebra.norm A (β : L ⊗[K] A) = b := by
  rw [normString_diagUnits2, toTensorGL_diagUnits2] at h
  have hv := congrArg (fun g : GL (Fin 2) (L ⊗[K] A) => (g : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) h
  simp only [LanglandsTunnell.CubicInduction.coe_diagUnits2] at hv
  have h00 := congrFun (congrFun hv 0) 0
  have h11 := congrFun (congrFun hv 1) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const] at h00 h11
  rw [val_list_prod_iterate_map, Units.coe_map] at h00 h11
  have h00' : ((List.range (Module.finrank K L)).map fun i =>
      (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] (α : L ⊗[K] A)).prod = algebraMap A (L ⊗[K] A) a := h00
  have h11' : ((List.range (Module.finrank K L)).map fun i =>
      (⇑(AutomorphicForm.sigmaTensor K L A σ))^[i] (β : L ⊗[K] A)).prod = algebraMap A (L ⊗[K] A) b := h11
  rw [← algebraMap_norm_eq_prod_range K L σ A hgen] at h00' h11'
  exact ⟨algebraMap_tensor_injective K L A h00', algebraMap_tensor_injective K L A h11'⟩

end HNorm2
p2m_reactivate "P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_twistedWeighted_eq_neg_two_mul_finrank_mul_sum_log_mul_twistedOrbital_add_sum_real_add_sum_complex.DiscKL"

theorem norm_of_normString_eq (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (a t : (InfiniteAdeleRing K)ˣ) (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    (h : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)))
    (u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) :
    Algebra.norm (InfiniteAdeleRing K) (1 : (L ⊗[K] InfiniteAdeleRing K)) -
        Algebra.norm (InfiniteAdeleRing K) (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) = 1 - (t : InfiniteAdeleRing K) := by
  obtain ⟨hα, hβ⟩ := norm_eq_of_normString_diagUnits2 K L σ (InfiniteAdeleRing K) hgen a (a * t) α β h
  have hNα : (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)) α = a := Units.ext (by rw [Units.coe_map]; exact hα)
  have hNβ : (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)) β = a * t := Units.ext (by rw [Units.coe_map]; exact hβ)
  have hu1 : (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)) (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) = 1 := (MonoidHom.mem_ker).mp u.1.2
  have hu2 : (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)) (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) = 1 := (MonoidHom.mem_ker).mp u.2.2
  have hr : (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)) ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ))) = t := by
    rw [map_mul, map_inv, map_mul, map_mul, hNα, hNβ, hu1, hu2, mul_one, mul_one, inv_mul_cancel_left]
  have hval : Algebra.norm (InfiniteAdeleRing K) (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) = (t : InfiniteAdeleRing K) := by
    have := congrArg Units.val hr
    rw [Units.coe_map] at this
    exact this
  rw [map_one, hval]

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
    Real.finsetProd_rpow _ _ (fun w _ => pow_nonneg (norm_nonneg _) _),
    Real.rpow_neg (Finset.prod_nonneg fun w _ => pow_nonneg (norm_nonneg _) _), div_eq_mul_inv]

section NCls

abbrev Nm : Subgroup (InfiniteAdeleRing K)ˣ :=
  (Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).range

omit σ in
theorem unit_apply_ne_zero (p : (InfiniteAdeleRing K)ˣ) (v : InfinitePlace K) : (p : InfiniteAdeleRing K) v ≠ 0 := by
  intro h
  have h1 : (p : InfiniteAdeleRing K) v * ((p⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v = 1 :=
    congrArg (fun z : InfiniteAdeleRing K => z v) p.mul_inv
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

omit σ in

theorem exists_pow_eq_of_norm_sub_one_lt (x : (InfiniteAdeleRing K)ˣ)
    (hx : ∀ v : InfinitePlace K, v.IsReal → ‖(x : InfiniteAdeleRing K) v - 1‖ < 1) :
    ∃ y : (InfiniteAdeleRing K)ˣ, y ^ Module.finrank K L = x := by
  classical
  have hn : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'

  have hroot : ∀ v : InfinitePlace K, ∃ r : v.Completion, r ^ Module.finrank K L = (x : InfiniteAdeleRing K) v := by
    intro v
    by_cases hv : v.IsReal
    · let e := NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv
      have hpos : 0 ≤ e ((x : InfiniteAdeleRing K) v) := by
        have h1 : |e ((x : InfiniteAdeleRing K) v - 1)| < 1 := by
          rw [NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal_apply, ← Real.norm_eq_abs,
            (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _)]
          exact hx v hv
        rw [map_sub, map_one] at h1
        have := abs_sub_lt_iff.mp h1
        linarith
      refine ⟨e.symm ((e ((x : InfiniteAdeleRing K) v)) ^ ((Module.finrank K L : ℝ)⁻¹)), ?_⟩
      apply e.injective
      rw [map_pow, e.apply_symm_apply, Real.rpow_inv_natCast_pow hpos hn]
    · have hv' : v.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hv
      let e := NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv'
      refine ⟨e.symm ((e ((x : InfiniteAdeleRing K) v)) ^ ((Module.finrank K L : ℂ)⁻¹)), ?_⟩
      apply e.injective
      rw [map_pow, e.apply_symm_apply, Complex.cpow_nat_inv_pow _ hn]
  choose r hr using hroot
  have hru : IsUnit (r : InfiniteAdeleRing K) := by
    refine Pi.isUnit_iff.mpr fun v => isUnit_iff_ne_zero.mpr fun h0 => ?_
    have := hr v
    rw [h0, zero_pow hn] at this
    exact unit_apply_ne_zero K x v this.symm
  refine ⟨hru.unit, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
  funext v
  exact hr v

theorem isOpen_Nm : IsOpen ((Nm K L : Subgroup (InfiniteAdeleRing K)ˣ) : Set (InfiniteAdeleRing K)ˣ) := by
  classical
  apply Subgroup.isOpen_of_mem_nhds (g := 1)

  have hV : IsOpen {x : InfiniteAdeleRing K | ∀ v : InfinitePlace K, v.IsReal → ‖x v - 1‖ < 1} := by
    have : {x : InfiniteAdeleRing K | ∀ v : InfinitePlace K, v.IsReal → ‖x v - 1‖ < 1} =
        ⋂ v ∈ {v : InfinitePlace K | v.IsReal}, {x : InfiniteAdeleRing K | ‖x v - 1‖ < 1} := by
      ext x; simp
    rw [this]
    refine Set.Finite.isOpen_biInter (Set.toFinite _) fun v _ => ?_
    have hc : Continuous fun x : InfiniteAdeleRing K => ‖x v - 1‖ :=
      ((continuous_apply v).sub continuous_const).norm
    exact isOpen_lt hc continuous_const
  have h1 : ((1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) ∈
      {x : InfiniteAdeleRing K | ∀ v : InfinitePlace K, v.IsReal → ‖x v - 1‖ < 1} := by
    intro v _
    show ‖(1 : InfiniteAdeleRing K) v - 1‖ < 1
    have : (1 : InfiniteAdeleRing K) v = 1 := rfl
    rw [this, sub_self, norm_zero]; exact one_pos
  refine Filter.mem_of_superset ((hV.preimage Units.continuous_val).mem_nhds h1) fun x hx => ?_
  obtain ⟨y, hy⟩ := exists_pow_eq_of_norm_sub_one_lt K L x hx
  refine ⟨Units.map (algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) : _ →* _) y, ?_⟩
  apply Units.ext
  rw [Units.coe_map, Units.coe_map]
  show Algebra.norm (InfiniteAdeleRing K) (algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) (y : InfiniteAdeleRing K)) = (x : InfiniteAdeleRing K)
  rw [Algebra.norm_algebraMap, TensorProduct.finrank_rightAlgebra L, ← hy, Units.val_pow_eq_pow_val]

end NCls
p2m_reactivate "P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_twistedWeighted_eq_neg_two_mul_finrank_mul_sum_log_mul_twistedOrbital_add_sum_real_add_sum_complex.DiscKL"

omit L σ in
theorem TwKAvgE_continuous_iota_symm : Continuous (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  have h := NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace K
  have e : ⇑(NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm = ⇑(h.homeomorph _).symm := by
    funext y
    apply (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
    rw [RingEquiv.apply_symm_apply]
    exact ((h.homeomorph _).apply_symm_apply y).symm
  rw [e]
  exact (h.homeomorph _).symm.continuous

theorem exists_normClass_cutoff (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime) :
    ∃ χ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℝ,
      (∀ F : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        (∀ p ∈ tsupport F, IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ).symm (p 0)) ∧ IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ).symm (p 1))) →
        ContDiff ℝ (⊤ : ℕ∞) (fun p => ((χ p : ℝ) : ℂ) * F p)) ∧
      (∀ a t : (InfiniteAdeleRing K)ˣ,
        (¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (diagUnits2 a (a * t)) δ) →
          χ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] = 0) ∧
      (∀ (a t : (InfiniteAdeleRing K)ˣ) (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ),
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)) →
          χ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] = 1) := by
  classical

  let g₁ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → InfiniteAdeleRing K := fun p => (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1)
  let g₂ : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → InfiniteAdeleRing K :=
    fun p => (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1) * (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0)
  let cond : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → Prop := fun p =>
    ∃ α β : (L ⊗[K] InfiniteAdeleRing K)ˣ, Algebra.norm (InfiniteAdeleRing K) (α : (L ⊗[K] InfiniteAdeleRing K)) = g₁ p ∧
      Algebra.norm (InfiniteAdeleRing K) (β : (L ⊗[K] InfiniteAdeleRing K)) = g₂ p
  refine ⟨fun p => if cond p then 1 else 0, ?_, ?_, ?_⟩
  rotate_left
  ·
    intro a t hno
    beta_reduce
    rw [if_neg]
    rintro ⟨α, β, hα, hβ⟩
    apply hno
    simp only [g₁, g₂, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, RingEquiv.symm_apply_apply] at hα hβ
    refine ⟨diagUnits2 α β, 1, ?_⟩
    show AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)) =
      1⁻¹ * AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) * 1
    rw [inv_one, one_mul, mul_one, normString_diagUnits2, toTensorGL_diagUnits2]
    congr 1 <;> apply Units.ext <;>
      rw [val_list_prod_iterate_map, Units.coe_map, MonoidHom.coe_coe]
    · show algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) (a : InfiniteAdeleRing K) = _
      rw [← hα, algebraMap_norm_eq_prod_range K L σ (InfiniteAdeleRing K) hgen]; rfl
    · show algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) ((a * t : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = _
      rw [Units.val_mul, ← hβ, algebraMap_norm_eq_prod_range K L σ (InfiniteAdeleRing K) hgen]; rfl
  ·
    intro a t α β h
    beta_reduce
    rw [if_pos]
    obtain ⟨hα, hβ⟩ := norm_eq_of_normString_diagUnits2 K L σ (InfiniteAdeleRing K) hgen a (a * t) α β h
    refine ⟨α, β, ?_, ?_⟩
    · simp only [g₁, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Matrix.cons_val_fin_one, RingEquiv.symm_apply_apply]; exact hα
    · simp only [g₂, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, RingEquiv.symm_apply_apply, hβ,
        Units.val_mul]
  ·
    intro F hF hFc hFu

    have hunits : IsOpen {y : InfiniteAdeleRing K | IsUnit y} := by
      have h : {y : InfiniteAdeleRing K | IsUnit y} = ⋂ w : InfinitePlace K, {y | y w ≠ 0} := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_iInter]
        exact (@Pi.isUnit_iff (InfinitePlace K) (fun w => w.Completion) _ y).trans
          (forall_congr' fun w => isUnit_iff_ne_zero)
      rw [h]
      exact isOpen_iInter_of_finite fun w => isOpen_ne_fun (continuous_apply w) continuous_const
    have hrange : Set.range (Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) = {y | IsUnit y} := by
      ext y; exact ⟨fun ⟨u, hu⟩ => hu ▸ u.isUnit, fun hy => ⟨hy.unit, hy.unit_spec⟩⟩
    have hopen : IsOpenMap (Units.val : (InfiniteAdeleRing K)ˣ → InfiniteAdeleRing K) :=
      (NumberField.InfiniteAdeleRing.isEmbedding_units_val K).isInducing.isOpenMap (hrange ▸ hunits)
    have hNo : IsOpen ((Nm K L : Subgroup (InfiniteAdeleRing K)ˣ) : Set (InfiniteAdeleRing K)ˣ) := isOpen_Nm K L
    have hNc : IsClosed ((Nm K L : Subgroup (InfiniteAdeleRing K)ˣ) : Set (InfiniteAdeleRing K)ˣ) :=
      Subgroup.isClosed_of_isOpen _ hNo
    set T : Set (InfiniteAdeleRing K) := Units.val '' ((Nm K L : Subgroup (InfiniteAdeleRing K)ˣ) : Set (InfiniteAdeleRing K)ˣ) with hT
    set T' : Set (InfiniteAdeleRing K) := Units.val '' ((Nm K L : Subgroup (InfiniteAdeleRing K)ˣ) : Set (InfiniteAdeleRing K)ˣ)ᶜ with hT'
    have hTo : IsOpen T := hopen _ hNo
    have hT'o : IsOpen T' := hopen _ hNc.isOpen_compl
    have hTT' : ∀ z, z ∈ T → z ∉ T' := by
      rintro z ⟨u, hu, rfl⟩ ⟨u', hu', h⟩
      exact hu' (Units.ext h ▸ hu)

    have hmemT : ∀ z : InfiniteAdeleRing K, (∃ α : (L ⊗[K] InfiniteAdeleRing K)ˣ, Algebra.norm (InfiniteAdeleRing K) (α : (L ⊗[K] InfiniteAdeleRing K)) = z) ↔ z ∈ T := by
      intro z
      constructor
      · rintro ⟨α, hα⟩
        refine ⟨Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K) α, ⟨α, rfl⟩, ?_⟩
        rw [Units.coe_map]; exact hα
      · rintro ⟨u, ⟨α, hα⟩, rfl⟩
        exact ⟨α, by rw [← hα, Units.coe_map]⟩
    have hdich : ∀ z : InfiniteAdeleRing K, IsUnit z → z ∈ T ∨ z ∈ T' := by
      intro z hz
      by_cases h : hz.unit ∈ ((Nm K L : Subgroup (InfiniteAdeleRing K)ˣ) : Set (InfiniteAdeleRing K)ˣ)
      · exact Or.inl ⟨hz.unit, h, hz.unit_spec⟩
      · exact Or.inr ⟨hz.unit, h, hz.unit_spec⟩
    have hcond : ∀ p, cond p ↔ g₁ p ∈ T ∧ g₂ p ∈ T := by
      intro p
      constructor
      · rintro ⟨α, β, hα, hβ⟩; exact ⟨(hmemT _).mp ⟨α, hα⟩, (hmemT _).mp ⟨β, hβ⟩⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨α, hα⟩ := (hmemT _).mpr h1
        obtain ⟨β, hβ⟩ := (hmemT _).mpr h2
        exact ⟨α, β, hα, hβ⟩
    have hg₁ : Continuous g₁ := (TwKAvgE_continuous_iota_symm K).comp (continuous_apply 1)
    have hg₂ : Continuous g₂ :=
      ((TwKAvgE_continuous_iota_symm K).comp (continuous_apply 1)).mul ((TwKAvgE_continuous_iota_symm K).comp (continuous_apply 0))

    have hloc : ∀ p₀, IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p₀ 0)) → IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p₀ 1)) →
        ∀ᶠ p in nhds p₀, cond p ↔ cond p₀ := by
      intro p₀ h0 h1
      have hu1 : IsUnit (g₁ p₀) := h1
      have hu2 : IsUnit (g₂ p₀) := h1.mul h0
      have key : ∀ (g : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → InfiniteAdeleRing K), Continuous g →
          IsUnit (g p₀) → ∀ᶠ p in nhds p₀, (g p ∈ T ↔ g p₀ ∈ T) := by
        intro g hg hu
        rcases hdich _ hu with h | h
        · filter_upwards [hg.continuousAt.preimage_mem_nhds (hTo.mem_nhds h)] with p hp
          exact ⟨fun _ => h, fun _ => hp⟩
        · filter_upwards [hg.continuousAt.preimage_mem_nhds (hT'o.mem_nhds h)] with p hp
          exact ⟨fun hp' => (hTT' _ hp' hp).elim, fun h' => (hTT' _ h' h).elim⟩
      filter_upwards [key g₁ hg₁ hu1, key g₂ hg₂ hu2] with p e1 e2
      rw [hcond, hcond, e1, e2]

    refine contDiff_iff_contDiffAt.mpr fun p => ?_
    by_cases hp : p ∈ tsupport F
    · obtain ⟨h0, h1⟩ := hFu p hp
      have hev : (fun q => (((if cond q then (1 : ℝ) else 0) : ℝ) : ℂ) * F q) =ᶠ[nhds p]
          fun q => (((if cond p then (1 : ℝ) else 0) : ℝ) : ℂ) * F q := by
        filter_upwards [hloc p h0 h1] with q hq
        simp only [hq]
      exact ((contDiff_const.mul hF).contDiffAt).congr_of_eventuallyEq hev
    · have hF0 := notMem_tsupport_iff_eventuallyEq.mp hp
      have hev : (fun q => (((if cond q then (1 : ℝ) else 0) : ℝ) : ℂ) * F q) =ᶠ[nhds p] fun _ => 0 := by
        filter_upwards [hF0] with q hq
        rw [hq, Pi.zero_apply, mul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq hev

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

theorem apply_ne_one_of_isRegularSemisimple (a t : (InfiniteAdeleRing K)ˣ)
    (hreg : AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t))) :
    ∀ v : NumberField.InfinitePlace K, (t : InfiniteAdeleRing K) v ≠ 1 := by
  intro v h1

  have hu : IsUnit ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) := by
    unfold AutomorphicForm.IsRegularSemisimple at hreg
    rw [LanglandsTunnell.CubicInduction.coe_diagUnits2, Matrix.trace_fin_two_of, Matrix.det_fin_two_of] at hreg
    have e : ((a : InfiniteAdeleRing K) + ((a * t : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) ^ 2 -
        4 * ((a : InfiniteAdeleRing K) * ((a * t : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) - 0 * 0) =
        ((a : InfiniteAdeleRing K) * ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))) ^ 2 := by
      push_cast; ring
    rw [e, isUnit_pow_iff two_ne_zero] at hreg
    exact isUnit_of_mul_isUnit_right hreg
  have hw := ((@Pi.isUnit_iff (NumberField.InfinitePlace K) (fun w => w.Completion) _ _).mp hu) v
  have : ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) v = 0 := by
    show (1 : InfiniteAdeleRing K) v - (t : InfiniteAdeleRing K) v = 0
    rw [h1]; exact sub_self _
  rw [this] at hw
  exact not_isUnit_zero hw

theorem measure_side (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (τ₀ : Measure (InfiniteAdeleRing K × InfiniteAdeleRing K))
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) [θ.IsHaarMeasure]
    (κ : @Measure (↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) (borel _)) (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ) :
    ∃ c : ℝ, 0 < c ∧ ∃ Φ : (Fin 3 → NumberField.mixedEmbedding.mixedSpace L) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      (∃ C : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ), IsCompact C ∧
        ∀ p ∈ tsupport Φ, ∃ q ∈ C,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ), AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t)) →
      ∀ (τ : Measure (Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
        τ.IsHaarMeasure →
        Measure.map
            (fun x : Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
              ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
                ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
                InfiniteAdeleRing K × InfiniteAdeleRing K))
            τ = τ₀ →
      ∀ α β : (L ⊗[K] InfiniteAdeleRing K)ˣ,
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)) →
      ∀ (τ' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (diagUnits2 α β))),
        τ'.IsHaarMeasure →
        AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (diagUnits2 a (a * t)) (diagUnits2 α β) 1 τ τ' →
      ∀ J' I' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.archHaarL K L)
          (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
            -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
              - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                  (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                    AutomorphicForm.archIdentGL K L y)))
          (diagUnits2 α β) τ' (φa ∘ AutomorphicForm.archIdentGL K L) J' →
        AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (AutomorphicForm.archHaarL K L)
          (diagUnits2 α β) τ' (φa ∘ AutomorphicForm.archIdentGL K L) I' →
        I' = (c : ℂ) * ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] ∂lam ∂(θ.prod θ) ∧
        J' = (c : ℂ) * ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * ((omega K L y : ℝ) : ℂ) ∂lam ∂(θ.prod θ) := by
  classical
  obtain ⟨ρ, hρ, hpin⟩ :=
    AutomorphicForm.exists_isHaarMeasure_forall_integral_centralizer_diagUnits2_eq_integral_prod_of_map_eq K τ₀
  haveI := hρ
  obtain ⟨c, hc, hA3⟩ :=
    AutomorphicForm.exists_pos_forall_twistedOrbital_archHaarL_diagUnits2_eq_mul_integral_ker_norm_integral_integral_and_twistedWeighted_eq_of_coupled K L σ hgen hdeg ρ lam θ κ hκ
  obtain ⟨Φ, hΦs, hΦc, hΦu, hΦ⟩ :=
    AutomorphicForm.exists_contDiff_hasCompactSupport_forall_integral_twistedConj_diagUnits2_mul_unipotentGL2_eq K L σ hgen hdeg φa hφa κ hκ
  refine ⟨c, hc, Φ, hΦs, hΦc, hΦu, ?_⟩
  intro a t hreg τ hτ hmap α β hαβ τ' hτ' hcpl J' I' hJ hI
  have hsch := hpin a (a * t) hreg τ hτ hmap
  obtain ⟨hI', hJ'⟩ := hA3 φa hφa (omega K L) (continuous_omega K L) _ (continuous_weight K L)
    (weight_iwasawa K L) a t hreg τ hsch α β hαβ τ' hτ' hcpl
  have eI := hI' I' hI
  have eJ := hJ' J' hJ
  simp_rw [hΦ] at eI eJ
  exact ⟨eI, eJ⟩

theorem unweighted_normalisation (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) [θ.IsHaarMeasure]
    (Φ : (Fin 3 → NumberField.mixedEmbedding.mixedSpace L) → ℂ)
    (a t : (InfiniteAdeleRing K)ˣ) (ht : ∀ v : NumberField.InfinitePlace K, (t : InfiniteAdeleRing K) v ≠ 1)
    (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    (h : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t))) :
    ((∏ w : NumberField.InfinitePlace K, ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ w.mult : ℝ) : ℂ) *
        ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] ∂lam ∂(θ.prod θ) =
      ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] ∂lam ∂(θ.prod θ) := by
  classical

  have hunit : IsUnit ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K)) := by
    refine Pi.isUnit_iff.mpr fun v => isUnit_iff_ne_zero.mpr ?_
    show (1 : v.Completion) - (t : InfiniteAdeleRing K) v ≠ 0
    exact sub_ne_zero.mpr (ht v).symm
  set P : ℝ := ∏ w : NumberField.InfinitePlace K,
      ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ w.mult with hP
  have hPpos : 0 < P := by
    rw [hP]
    refine Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr ?_) _
    exact ((Pi.isUnit_iff.mp hunit) w).ne_zero
  have hfib : ∀ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
      ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] ∂lam = ((P⁻¹ : ℝ) : ℂ) * ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] ∂lam := by
    intro u
    have hN := norm_of_normString_eq K L σ hgen a t α β h u
    have hab : IsUnit (Algebra.norm (InfiniteAdeleRing K) (1 : (L ⊗[K] InfiniteAdeleRing K)) - Algebra.norm (InfiniteAdeleRing K) (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) := by
      rw [hN]; exact hunit
    have h2 := (AutomorphicForm.map_mul_sigmaTensor_sub_mul_addHaar_infiniteAdeleRing_eq_inv_prod_norm_archEval_algebraNorm_sub_pow_mult_smul K L σ hgen hdeg lam (1 : (L ⊗[K] InfiniteAdeleRing K)) (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) hab).2
      (fun z => Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L z)])
    simp only [one_mul] at h2
    rw [h2, hN, hP]
  simp_rw [hfib]
  rw [integral_const_mul, ← mul_assoc]
  have : ((P : ℝ) : ℂ) * ((P⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ hPpos.ne', Complex.ofReal_one]
  rw [this, one_mul]

def kink (w : InfinitePlace K) (t : (InfiniteAdeleRing K)ˣ) : ℝ :=
  if w.IsReal then ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖
  else ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖

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

theorem per_place (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) [θ.IsHaarMeasure]
    (Φ : (Fin 3 → NumberField.mixedEmbedding.mixedSpace L) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hΦc : HasCompactSupport Φ)
    (hΦu : ∃ C : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ), IsCompact C ∧
        ∀ p ∈ tsupport Φ, ∃ q ∈ C,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))))
    (w : NumberField.InfinitePlace K) :
    ∃ A B : (Fin 2 → NumberField.mixedEmbedding.mixedSpace K) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) A ∧ ContDiff ℝ (⊤ : ℕ∞) B ∧ HasCompactSupport A ∧ HasCompactSupport B ∧
      (∃ Ca : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ), IsCompact Ca ∧
        ∀ p ∈ tsupport A ∪ tsupport B, ∃ q ∈ Ca,
          p = ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
                NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ), (∀ v : NumberField.InfinitePlace K, (t : InfiniteAdeleRing K) v ≠ 1) →
      ∀ (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ),
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)) →
        (∀ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
            Integrable (fun y : (L ⊗[K] InfiniteAdeleRing K) => Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * ((omegaPlace K L w y : ℝ) : ℂ)) lam) ∧
        Integrable (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker =>
            ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * ((omegaPlace K L w y : ℝ) : ℂ) ∂lam) (θ.prod θ) ∧
        (∀ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker, Integrable (fun y : (L ⊗[K] InfiniteAdeleRing K) => Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)]) lam) ∧
        Integrable (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker => ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] ∂lam) (θ.prod θ) ∧
        ((∏ v : NumberField.InfinitePlace K,
            ‖NumberField.AdelicLevel.archEval K v ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ v.mult : ℝ) : ℂ) *
          ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * ((omegaPlace K L w y : ℝ) : ℂ) ∂lam ∂(θ.prod θ) =
        -2 * (Module.finrank K L : ℂ) * (((w.mult : ℝ) * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
            ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] ∂lam ∂(θ.prod θ) +
          A ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] +
          ((kink K w t : ℝ) : ℂ) * B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by
  by_cases hw : w.IsReal
  · obtain ⟨A, B, h1, h2, h3, h4, h5, h6⟩ :=
      AutomorphicForm.exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_mul_of_isReal
        K L σ hgen hdeg lam θ Φ hΦ hΦc hΦu w hw
    refine ⟨A, B, h1, h2, h3, h4, h5, fun a t ht α β hαβ => ?_⟩
    obtain ⟨i1, i2, i3, i4, i5⟩ := h6 a t ht α β hαβ
    refine ⟨i1, i2, i3, i4, ?_⟩
    unfold omegaPlace
    rw [i5]
    unfold kink
    rw [if_pos hw]
  · have hw' : w.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw
    obtain ⟨A, B, h1, h2, h3, h4, h5, h6⟩ :=
      AutomorphicForm.exists_contDiff_hasCompactSupport_prod_norm_pow_mul_integral_ker_norm_integral_twistedLogWeight_eq_add_norm_sq_mul_log_mul_of_isComplex
        K L σ hgen hdeg lam θ Φ hΦ hΦc hΦu w hw'
    refine ⟨A, B, h1, h2, h3, h4, h5, fun a t ht α β hαβ => ?_⟩
    obtain ⟨i1, i2, i3, i4, i5⟩ := h6 a t ht α β hαβ
    refine ⟨i1, i2, i3, i4, ?_⟩
    unfold omegaPlace
    rw [i5]
    unfold kink
    rw [if_neg hw]

end DiscL
p2m_reactivate "P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_twistedWeighted_eq_neg_two_mul_finrank_mul_sum_log_mul_twistedOrbital_add_sum_real_add_sum_complex.DiscKL"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_twistedWeighted_eq_neg_two_mul_finrank_mul_sum_log_mul_twistedOrbital_add_sum_real_add_sum_complex.DiscKL"

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open scoped Classical in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
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

      (∀ a t : (InfiniteAdeleRing K)ˣ,
        (¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (diagUnits2 a (a * t)) δ) →
          B ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] = 0 ∧
          ∀ w, C w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] = 0 ∧ E w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] = 0) ∧
      ∀ (a t : (InfiniteAdeleRing K)ˣ), AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t)) →
      ∀ (τ : Measure (Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
        τ.IsHaarMeasure →
        Measure.map
            (fun x : Subgroup.centralizer ({diagUnits2 a (a * t)} : Set (GL (Fin 2) (InfiniteAdeleRing K))) =>
              ((((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 0,
                ((x : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 1 1) :
                InfiniteAdeleRing K × InfiniteAdeleRing K))
            τ = τ₀ →
      ∀ α β : (L ⊗[K] InfiniteAdeleRing K)ˣ,
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t)) →
      ∀ (τ' : Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (diagUnits2 α β))),
        τ'.IsHaarMeasure →
        AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (diagUnits2 a (a * t)) (diagUnits2 α β) 1 τ τ' →
      ∀ J' I' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.archHaarL K L)
          (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
            -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
              - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                  (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                    AutomorphicForm.archIdentGL K L y)))
          (diagUnits2 α β) τ' (φa ∘ AutomorphicForm.archIdentGL K L) J' →
        AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (AutomorphicForm.archHaarL K L)
          (diagUnits2 α β) τ' (φa ∘ AutomorphicForm.archIdentGL K L) I' →
        ((∏ w : NumberField.InfinitePlace K,
              (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ /
                  Real.sqrt ‖NumberField.AdelicLevel.archEval K w (t : InfiniteAdeleRing K)‖) ^ w.mult : ℝ) : ℂ) * J' =
          -2 * (Module.finrank K L : ℂ) * ((∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) *
              Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
            (((∏ w : NumberField.InfinitePlace K,
              (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ /
                  Real.sqrt ‖NumberField.AdelicLevel.archEval K w (t : InfiniteAdeleRing K)‖) ^ w.mult : ℝ) : ℂ) * I') +
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
  obtain ⟨mE, bE, lam, hlam, mEu, bEu, θ, hθ, κ, hκ⟩ := DiscL.H0_measures K L
  letI := mE; haveI := bE; haveI := hlam; letI := mEu; haveI := bEu; haveI := hθ
  obtain ⟨c, hc, Φ, hΦs, hΦc, hΦu, hms⟩ :=
    DiscL.measure_side K L σ hgen hdeg φa hφa τ₀ lam θ κ hκ
  have hpl := fun w => DiscL.per_place K L σ hgen hdeg lam θ Φ hΦs hΦc hΦu w
  choose A B hA hB hAc hBc hCaAB hmain using hpl
  obtain ⟨χ, hχs, hχ0, hχ1⟩ := DiscL.exists_normClass_cutoff K L σ hgen hdeg
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

  have hRA_unit : ∀ w, ∀ p ∈ tsupport (fun p => DiscL.Rfac K p * A w p),
      IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ).symm (p 0)) ∧ IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ).symm (p 1)) := fun w p hp => by
    obtain ⟨q, -, hq⟩ := hCaAm w p hp
    subst hq
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, RingEquiv.symm_apply_apply]
    exact ⟨Units.isUnit _, Units.isUnit _⟩
  have hRB_unit : ∀ w, ∀ p ∈ tsupport (fun p => DiscL.Rfac K p * B w p),
      IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ).symm (p 0)) ∧ IsUnit ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K ).symm (p 1)) := fun w p hp => by
    obtain ⟨q, -, hq⟩ := hCaBm w p hp
    subst hq
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, RingEquiv.symm_apply_apply]
    exact ⟨Units.isUnit _, Units.isUnit _⟩
  have hχA : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (fun p => ((χ p : ℝ) : ℂ) * (DiscL.Rfac K p * A w p)) :=
    fun w => hχs _ (hUA w).1 (hUA w).2.1 (hRA_unit w)
  have hχB : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (fun p => ((χ p : ℝ) : ℂ) * (DiscL.Rfac K p * B w p)) :=
    fun w => hχs _ (hUB w).1 (hUB w).2.1 (hRB_unit w)
  refine ⟨fun p => (c : ℂ) * ∑ w : NumberField.InfinitePlace K, ((χ p : ℝ) : ℂ) * (DiscL.Rfac K p * A w p),
          fun w p => (c : ℂ) * (((χ p : ℝ) : ℂ) * (DiscL.Rfac K p * B w p)),
          fun w p => (c : ℂ) * (((χ p : ℝ) : ℂ) * (DiscL.Rfac K p * B w p)),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.mul (ContDiff.sum fun w _ => hχA w)
  · intro w; exact contDiff_const.mul (hχB w)
  · intro w; exact contDiff_const.mul (hχB w)
  · exact (DiscL.hasCompactSupport_finset_sum _ _ fun w _ => (hUA w).2.1.mul_left).mul_left
  · intro w; exact ((hUB w).2.1.mul_left).mul_left
  · intro w; exact ((hUB w).2.1.mul_left).mul_left
  ·
    intro p hp
    rcases hp with h | ⟨w, h | h⟩
    · have h' : ∑ w : NumberField.InfinitePlace K, ((χ p : ℝ) : ℂ) * (DiscL.Rfac K p * A w p) ≠ 0 :=
        fun h0 => h (by beta_reduce; rw [h0, mul_zero])
      obtain ⟨w, -, hw⟩ := Finset.exists_ne_zero_of_sum_ne_zero h'
      have hw' : DiscL.Rfac K p * A w p ≠ 0 := fun h0 => hw (by rw [h0, mul_zero])
      exact hRA_unit w p (subset_tsupport _ hw')
    · have hw' : DiscL.Rfac K p * B w p ≠ 0 := fun h0 => h (by beta_reduce; rw [h0, mul_zero, mul_zero])
      exact hRB_unit w p (subset_tsupport _ hw')
    · have hw' : DiscL.Rfac K p * B w p ≠ 0 := fun h0 => h (by beta_reduce; rw [h0, mul_zero, mul_zero])
      exact hRB_unit w p (subset_tsupport _ hw')
  ·
    refine ⟨⋃ w, (CaA w ∪ CaB w), isCompact_iUnion fun w => (hCaAc w).union (hCaBc w), fun p hp => ?_⟩
    rcases hp with h | h
    · have hex : ∃ w, p ∈ tsupport (fun p => DiscL.Rfac K p * A w p) := by
        by_contra h'
        push Not at h'
        apply DiscL.notMem_tsupport_finset_sum (Finset.univ) (fun w p => ((χ p : ℝ) : ℂ) * (DiscL.Rfac K p * A w p)) p
          (fun w _ hw => h' w (tsupport_mul_subset_right (f := fun p => ((χ p : ℝ) : ℂ)) hw))
        exact tsupport_mul_subset_right (f := fun _ => (c : ℂ)) h
      obtain ⟨w, hw⟩ := hex
      obtain ⟨q, hq, hpq⟩ := hCaAm w p hw
      exact ⟨q, Set.mem_iUnion.mpr ⟨w, Or.inl hq⟩, hpq⟩
    · obtain ⟨w, hw⟩ := Set.mem_iUnion.mp h
      have h1 : p ∈ tsupport (fun p => DiscL.Rfac K p * B w p) := by
        rcases hw with h2 | h2 <;>
          exact tsupport_mul_subset_right (f := fun p => ((χ p : ℝ) : ℂ))
            (tsupport_mul_subset_right (f := fun _ => (c : ℂ)) h2)
      obtain ⟨q, hq, hpq⟩ := hCaBm w p h1
      exact ⟨q, Set.mem_iUnion.mpr ⟨w, Or.inr hq⟩, hpq⟩
  ·
    intro a t hno
    have h0 := hχ0 a t hno
    refine ⟨by beta_reduce; rw [h0]; simp, fun w => ⟨by beta_reduce; rw [h0]; simp, by beta_reduce; rw [h0]; simp⟩⟩
  ·
    intro a t hreg τ hτ hmap α β hαβ τ' hτ' hcpl J' I' hJ hI
    obtain ⟨eI, eJ⟩ := hms a t hreg τ hτ hmap α β hαβ τ' hτ' hcpl J' I' hJ hI
    have ht : ∀ v : NumberField.InfinitePlace K, (t : InfiniteAdeleRing K) v ≠ 1 :=
      DiscL.apply_ne_one_of_isRegularSemisimple K a t hreg
    have h1 := hχ1 a t α β hαβ
    have hint := fun w => hmain w a t ht α β hαβ
    have hU := DiscL.unweighted_normalisation K L σ hgen hdeg lam θ Φ a t ht α β hαβ

    set U : ℂ := ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] ∂lam ∂(θ.prod θ) with hUdef
    set V : ℂ := ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] ∂lam ∂(θ.prod θ) with hVdef
    set Vw : NumberField.InfinitePlace K → ℂ := fun w =>
      ∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * ((DiscL.omegaPlace K L w y : ℝ) : ℂ) ∂lam ∂(θ.prod θ) with hVwdef
    set P : ℝ := ∏ w : NumberField.InfinitePlace K,
      ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ w.mult with hPdef
    set R : ℝ := (∏ w : NumberField.InfinitePlace K, ‖(t : InfiniteAdeleRing K) w‖ ^ w.mult) ^ (-(1 / 2 : ℝ)) with hRdef

    have hWj : (∫ u, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * ((DiscL.omega K L y : ℝ) : ℂ) ∂lam ∂(θ.prod θ)) =
        ∑ w : NumberField.InfinitePlace K, Vw w := by
      have hin : ∀ u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker,
          (∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * ((DiscL.omega K L y : ℝ) : ℂ) ∂lam) =
            ∑ w : NumberField.InfinitePlace K, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * ((DiscL.omegaPlace K L w y : ℝ) : ℂ) ∂lam := by
        intro u
        rw [← integral_finsetSum _ (fun w _ => (hint w).1 u)]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        beta_reduce
        rw [DiscL.omega_eq_sum_omegaPlace, Complex.ofReal_sum, Finset.mul_sum]
      rw [show (fun u : ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker × ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) : (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker => ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * ((DiscL.omega K L y : ℝ) : ℂ) ∂lam) =
          fun u => ∑ w : NumberField.InfinitePlace K, ∫ y, Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))),
                 NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - (((α * (u.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (u.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)) * y))] * ((DiscL.omegaPlace K L w y : ℝ) : ℂ) ∂lam
          from funext hin]
      rw [integral_finsetSum _ (fun w _ => (hint w).2.1)]

    have hsum : ((P : ℝ) : ℂ) * ∑ w : NumberField.InfinitePlace K, Vw w =
        ∑ w : NumberField.InfinitePlace K,
          (-2 * (Module.finrank K L : ℂ) * (((w.mult : ℝ) * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) * U +
            A w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] + ((DiscL.kink K w t : ℝ) : ℂ) * B w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)]) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      exact (hint w).2.2.2.2
    rw [hWj] at eJ

    have hν := DiscL.nu_eq K t
    have hRv := DiscL.Rfac_vec K t a
    beta_reduce
    rw [hν, h1]
    simp only [hRv, Complex.ofReal_one, one_mul]
    rw [← hPdef, ← hRdef]

    have hsplit :
        (∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal),
            ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
              ((c : ℂ) * (((R : ℝ) : ℂ) * B w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)]))) +
          ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex),
            ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ ^ 2 *
                Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) *
              ((c : ℂ) * (((R : ℝ) : ℂ) * B w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)])) =
        (c : ℂ) * ((R : ℝ) : ℂ) *
          ∑ w : NumberField.InfinitePlace K, ((DiscL.kink K w t : ℝ) : ℂ) * B w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by
      rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun w : NumberField.InfinitePlace K => w.IsReal)]
      congr 1
      · refine Finset.sum_congr rfl fun w hw => ?_
        rw [Finset.mem_filter] at hw
        unfold DiscL.kink; rw [if_pos hw.2]; ring
      · refine Finset.sum_congr (Finset.filter_congr fun w _ => ?_) fun w hw => ?_
        · exact (NumberField.InfinitePlace.not_isReal_iff_isComplex).symm
        · rw [Finset.mem_filter] at hw
          unfold DiscL.kink; rw [if_neg hw.2]; push_cast; ring
    rw [add_assoc, hsplit]

    have hSA : (∑ w : NumberField.InfinitePlace K, ((R : ℝ) : ℂ) * A w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)]) =
        ((R : ℝ) : ℂ) * ∑ w : NumberField.InfinitePlace K, A w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by rw [Finset.mul_sum]
    have hS3 : (∑ w : NumberField.InfinitePlace K,
          (-2 * (Module.finrank K L : ℂ) * (((w.mult : ℝ) * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) * U +
            A w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] + ((DiscL.kink K w t : ℝ) : ℂ) * B w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)])) =
        -2 * (Module.finrank K L : ℂ) * ((∑ w : NumberField.InfinitePlace K, (w.mult : ℝ) * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ) * U +
          (∑ w : NumberField.InfinitePlace K, A w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)]) +
          ∑ w : NumberField.InfinitePlace K, ((DiscL.kink K w t : ℝ) : ℂ) * B w ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (t : InfiniteAdeleRing K), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace K (a : InfiniteAdeleRing K)] := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
    rw [hS3] at hsum
    rw [hSA, eJ, eI]
    push_cast at hsum hU ⊢
    clear hms hmain hint hχs hχ0 hχ1 hCaAB hCaA hCaB hUA hUB hCaAm hCaBm hRA_unit hRB_unit hχA hχB hJ hI hcpl hWj hsplit hSA hS3 hΦu
    linear_combination (((R : ℝ) : ℂ) * (c : ℂ)) * hsum +
      (2 * (Module.finrank K L : ℂ) * (∑ w : NumberField.InfinitePlace K, ((w.mult : ℝ) : ℂ) *
          ((Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (t : InfiniteAdeleRing K))‖ : ℝ) : ℂ)) *
        ((R : ℝ) : ℂ) * (c : ℂ)) * hU

end S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_twistedWeighted_eq_neg_two_mul_finrank_mul_sum_log_mul_twistedOrbital_add_sum_real_add_sum_complex
end P2MW
export P2MW.S_AutomorphicForm_exists_contDiff_hasCompactSupport_tsupport_subset_archDisc_mul_twistedWeighted_eq_neg_two_mul_finrank_mul_sum_log_mul_twistedOrbital_add_sum_real_add_sum_complex (solution)
