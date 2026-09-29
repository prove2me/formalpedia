-- Prove2me | solution 1 for AutomorphicForm.exists_pos_forall_prod_norm_sub_one_pow_mul_eq_mul_prod_norm_pow_mul_integral_integral_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b539a88e-1098-57a6-9bdd-6124e4ae79c7

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_lintegral_generalLinearGroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2_rowIsometry
import Theorems.Thm_NumberField_InfiniteAdeleRing_exists_mem_borelSubgroup_mul_eq_and_isCompact_iInf_rowIsometrySubgroup
import Theorems.Thm_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_pos_forall_prod_norm_sub_one_pow_mul_eq_mul_prod_norm_pow_mul_integral_integral_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply"
p2m_attr_erase "simp" "LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option synthInstance.maxSize 8192

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped ENNReal

attribute [local instance] AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace HCDescentArch

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

theorem continuous_unipotentGL2 :
    Continuous (fun y : InfiniteAdeleRing K => (unipotentGL2 y : GL (Fin 2) (InfiniteAdeleRing K))) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Function.comp_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have : ∀ y : InfiniteAdeleRing K, (↑((unipotentGL2 y : GL (Fin 2) (InfiniteAdeleRing K))⁻¹) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) = !![1, -y; 0, 1] := fun y => rfl
    simp_rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem continuous_scalar :
    Continuous (Matrix.GeneralLinearGroup.scalar (Fin 2) : (InfiniteAdeleRing K)ˣ → GL (Fin 2) (InfiniteAdeleRing K)) := by
  have hval : Continuous fun u : (InfiniteAdeleRing K)ˣ =>
      ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) (InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := by
    change Continuous fun u : (InfiniteAdeleRing K)ˣ => Matrix.scalar (Fin 2) (u : InfiniteAdeleRing K)
    simp_rw [Matrix.scalar_apply]
    exact (continuous_pi fun _ => Units.continuous_val).matrix_diagonal
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp_rw [← map_inv]
  exact hval.comp continuous_inv

theorem diagUnits2_val (a b : (InfiniteAdeleRing K)ˣ) :
    ((diagUnits2 a b : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) =
      Matrix.diagonal ![(a : InfiniteAdeleRing K), (b : InfiniteAdeleRing K)] := by
  rw [LanglandsTunnell.CubicInduction.coe_diagUnits2]
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem diagUnits2_val' (a b : (InfiniteAdeleRing K)ˣ) :
    ((diagUnits2 a b : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) =
      !![(a : InfiniteAdeleRing K), 0; 0, (b : InfiniteAdeleRing K)] := by
  rw [diagUnits2_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem continuous_diagUnits2 :
    Continuous (fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => (diagUnits2 p.1 p.2 : GL (Fin 2) (InfiniteAdeleRing K))) := by
  have hval : Continuous fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
      ((diagUnits2 p.1 p.2 : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) := by
    simp_rw [diagUnits2_val]
    refine (continuous_pi fun i => ?_).matrix_diagonal
    fin_cases i
    · exact Units.continuous_val.comp continuous_fst
    · exact Units.continuous_val.comp continuous_snd
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  have : ∀ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
      (diagUnits2 p.1 p.2 : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ = diagUnits2 p⁻¹.1 p⁻¹.2 := by
    intro p
    rw [inv_eq_iff_mul_eq_one]
    apply Units.ext
    rw [Units.val_mul, diagUnits2_val, diagUnits2_val, Matrix.diagonal_mul_diagonal, Units.val_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  simp_rw [this]
  exact hval.comp continuous_inv

theorem scalar_mul_diagUnits2 (a t : (InfiniteAdeleRing K)ˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2) a * diagUnits2 t 1 = (diagUnits2 (a * t) a : GL (Fin 2) (InfiniteAdeleRing K)) := by
  apply Units.ext
  rw [Units.val_mul, diagUnits2_val, diagUnits2_val]
  change Matrix.scalar (Fin 2) (a : InfiniteAdeleRing K) * _ = _
  rw [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem diagUnits2_mul (a b c d : (InfiniteAdeleRing K)ˣ) :
    (diagUnits2 a b * diagUnits2 c d : GL (Fin 2) (InfiniteAdeleRing K)) = diagUnits2 (a * c) (b * d) := by
  apply Units.ext
  rw [Units.val_mul, diagUnits2_val, diagUnits2_val, diagUnits2_val, Matrix.diagonal_mul_diagonal]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem diagUnits2_comm (a b c d : (InfiniteAdeleRing K)ˣ) :
    (diagUnits2 a b * diagUnits2 c d : GL (Fin 2) (InfiniteAdeleRing K)) = diagUnits2 c d * diagUnits2 a b := by
  rw [diagUnits2_mul, diagUnits2_mul, mul_comm a c, mul_comm b d]

theorem unipotentGL2_inv (x : InfiniteAdeleRing K) :
    (unipotentGL2 x : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ = unipotentGL2 (-x) := by
  rw [inv_eq_iff_mul_eq_one]
  apply Units.ext
  rw [Units.val_mul, unipotentGL2_coe, unipotentGL2_coe, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_conj (u z : (InfiniteAdeleRing K)ˣ) (x : InfiniteAdeleRing K) :
    (unipotentGL2 x : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) *
        unipotentGL2 x =
      Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 *
        unipotentGL2 (((1 : InfiniteAdeleRing K) - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) * x) := by
  rw [unipotentGL2_inv, scalar_mul_diagUnits2]
  apply Units.ext
  simp only [Units.val_mul, unipotentGL2_coe, diagUnits2_val']
  have hu : (u : InfiniteAdeleRing K) * ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) = 1 := Units.mul_inv u
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination ((z : InfiniteAdeleRing K) * x) * hu

theorem conj_coords (u z a t : (InfiniteAdeleRing K)ˣ) (x : InfiniteAdeleRing K) (k : GL (Fin 2) (InfiniteAdeleRing K)) :
    (Matrix.GeneralLinearGroup.scalar (Fin 2) a * diagUnits2 t 1 * unipotentGL2 x * k)⁻¹ *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a * diagUnits2 t 1 * unipotentGL2 x * k) =
      k⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 *
        unipotentGL2 (((1 : InfiniteAdeleRing K) - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) * x)) * k := by
  have hcomm : (Matrix.GeneralLinearGroup.scalar (Fin 2) a * diagUnits2 t 1 : GL (Fin 2) (InfiniteAdeleRing K)) *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) =
      (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) * (Matrix.GeneralLinearGroup.scalar (Fin 2) a * diagUnits2 t 1) := by
    rw [scalar_mul_diagUnits2, scalar_mul_diagUnits2, diagUnits2_comm]
  rw [← unipotent_conj]
  simp only [mul_inv_rev]

  have key : ((diagUnits2 t 1 : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) a)⁻¹ *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) *
      (Matrix.GeneralLinearGroup.scalar (Fin 2) a * diagUnits2 t 1)) = Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 := by
    rw [← mul_inv_rev, mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  calc _ = k⁻¹ * (unipotentGL2 x)⁻¹ * (((diagUnits2 t 1 : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a)⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) a * diagUnits2 t 1))) * unipotentGL2 x * k := by
          simp only [mul_assoc]
    _ = _ := by rw [key]; simp only [mul_assoc]

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion in
theorem continuous_ringEquiv_mixedSpace : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  refine continuous_prodMk.2 ⟨continuous_pi fun v => ?_, continuous_pi fun v => ?_⟩
  · exact (isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem continuous_archEntries : Continuous (archEntries K : GL (Fin 2) (InfiniteAdeleRing K) → _) :=
  continuous_pi fun i => continuous_pi fun j =>
    (continuous_ringEquiv_mixedSpace K).comp (Units.continuous_val.matrix_elem i j)

namespace IsArchTestFactor
open scoped Classical in
private theorem _root_.HCDescentArch.IsArchTestFactor.continuous {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} (h : IsArchTestFactor K fa) :
    Continuous fa := by
  obtain ⟨⟨Φ, hΦ, hfa⟩, -⟩ := h
  have : fa = Φ ∘ archEntries K := funext hfa
  rw [this]
  exact hΦ.continuous.comp (continuous_archEntries K)

end IsArchTestFactor
p2m_export "HCDescentArch" "IsArchTestFactor.continuous"

def Psi (p : ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) × (InfiniteAdeleRing K × Kc K)) :
    GL (Fin 2) (InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) p.1.1 * diagUnits2 p.1.2 1 * unipotentGL2 p.2.1 *
    (p.2.2 : GL (Fin 2) (InfiniteAdeleRing K))

theorem continuous_Psi : Continuous (Psi K) := by
  unfold Psi
  refine ((((continuous_scalar K).comp (continuous_fst.comp continuous_fst)).mul ?_).mul
    ((continuous_unipotentGL2 K).comp (continuous_fst.comp continuous_snd))).mul
    (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  exact (continuous_diagUnits2 K).comp ((continuous_snd.comp continuous_fst).prodMk continuous_const)

section Main

variable [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
  (lam : Measure (InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
  [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
  (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
  (κ : Measure (Kc K)) [κ.IsHaarMeasure]
  (ν : Measure (GL (Fin 2) (InfiniteAdeleRing K))) [ν.IsHaarMeasure]

scoped instance sigmaFinite_lam' : SigmaFinite lam := by infer_instance
scoped instance sigmaFinite_ρ' : SigmaFinite ρ := by infer_instance
scoped instance isFiniteMeasure_κ : IsFiniteMeasure κ := by infer_instance

def piM : Measure (((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) × (InfiniteAdeleRing K × Kc K)) :=
  (ρ.prod ρ).prod (lam.prod κ)

scoped instance sigmaFinite_κ : SigmaFinite κ := @IsFiniteMeasure.toSigmaFinite _ _ κ (isFiniteMeasure_κ K κ)
scoped instance sFinite_κ : SFinite κ := @instSFiniteOfSigmaFinite _ _ κ (sigmaFinite_κ K κ)
scoped instance sFinite_lam : SFinite lam := inferInstance
scoped instance sFinite_ρ : SFinite ρ := inferInstance
scoped instance sFinite_ρρ : SFinite (ρ.prod ρ) := Measure.prod.instSFinite
scoped instance sFinite_lamκ : SFinite (lam.prod κ) := inferInstance
scoped instance sFinite_piM' : SFinite ((ρ.prod ρ).prod (lam.prod κ)) := inferInstance
scoped instance sFinite_piM : SFinite (piM K lam ρ κ) := sFinite_piM' K lam ρ κ

theorem exists_eq_smul_map :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ν = c • (piM K lam ρ κ).map (Psi K) := by
  obtain ⟨c, hc0, hct, h⟩ :=
    NumberField.InfiniteAdeleRing.exists_lintegral_generalLinearGroup_eq_mul_lintegral_scalar_diagUnits2_unipotentGL2_rowIsometry
      K ν ‹_› lam ρ κ ‹_›
  refine ⟨c, hc0, hct, Measure.ext fun S hS => ?_⟩
  have hmS : Measurable (S.indicator (1 : GL (Fin 2) (InfiniteAdeleRing K) → ℝ≥0∞)) := measurable_one.indicator hS
  have hmSP : Measurable (fun p => S.indicator (1 : GL (Fin 2) (InfiniteAdeleRing K) → ℝ≥0∞) (Psi K p)) :=
    hmS.comp (continuous_Psi K).measurable
  rw [Measure.smul_apply, Measure.map_apply (continuous_Psi K).measurable hS, smul_eq_mul, ← lintegral_indicator_one hS,
    h _ hmS, ← lintegral_indicator_one (hS.preimage (continuous_Psi K).measurable)]
  congr 1
  have hind : ∀ p : (((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) × (InfiniteAdeleRing K × Kc K)), ((Psi K) ⁻¹' S).indicator (1 : (((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) × (InfiniteAdeleRing K × Kc K)) → ℝ≥0∞) p = S.indicator 1 (Psi K p) := by
    intro p
    by_cases hp : Psi K p ∈ S
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (Set.mem_preimage.mpr hp)]; rfl
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (fun h => hp (Set.mem_preimage.mp h))]
  simp_rw [hind]
  rw [piM, lintegral_prod _ hmSP.aemeasurable]
  have h1 : ∀ r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
      Measurable (fun q : InfiniteAdeleRing K × Kc K => S.indicator (1 : GL (Fin 2) (InfiniteAdeleRing K) → ℝ≥0∞) (Psi K (r, q))) := fun r =>
    hmSP.comp measurable_prodMk_left
  have h2 : Measurable (fun r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
      ∫⁻ q, S.indicator (1 : GL (Fin 2) (InfiniteAdeleRing K) → ℝ≥0∞) (Psi K (r, q)) ∂(lam.prod κ)) := hmSP.lintegral_prod_right'
  rw [lintegral_prod _ h2.aemeasurable]
  refine lintegral_congr fun a => lintegral_congr fun t => ?_
  rw [lintegral_prod _ (h1 (a, t)).aemeasurable]
  rfl

theorem measurePreserving_torus :
    MeasurePreserving (fun r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => (r.1 * r.2, r.1)) (ρ.prod ρ) (ρ.prod ρ) := by
  have h1 : MeasurePreserving (fun r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => (r.1, r.1 * r.2)) (ρ.prod ρ) (ρ.prod ρ) :=
    (MeasurePreserving.id ρ).skew_product (g := fun a t => a * t) measurable_mul
      (Filter.Eventually.of_forall fun a => map_mul_left_eq_self ρ a)
  have h2 : (fun r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => (r.1 * r.2, r.1)) =
      Prod.swap ∘ (fun r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => (r.1, r.1 * r.2)) := rfl
  rw [h2]
  exact (Measure.measurePreserving_swap).comp h1

theorem Psi_eq (r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) (q : InfiniteAdeleRing K × Kc K) :
    Psi K (r, q) = diagUnits2 (r.1 * r.2) r.1 * (unipotentGL2 q.1 * (q.2 : GL (Fin 2) (InfiniteAdeleRing K))) := by
  rw [Psi, scalar_mul_diagUnits2, mul_assoc]

theorem blocks123_core
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : IsArchTestFactor K fa)
    (u z : (InfiniteAdeleRing K)ˣ) (hu : ∀ w : InfinitePlace K, (u : InfiniteAdeleRing K) w ≠ 1)
    (τ : Measure (Subgroup.centralizer
      ({Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1} : Set (GL (Fin 2) (InfiniteAdeleRing K)))))
    (hτ : ∀ g : GL (Fin 2) (InfiniteAdeleRing K) → ℂ,
      ∫ t, g (t : GL (Fin 2) (InfiniteAdeleRing K)) ∂τ =
        ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, g (diagUnits2 p.1 p.2) ∂(ρ.prod ρ))
    (w : GL (Fin 2) (InfiniteAdeleRing K) → ℝ)
    (hw : IsSectionFnOn (InfiniteAdeleRing K) (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) τ fa w)
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞) (hν : ν = c • (piM K lam ρ κ).map (Psi K)) :
    ∫ g, fa (g⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) * g) * (w g : ℂ) ∂ν =
      (c.toReal : ℂ) * ∫ x, ∫ k, fa ((k : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ *
          (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 *
            unipotentGL2 (((1 : InfiniteAdeleRing K) - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) * x)) *
          (k : GL (Fin 2) (InfiniteAdeleRing K))) ∂κ ∂lam := by
  obtain ⟨hw0, hwm, hwc, hsec⟩ := hw
  set γ : GL (Fin 2) (InfiniteAdeleRing K) := Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 with hγ
  set a : InfiniteAdeleRing K := (1 : InfiniteAdeleRing K) - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) with ha
  have hfac : Continuous fa := IsArchTestFactor.continuous K hfa

  set Fq : InfiniteAdeleRing K × Kc K → ℂ := fun q =>
    fa ((q.2 : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ * (γ * unipotentGL2 (a * q.1)) * (q.2 : GL (Fin 2) (InfiniteAdeleRing K)))
    with hFq
  have hFq_cont : Continuous Fq := by
    rw [hFq]
    refine hfac.comp ?_
    exact ((continuous_subtype_val.comp continuous_snd).inv.mul
      (continuous_const.mul ((continuous_unipotentGL2 K).comp (continuous_const.mul continuous_fst)))).mul
      (continuous_subtype_val.comp continuous_snd)

  set Φ : GL (Fin 2) (InfiniteAdeleRing K) → ℂ := fun g => fa (g⁻¹ * γ * g) * (w g : ℂ) with hΦ
  have hΦm : Measurable Φ := by
    rw [hΦ]
    exact (hfac.comp ((continuous_inv.mul continuous_const).mul continuous_id)).measurable.mul
      (Complex.continuous_ofReal.measurable.comp hwm)
  have hΦPsi : ∀ (r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) (q : InfiniteAdeleRing K × Kc K),
      Φ (Psi K (r, q)) = Fq q * (w (Psi K (r, q)) : ℂ) := by
    intro r q
    simp only [hΦ, hFq, Psi, hγ]
    rw [conj_coords]

  have hwmeas : ∀ q : InfiniteAdeleRing K × Kc K, Measurable (fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
      w (diagUnits2 p.1 p.2 * (unipotentGL2 q.1 * (q.2 : GL (Fin 2) (InfiniteAdeleRing K))))) := fun q =>
    hwm.comp ((continuous_diagUnits2 K).mul continuous_const).measurable
  have htorusC : ∀ q : InfiniteAdeleRing K × Kc K, Fq q ≠ 0 →
      ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
        (w (diagUnits2 p.1 p.2 * (unipotentGL2 q.1 * (q.2 : GL (Fin 2) (InfiniteAdeleRing K)))) : ℂ) ∂(ρ.prod ρ) = 1 := by
    intro q hq
    set m : GL (Fin 2) (InfiniteAdeleRing K) := unipotentGL2 q.1 * (q.2 : GL (Fin 2) (InfiniteAdeleRing K)) with hm
    have hne : fa (m⁻¹ * γ * m) ≠ 0 := by
      have : m⁻¹ * γ * m = (q.2 : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ * (γ * unipotentGL2 (a * q.1)) *
          (q.2 : GL (Fin 2) (InfiniteAdeleRing K)) := by
        rw [hm, mul_inv_rev, hγ, ha, ← unipotent_conj]
        simp only [mul_assoc]
      rw [this]; exact hq
    have h1 := hsec m hne
    rw [← hτ (fun y => (w (y * m) : ℂ)), integral_complex_ofReal, h1, Complex.ofReal_one]
  have htorusR : ∀ q : InfiniteAdeleRing K × Kc K, Fq q ≠ 0 →
      ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
        w (diagUnits2 p.1 p.2 * (unipotentGL2 q.1 * (q.2 : GL (Fin 2) (InfiniteAdeleRing K)))) ∂(ρ.prod ρ) = 1 := by
    intro q hq
    have := htorusC q hq
    rw [integral_complex_ofReal] at this
    exact_mod_cast this

  have hchange : ∀ (q : InfiniteAdeleRing K × Kc K) (G : GL (Fin 2) (InfiniteAdeleRing K) → ℂ), Measurable G →
      ∫ r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, G (Psi K (r, q)) ∂(ρ.prod ρ) =
        ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
          G (diagUnits2 p.1 p.2 * (unipotentGL2 q.1 * (q.2 : GL (Fin 2) (InfiniteAdeleRing K)))) ∂(ρ.prod ρ) := by
    intro q G hG
    have hG' : AEStronglyMeasurable (fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
        G (diagUnits2 p.1 p.2 * (unipotentGL2 q.1 * (q.2 : GL (Fin 2) (InfiniteAdeleRing K))))) (ρ.prod ρ) :=
      (hG.comp ((continuous_diagUnits2 K).mul continuous_const).measurable).aestronglyMeasurable
    have hT := measurePreserving_torus K ρ
    have hG'' : AEStronglyMeasurable (fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
        G (diagUnits2 p.1 p.2 * (unipotentGL2 q.1 * (q.2 : GL (Fin 2) (InfiniteAdeleRing K)))))
        (Measure.map (fun r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => (r.1 * r.2, r.1)) (ρ.prod ρ)) := by
      rw [hT.map_eq]; exact hG'
    calc ∫ r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, G (Psi K (r, q)) ∂(ρ.prod ρ)
        = ∫ r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, (fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
            G (diagUnits2 p.1 p.2 * (unipotentGL2 q.1 * (q.2 : GL (Fin 2) (InfiniteAdeleRing K))))) (r.1 * r.2, r.1) ∂(ρ.prod ρ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
          simp only [Psi_eq]
      _ = ∫ p, G (diagUnits2 p.1 p.2 * (unipotentGL2 q.1 * (q.2 : GL (Fin 2) (InfiniteAdeleRing K))))
            ∂(Measure.map (fun r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => (r.1 * r.2, r.1)) (ρ.prod ρ)) :=
          (integral_map hT.measurable.aemeasurable hG'').symm
      _ = _ := by rw [hT.map_eq]

  have ha_ne : ∀ wp : InfinitePlace K, a wp ≠ 0 := by
    intro wp h0
    have hmul : ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) wp * (u : InfiniteAdeleRing K) wp = 1 := by
      have := congrFun (Units.inv_mul u : ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * u = 1) wp
      exact this
    have h1 : ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) wp = 1 := by
      have : ((1 : InfiniteAdeleRing K) - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) wp = 0 := by rw [← ha]; exact h0
      have e : ((1 : InfiniteAdeleRing K) - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) wp =
          1 - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) wp := rfl
      rw [e, sub_eq_zero] at this
      exact this.symm
    rw [h1, one_mul] at hmul
    exact hu wp hmul
  set aU : (InfiniteAdeleRing K)ˣ := ⟨a, fun wp => (a wp)⁻¹, funext fun wp => mul_inv_cancel₀ (ha_ne wp),
    funext fun wp => inv_mul_cancel₀ (ha_ne wp)⟩ with haU
  have haU_val : (aU : InfiniteAdeleRing K) = a := rfl

  have hFq_supp : HasCompactSupport Fq := by
    obtain ⟨-, hfaK⟩ := hfa
    set Kset : Set (GL (Fin 2) (InfiniteAdeleRing K)) := Set.range (Subtype.val : Kc K → GL (Fin 2) (InfiniteAdeleRing K))
    have hKset : IsCompact Kset := isCompact_range continuous_subtype_val
    set S1 : Set (GL (Fin 2) (InfiniteAdeleRing K)) :=
      (fun p : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (InfiniteAdeleRing K) => p.1 * p.2 * p.1⁻¹) '' (Kset ×ˢ tsupport fa)
    have hS1 : IsCompact S1 := (hKset.prod hfaK).image ((continuous_fst.mul continuous_snd).mul continuous_fst.inv)
    set E : Set (InfiniteAdeleRing K) :=
      (fun g : GL (Fin 2) (InfiniteAdeleRing K) => ((γ⁻¹ * g : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1) '' S1
    have hE : IsCompact E := hS1.image ((Units.continuous_val.comp (continuous_const.mul continuous_id)).matrix_elem 0 1)
    set X0 : Set (InfiniteAdeleRing K) := (fun y => ((aU⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * y) '' E
    have hX0 : IsCompact X0 := hE.image (continuous_const.mul continuous_id)
    refine HasCompactSupport.intro (hX0.prod isCompact_univ) fun q hq => ?_
    by_contra hne
    apply hq
    refine ⟨?_, Set.mem_univ _⟩

    have hmem : γ * unipotentGL2 (a * q.1) ∈ S1 := by
      refine ⟨((q.2 : GL (Fin 2) (InfiniteAdeleRing K)),
        (q.2 : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ * (γ * unipotentGL2 (a * q.1)) * (q.2 : GL (Fin 2) (InfiniteAdeleRing K))),
        ⟨⟨q.2, rfl⟩, subset_tsupport _ hne⟩, ?_⟩
      simp only [← mul_assoc, mul_inv_cancel, one_mul, mul_inv_cancel_right]
    have hE' : a * q.1 ∈ E := by
      refine ⟨_, hmem, ?_⟩
      show (((γ⁻¹ * (γ * unipotentGL2 (a * q.1)) : GL (Fin 2) (InfiniteAdeleRing K))) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) 0 1 = a * q.1
      rw [← mul_assoc, inv_mul_cancel, one_mul, unipotentGL2_coe]
      simp
    refine ⟨a * q.1, hE', ?_⟩
    show ((aU⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) * (a * q.1) = q.1
    rw [← haU_val, ← mul_assoc, Units.inv_mul, one_mul]
  have hFq_int : Integrable Fq (lam.prod κ) := hFq_cont.integrable_of_hasCompactSupport hFq_supp

  have hΦPsi_m : Measurable (fun p => Φ (Psi K p)) := hΦm.comp (continuous_Psi K).measurable
  have hwPsi_m : Measurable (fun p : ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) × (InfiniteAdeleRing K × Kc K) =>
      ((w (Psi K p) : ℝ) : ℂ)) := Complex.continuous_ofReal.measurable.comp (hwm.comp (continuous_Psi K).measurable)
  have henorm_w : ∀ g : GL (Fin 2) (InfiniteAdeleRing K), ‖((w g : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (w g) := by
    intro g
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hw0 g)]
  have hinnerL : ∀ q : InfiniteAdeleRing K × Kc K, Fq q ≠ 0 →
      ∫⁻ r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, ‖((w (Psi K (r, q)) : ℝ) : ℂ)‖ₑ ∂(ρ.prod ρ) = 1 := by
    intro q hq
    simp_rw [henorm_w, Psi_eq]
    have hT := measurePreserving_torus K ρ
    have hmeasg : Measurable (fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
        ENNReal.ofReal (w (diagUnits2 p.1 p.2 * (unipotentGL2 q.1 * (q.2 : GL (Fin 2) (InfiniteAdeleRing K)))))) :=
      ENNReal.measurable_ofReal.comp (hwmeas q)
    have := hT.lintegral_comp hmeasg
    simp only [Function.comp] at this
    rw [this]
    have hint : Integrable (fun p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
        w (diagUnits2 p.1 p.2 * (unipotentGL2 q.1 * (q.2 : GL (Fin 2) (InfiniteAdeleRing K))))) (ρ.prod ρ) := by
      by_contra h
      have := htorusR q hq
      rw [integral_undef h] at this
      exact zero_ne_one this
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun p => hw0 _), htorusR q hq,
      ENNReal.ofReal_one]
  have hint : Integrable (fun p => Φ (Psi K p)) (piM K lam ρ κ) := by
    refine ⟨hΦPsi_m.aestronglyMeasurable, ?_⟩
    show ∫⁻ p, ‖Φ (Psi K p)‖ₑ ∂(piM K lam ρ κ) < ∞
    rw [piM, lintegral_prod_symm _ hΦPsi_m.enorm.aemeasurable]
    calc ∫⁻ q, ∫⁻ r, ‖Φ (Psi K (r, q))‖ₑ ∂(ρ.prod ρ) ∂(lam.prod κ)
        ≤ ∫⁻ q, ‖Fq q‖ₑ ∂(lam.prod κ) := by
          refine lintegral_mono fun q => ?_
          simp_rw [hΦPsi, enorm_mul]
          have hm : Measurable (fun r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => ‖((w (Psi K (r, q)) : ℝ) : ℂ)‖ₑ) :=
            (hwPsi_m.comp measurable_prodMk_right).enorm
          rw [lintegral_const_mul _ hm]
          by_cases hq : Fq q = 0
          · simp [hq]
          · rw [hinnerL q hq, mul_one]
      _ < ∞ := hFq_int.2

  rw [hν, integral_smul_measure, integral_map (continuous_Psi K).measurable.aemeasurable hΦm.aestronglyMeasurable,
    piM, integral_prod_symm _ (by rw [← piM]; exact hint)]
  have hinner : ∀ q : InfiniteAdeleRing K × Kc K,
      ∫ r : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, Φ (Psi K (r, q)) ∂(ρ.prod ρ) = Fq q := by
    intro q
    simp_rw [hΦPsi]
    rw [integral_const_mul]
    by_cases hq : Fq q = 0
    · rw [hq, zero_mul]
    · rw [hchange q (fun y => ((w y : ℝ) : ℂ)) (Complex.continuous_ofReal.measurable.comp hwm), htorusC q hq, mul_one]
  simp_rw [hinner]
  rw [integral_prod _ hFq_int, Complex.real_smul]

end Main

end HCDescentArch
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_prod_norm_sub_one_pow_mul_eq_mul_prod_norm_pow_mul_integral_integral_of_isOrbitalIntegralOn_scalar_mul_diagUnits2.HCDescentArch"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_prod_norm_sub_one_pow_mul_eq_mul_prod_norm_pow_mul_integral_integral_of_isOrbitalIntegralOn_scalar_mul_diagUnits2.HCDescentArch"

theorem HCDescentArch.blocks123
    (K : Type) [Field K] [NumberField K]
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) ν)
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (lam : Measure (InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    (κ : @Measure (↥(⨅ w : InfinitePlace K,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent K w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing K)))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ), AutomorphicForm.IsArchTestFactor K fa →
      ∀ (u z : (InfiniteAdeleRing K)ˣ), (∀ w : InfinitePlace K, (u : InfiniteAdeleRing K) w ≠ 1) →
        ∀ (τ : Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
          (∀ g : GL (Fin 2) (InfiniteAdeleRing K) → ℂ,
              ∫ t, g (t : GL (Fin 2) (InfiniteAdeleRing K)) ∂τ =
                ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, g (diagUnits2 p.1 p.2) ∂(ρ.prod ρ)) →
          ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν
              (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) τ fa I →
            I = (c : ℂ) * ∫ x, @integral _ ℂ _ _ (borel _) κ (fun k =>
                fa ((k : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ *
                  (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 *
                    AutomorphicForm.unipotentGL2 (((1 : InfiniteAdeleRing K) - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) * x)) *
                  (k : GL (Fin 2) (InfiniteAdeleRing K)))) ∂lam := by
  haveI : ν.IsHaarMeasure := hν
  haveI : κ.IsHaarMeasure := hκ
  obtain ⟨c, hc0, hct, hνeq⟩ := HCDescentArch.exists_eq_smul_map K lam ρ κ ν
  refine ⟨c.toReal, ENNReal.toReal_pos hc0 hct, ?_⟩
  intro fa hfa u z hu τ hτ I hI
  obtain ⟨w, hw, rfl⟩ := hI
  exact HCDescentArch.blocks123_core K lam ρ κ ν fa hfa u z hu τ hτ w hw c hc0 hct hνeq

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped ENNReal
open LanglandsTunnell.CubicInduction (diagUnits2)

namespace HCDescentBlock4

open AutomorphicForm
open scoped Pointwise NNReal

variable (K : Type) [Field K] [NumberField K]

theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ w : InfinitePlace K, SecondCountableTopology w.Completion := fun w =>
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((w : InfinitePlace K) → w.Completion))

theorem integral_comp_mul_left
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (lam : Measure (InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (a : (InfiniteAdeleRing K)ˣ) (H : InfiniteAdeleRing K → ℂ) :
    ∫ x, H ((a : InfiniteAdeleRing K) * x) ∂lam =
      (((distribHaarChar (InfiniteAdeleRing K) a : ℝ))⁻¹ : ℝ) * ∫ x, H x ∂lam := by
  haveI := secondCountableTopology_infiniteAdeleRing K

  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts (InfiniteAdeleRing K)) := inferInstance
  haveI : lam.Regular :=
    Measure.regular_of_isAddLeftInvariant K₀.isCompact K₀.interior_nonempty K₀.isCompact.measure_lt_top.ne

  let e : InfiniteAdeleRing K ≃ᵐ InfiniteAdeleRing K :=
    { toEquiv := Units.mulLeft a
      measurable_toFun := (continuous_const.mul continuous_id).measurable
      measurable_invFun := (continuous_const.mul continuous_id).measurable }
  have he : ∀ x, e x = (a : InfiniteAdeleRing K) * x := fun _ => rfl
  have hmap : Measure.map e lam = (((distribHaarChar (InfiniteAdeleRing K) a)⁻¹ : ℝ≥0) : ℝ≥0∞) • lam := by
    ext s hs
    rw [Measure.map_apply e.measurable hs, Measure.smul_apply]
    have hpre : e ⁻¹' s = a⁻¹ • s := by
      ext x
      simp only [Set.mem_preimage, he, Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
      rfl
    rw [hpre, ← distribHaarChar_mul lam a⁻¹ s, map_inv]
    rfl
  calc ∫ x, H ((a : InfiniteAdeleRing K) * x) ∂lam = ∫ x, H (e x) ∂lam := by simp only [he]
    _ = ∫ y, H y ∂(Measure.map e lam) := (integral_map_equiv e H).symm
    _ = ∫ y, H y ∂((((distribHaarChar (InfiniteAdeleRing K) a)⁻¹ : ℝ≥0) : ℝ≥0∞) • lam) := by rw [hmap]
    _ = (((distribHaarChar (InfiniteAdeleRing K) a : ℝ))⁻¹ : ℝ) * ∫ x, H x ∂lam := by
        rw [integral_smul_measure, ENNReal.coe_toReal, RCLike.real_smul_eq_coe_mul]
        simp

theorem prod_norm_sub_one_pow_eq (u : (InfiniteAdeleRing K)ˣ) :
    (∏ w : InfinitePlace K, ‖(u : InfiniteAdeleRing K) w - 1‖ ^ w.mult) =
      (∏ w : InfinitePlace K, ‖(u : InfiniteAdeleRing K) w‖ ^ w.mult) *
        ∏ w : InfinitePlace K, ‖((1 : InfiniteAdeleRing K) - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) w‖ ^ w.mult := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← mul_pow, ← norm_mul]
  congr 2
  have hu : (u : InfiniteAdeleRing K) w * ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w = 1 := by
    have h := congrArg (fun x : InfiniteAdeleRing K => x w) u.mul_inv
    exact h
  show (u : InfiniteAdeleRing K) w - 1 =
    (u : InfiniteAdeleRing K) w * ((1 : InfiniteAdeleRing K) w - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w)
  have h1 : (1 : InfiniteAdeleRing K) w = 1 := rfl
  rw [mul_sub, h1, mul_one, hu]

end HCDescentBlock4
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_forall_prod_norm_sub_one_pow_mul_eq_mul_prod_norm_pow_mul_integral_integral_of_isOrbitalIntegralOn_scalar_mul_diagUnits2.HCDescentArch"

open scoped NNReal in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) ν)
    [MeasurableSpace (InfiniteAdeleRing K)] [BorelSpace (InfiniteAdeleRing K)]
    (lam : Measure (InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ]
    (ρ : Measure (InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    (κ : @Measure (↥(⨅ w : InfinitePlace K,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent K w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing K)))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ), AutomorphicForm.IsArchTestFactor K fa →
      ∀ (u z : (InfiniteAdeleRing K)ˣ), (∀ w : InfinitePlace K, (u : InfiniteAdeleRing K) w ≠ 1) →
        ∀ (τ : Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1} : Set (GL (Fin 2) (InfiniteAdeleRing K))))),
          (∀ g : GL (Fin 2) (InfiniteAdeleRing K) → ℂ,
              ∫ t, g (t : GL (Fin 2) (InfiniteAdeleRing K)) ∂τ =
                ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ, g (diagUnits2 p.1 p.2) ∂(ρ.prod ρ)) →
          ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν
              (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) τ fa I →
            ((∏ w : InfinitePlace K, ‖(u : InfiniteAdeleRing K) w - 1‖ ^ w.mult : ℝ) : ℂ) * I =
              (c : ℂ) * ((∏ w : InfinitePlace K, ‖(u : InfiniteAdeleRing K) w‖ ^ w.mult : ℝ) : ℂ) *
                ∫ x, @integral _ ℂ _ _ (borel _) κ (fun k =>
                    fa ((k : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ *
                      (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 * AutomorphicForm.unipotentGL2 x) *
                      (k : GL (Fin 2) (InfiniteAdeleRing K)))) ∂lam := by
  haveI := HCDescentBlock4.secondCountableTopology_infiniteAdeleRing K
  obtain ⟨c, hc, hblocks⟩ := HCDescentArch.blocks123 K ν hν lam ρ κ hκ
  refine ⟨c, hc, fun fa hfa u z hu τ hτ I hI => ?_⟩

  have ha : IsUnit ((1 : InfiniteAdeleRing K) - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) := by
    have h := @Pi.isUnit_iff (InfinitePlace K) (fun w => w.Completion) _
      ((1 : InfiniteAdeleRing K) - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K))
    refine h.mpr fun w => isUnit_iff_ne_zero.mpr ?_
    intro h0
    have hu1 : (u : InfiniteAdeleRing K) w * ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w = 1 :=
      congrArg (fun x : InfiniteAdeleRing K => x w) u.mul_inv
    have h0' : ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w = 1 := by
      have := h0
      rw [show ((1 : InfiniteAdeleRing K) - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) w =
        1 - ((u⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) w from rfl] at this
      exact (sub_eq_zero.mp this).symm
    rw [h0', mul_one] at hu1
    exact hu w hu1
  obtain ⟨a, ha'⟩ := ha
  have hI := hblocks fa hfa u z hu τ hτ I hI
  rw [← ha'] at hI
  have h4 := HCDescentBlock4.integral_comp_mul_left K lam a (fun y =>
    @integral _ ℂ _ _ (borel _) κ (fun k =>
      fa ((k : GL (Fin 2) (InfiniteAdeleRing K))⁻¹ *
        (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1 * AutomorphicForm.unipotentGL2 y) *
        (k : GL (Fin 2) (InfiniteAdeleRing K)))))
  beta_reduce at h4
  rw [h4] at hI
  have hmod := NumberField.InfiniteAdeleRing.distribHaarChar_eq_prod_norm_pow_mult K a
  have hnorm := HCDescentBlock4.prod_norm_sub_one_pow_eq K u
  rw [← ha', ← hmod] at hnorm
  have hpos : (0 : ℝ) < (distribHaarChar (InfiniteAdeleRing K) a : ℝ) := NNReal.coe_pos.mpr distribHaarChar_pos
  rw [hI, hnorm]
  have hδ : (((distribHaarChar (InfiniteAdeleRing K) a : ℝ≥0) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  push_cast
  field_simp

end S_AutomorphicForm_exists_pos_forall_prod_norm_sub_one_pow_mul_eq_mul_prod_norm_pow_mul_integral_integral_of_isOrbitalIntegralOn_scalar_mul_diagUnits2
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_forall_prod_norm_sub_one_pow_mul_eq_mul_prod_norm_pow_mul_integral_integral_of_isOrbitalIntegralOn_scalar_mul_diagUnits2 (solution)
