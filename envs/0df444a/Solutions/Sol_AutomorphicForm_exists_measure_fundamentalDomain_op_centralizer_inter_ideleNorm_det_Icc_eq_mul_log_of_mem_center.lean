-- Prove2me | solution 1 for AutomorphicForm.exists_measure_fundamentalDomain_op_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_center
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/c57c1196-0e1d-5a57-91a4-bccb71cfda8f

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Theorems.Thm_NumberField_AdelicHaar_exists_measure_fundamentalDomain_inter_ideleNorm_det_Icc_eq_mul_log
import Theorems.Thm_AutomorphicForm_adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_op_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_center
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar AutomorphicForm
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace P2mCentralCovolK

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem isMulRightInvariant_of_isHaarMeasure (μ : Measure (AdelicGL2 (𝓞 K) K)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, μ = c • adelicGLHaar (Fin 2) (𝓞 K) K :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul μ (adelicGLHaar (Fin 2) (𝓞 K) K)⟩
  rw [hc]
  infer_instance

theorem isHaarMeasure_inv (μ : Measure (AdelicGL2 (𝓞 K) K)) [μ.IsHaarMeasure] : μ.inv.IsHaarMeasure := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI := isMulRightInvariant_of_isHaarMeasure K μ
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts (AdelicGL2 (𝓞 K) K)) := inferInstance
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior μ.inv (K₀ : Set (AdelicGL2 (𝓞 K) K)) K₀.isCompact
    K₀.interior_nonempty ?_ ?_
  · rw [Measure.inv_apply]
    have hsub : (interior (K₀ : Set (AdelicGL2 (𝓞 K) K)))⁻¹ ⊆ (K₀ : Set (AdelicGL2 (𝓞 K) K))⁻¹ :=
      Set.inv_subset_inv.2 interior_subset
    have hpos : 0 < μ (interior (K₀ : Set (AdelicGL2 (𝓞 K) K)))⁻¹ :=
      (isOpen_interior.inv).measure_pos μ (K₀.interior_nonempty.inv)
    exact (hpos.trans_le (measure_mono hsub)).ne'
  · rw [Measure.inv_apply]
    exact K₀.isCompact.inv.measure_lt_top.ne

section Central

variable (γ : (AdelicGL2 (𝓞 K) K)) (hγ : γ ∈ Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 K) K))

include hγ in
theorem mem_centralizer_of_mem_center (g : (AdelicGL2 (𝓞 K) K)) : g ∈ Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K)) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_center_iff.1 hγ g

def centEquiv : Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K)) ≃ₜ* AutomorphicForm.AdelicGL2 (𝓞 K) K where
  toFun t := (t : (AdelicGL2 (𝓞 K) K))
  invFun g := ⟨g, mem_centralizer_of_mem_center K γ hγ g⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk continuous_id _

theorem centEquiv_apply (t : Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K))) : centEquiv K γ hγ t = (t : (AdelicGL2 (𝓞 K) K)) := rfl

theorem centEquiv_symm_apply (g : (AdelicGL2 (𝓞 K) K)) : ((centEquiv K γ hγ).symm g : (AdelicGL2 (𝓞 K) K)) = g := rfl

abbrev ΓZ : Subgroup (Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K))) :=
  ((globalPoints (𝓞 K) K).range).subgroupOf (Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K)))

def eqΓ : (globalPoints (𝓞 K) K).range ≃ (ΓZ K γ).op where
  toFun g := ⟨MulOpposite.op ⟨((g : (AdelicGL2 (𝓞 K) K)))⁻¹, mem_centralizer_of_mem_center K γ hγ _⟩, by
    rw [Subgroup.mem_op, MulOpposite.unop_op, Subgroup.mem_subgroupOf]
    exact Subgroup.inv_mem _ g.2⟩
  invFun x := ⟨(((MulOpposite.unop (x : (Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K)))ᵐᵒᵖ)) :
      Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K))) : (AdelicGL2 (𝓞 K) K))⁻¹, by
    refine Subgroup.inv_mem _ ?_
    have hx := x.2
    rw [Subgroup.mem_op, Subgroup.mem_subgroupOf] at hx
    exact hx⟩
  left_inv g := by
    apply Subtype.ext
    simp only [MulOpposite.unop_op, inv_inv]
  right_inv x := by
    apply Subtype.ext
    apply MulOpposite.unop_injective
    apply Subtype.ext
    simp only [MulOpposite.unop_op, inv_inv]

theorem eqΓ_smul (g : (globalPoints (𝓞 K) K).range) (t : Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K))) :
    ((eqΓ K γ hγ g • t : Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K))) : (AdelicGL2 (𝓞 K) K)) = (t : (AdelicGL2 (𝓞 K) K)) * ((g : (AdelicGL2 (𝓞 K) K)))⁻¹ := by
  rw [Subgroup.smul_def, MulOpposite.smul_eq_mul_unop]
  rfl

end Central

theorem ideleNorm_inv (u : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.TateGlobal.ideleNorm K u⁻¹ = (NumberField.TateGlobal.ideleNorm K u)⁻¹ := by
  simp [NumberField.TateGlobal.ideleNorm, map_inv]

theorem mem_band_inv_iff (g : (AdelicGL2 (𝓞 K) K)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g⁻¹) ∈ Set.Icc b⁻¹ a⁻¹ ↔
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b := by
  rw [map_inv, ideleNorm_inv]
  have hN := NumberField.TateGlobal.ideleNorm_pos (F := K) (Matrix.GeneralLinearGroup.det g)
  have hb : 0 < b := ha.trans_le hab
  rw [Set.mem_Icc, Set.mem_Icc, inv_le_inv₀ hb hN, inv_le_inv₀ hN ha, and_comm]

theorem main (γ : (AdelicGL2 (𝓞 K) K)) (hγ : γ ∈ Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (τ : Measure (Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K)))) [τ.IsHaarMeasure] :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ D : Set (Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K))),
        IsFundamentalDomain (ΓZ K γ).op D τ →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
            (Matrix.GeneralLinearGroup.det (t : (AdelicGL2 (𝓞 K) K))) ∈ Set.Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a)) := by
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K))) := ⟨rfl⟩
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  set e := centEquiv K γ hγ with he

  set μ : Measure (AdelicGL2 (𝓞 K) K) := Measure.map (e : Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K)) → AdelicGL2 (𝓞 K) K) τ with hμ
  haveI : μ.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map τ e
  haveI : μ.IsMulRightInvariant := isMulRightInvariant_of_isHaarMeasure K μ
  set ν : Measure (AdelicGL2 (𝓞 K) K) := μ.inv with hν
  haveI : ν.IsHaarMeasure := isHaarMeasure_inv K μ

  set η : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hη
  haveI : η.IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  obtain ⟨S, hSsub, hSfd⟩ :=
    AutomorphicForm.exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc K 1 2
  set c : ℝ≥0 := ν.haarScalarFactor η with hc
  have hνeq : ν = (c : ℝ≥0∞) • η := by
    have h := Measure.isMulLeftInvariant_eq_smul ν η
    rw [h]
    rfl
  have hSfdν : IsFundamentalDomain
      (Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) :
        Matrix.GeneralLinearGroup (Fin 2) K →* (AdelicGL2 (𝓞 K) K)).range S
      (ν.restrict {g : (AdelicGL2 (𝓞 K) K) | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈
        Set.Icc (1 : ℝ) 2}) := by
    rw [hνeq, Measure.restrict_smul]
    exact hSfd.mono Measure.smul_absolutelyContinuous
  have hfin : ν S ≠ ⊤ := by
    have h1 : η S < ⊤ := by
      have h := AutomorphicForm.adelicGLHaar_inter_setOf_ideleNorm_det_mem_Icc_lt_top_of_isFundamentalDomain
        K 1 2 one_pos one_lt_two S hSfd
      rwa [Set.inter_eq_self_of_subset_left hSsub] at h
    rw [hνeq, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top h1.ne

  obtain ⟨C, hC0, hCt, hleft, -⟩ :=
    NumberField.AdelicHaar.exists_measure_fundamentalDomain_inter_ideleNorm_det_Icc_eq_mul_log
      (Fin 2) K ν 1 2 one_pos one_lt_two S hSsub hSfdν hfin
  refine ⟨C, hC0, hCt, fun D hD a b ha hab => ?_⟩

  set fm : Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K)) ≃ᵐ (AdelicGL2 (𝓞 K) K) :=
    (e.toHomeomorph.trans (Homeomorph.inv (AdelicGL2 (𝓞 K) K))).toMeasurableEquiv with hfm_def
  have hfm : ∀ t : Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K)), fm t = ((t : (AdelicGL2 (𝓞 K) K)))⁻¹ := fun _ => rfl
  have hmap : Measure.map fm τ = ν := by
    have hcomp : (fm : Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K)) → (AdelicGL2 (𝓞 K) K)) =
        (fun g : (AdelicGL2 (𝓞 K) K) => g⁻¹) ∘
          (e : Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K)) → AdelicGL2 (𝓞 K) K) := rfl
    have hem : Measurable (e : Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K)) → AdelicGL2 (𝓞 K) K) :=
      e.continuous.measurable
    rw [hν, Measure.inv_def, hμ, Measure.map_map measurable_inv hem, ← hcomp]
  have hqmp : Measure.QuasiMeasurePreserving fm.symm ν τ := by
    refine ⟨fm.symm.measurable, ?_⟩
    rw [← hmap, MeasurableEquiv.map_symm_map]
  have hFD : IsFundamentalDomain (globalPoints (𝓞 K) K).range (fm '' D) ν := by
    have h := hD.image_of_equiv fm.toEquiv hqmp (eqΓ K γ hγ) (fun g x => ?_)
    · exact h
    · show fm (eqΓ K γ hγ g • x) = g • fm x
      rw [hfm, hfm, eqΓ_smul, Subgroup.smul_def, smul_eq_mul, mul_inv_rev, inv_inv]
  have hb : 0 < b := ha.trans_le hab
  have key := hleft (fm '' D) hFD b⁻¹ a⁻¹ (inv_pos.2 hb) ((inv_le_inv₀ hb ha).2 hab)

  have hset : D ∩ {t : Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K)) | NumberField.TateGlobal.ideleNorm K
      (Matrix.GeneralLinearGroup.det (t : (AdelicGL2 (𝓞 K) K))) ∈ Set.Icc a b} =
      fm ⁻¹' (fm '' D ∩ {g : (AdelicGL2 (𝓞 K) K) | NumberField.TateGlobal.ideleNorm K
        (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc b⁻¹ a⁻¹}) := by
    rw [Set.preimage_inter, fm.injective.preimage_image]
    congr 1
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hfm]
    exact (mem_band_inv_iff K (t : (AdelicGL2 (𝓞 K) K)) ha hab).symm
  calc τ (D ∩ {t : Subgroup.centralizer ({γ} : Set (AdelicGL2 (𝓞 K) K)) | NumberField.TateGlobal.ideleNorm K
          (Matrix.GeneralLinearGroup.det (t : (AdelicGL2 (𝓞 K) K))) ∈ Set.Icc a b})
      = τ (fm ⁻¹' (fm '' D ∩ {g : (AdelicGL2 (𝓞 K) K) | NumberField.TateGlobal.ideleNorm K
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc b⁻¹ a⁻¹})) := by rw [hset]
    _ = Measure.map fm τ (fm '' D ∩ {g : (AdelicGL2 (𝓞 K) K) | NumberField.TateGlobal.ideleNorm K
          (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc b⁻¹ a⁻¹}) :=
        (MeasurableEquiv.map_apply fm _).symm
    _ = C * ENNReal.ofReal (Real.log (a⁻¹ / b⁻¹)) := by rw [hmap]; exact key
    _ = C * ENNReal.ofReal (Real.log (b / a)) := by rw [inv_div_inv]

end P2mCentralCovolK

end

open MeasureTheory NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem solution
    (K : Type) [Field K] [NumberField K]
    (γ : AutomorphicForm.AdelicGL2 (𝓞 K) K)
    (hγ : γ ∈ Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (τ : Measure (Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))))
    [τ.IsHaarMeasure] :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ D : Set (Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
        IsFundamentalDomain
          (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf
            (Subgroup.centralizer ({γ} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))).op D τ →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
            (Matrix.GeneralLinearGroup.det (t : AutomorphicForm.AdelicGL2 (𝓞 K) K)) ∈ Set.Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a)) :=
  P2mCentralCovolK.main K γ hγ τ

end S_AutomorphicForm_exists_measure_fundamentalDomain_op_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_center
end P2MW
export P2MW.S_AutomorphicForm_exists_measure_fundamentalDomain_op_centralizer_inter_ideleNorm_det_Icc_eq_mul_log_of_mem_center (solution)
