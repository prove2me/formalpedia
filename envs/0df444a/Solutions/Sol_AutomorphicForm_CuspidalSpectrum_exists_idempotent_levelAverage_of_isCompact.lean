-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_idempotent_levelAverage_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a24c0ac4-0f20-53df-aeb7-9b24412863b3

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_monoidHom_isCuspLift_rightTranslate_coe_and_norm_eq_and_continuous_of_isCompact
import Theorems.Thm_ContinuousLinearMap_exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous
import Theorems.Thm_ContinuousLinearMap_comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact
import Theorems.Thm_MeasureTheory_exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_idempotent_levelAverage_of_isCompact
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace PFin

variable (F : Type) [Field F] [NumberField F]

theorem commute_of_glArch_eq_one_of_glFin_eq_one {g k : AdelicGL2 (𝓞 F) F}
    (hg : glArch (𝓞 F) F g = 1) (hk : glFin (𝓞 F) F k = 1) : Commute g k := by
  have e : ∀ a b : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F a = glArch (𝓞 F) F b → glFin (𝓞 F) F a = glFin (𝓞 F) F b → a = b := by
    intro a b h1 h2
    refine Units.ext (Matrix.ext fun i j => ?_)
    have e1 := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h1
    have e2 := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h2
    simp only [glArch_apply, glFin_apply] at e1 e2
    exact Prod.ext e1 e2
  show g * k = k * g
  apply e
  · rw [map_mul, map_mul, hg, one_mul, mul_one]
  · rw [map_mul, map_mul, hk, one_mul, mul_one]

theorem rightTranslate_mem_archCutSubmodule_of_mem_finiteAdelic (tys : ArchTypeFamily F)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F) :
    ∀ φ ∈ archCutSubmodule F tys, rightTranslate F g φ ∈ archCutSubmodule F tys := by
  intro φ hφ
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  refine Submodule.iSup_induction _
    (motive := fun φ => rightTranslate F g φ ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i))
    (hφ w) ?_ ?_ ?_
  · intro i f hfi
    refine Submodule.mem_iSup_of_mem i ?_
    exact comp_mul_mem_typeSubmodule_of_commute hfi _ fun k' =>
      commute_of_glArch_eq_one_of_glFin_eq_one F ((mem_finiteAdelicGL2Subgroup_iff F g).mp hg)
        (glFin_rowIsometryInclAt₀ F w k')
  · exact Submodule.zero_mem _
  · intro a b ha hb; exact Submodule.add_mem _ ha hb

variable {F}
variable {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)

theorem clm_eq_of_forall_toCuspSubcarrier
    (T₁ T₂ : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (h : ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ), T₁ (toCuspSubcarrier F hΦ₀ σ ξ φ) = T₂ (toCuspSubcarrier F hΦ₀ σ ξ φ)) :
    T₁ = T₂ := by
  set X : Submodule ℂ (Carrier F Φ₀ σ) := Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) with hX
  let s : Set ↥(cuspSubcarrier F hΦ₀ σ ξ) := {v | (v : Carrier F Φ₀ σ) ∈ X}
  have hs : Dense s := by
    rw [dense_iff_closure_eq, Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
    have himg : Subtype.val '' s = (X : Set (Carrier F Φ₀ σ)) := by
      ext x
      constructor
      · rintro ⟨v, hv, rfl⟩; exact hv
      · intro hx
        refine ⟨⟨x, ?_⟩, hx, rfl⟩
        show x ∈ cuspSubcarrier F hΦ₀ σ ξ
        unfold cuspSubcarrier
        exact Submodule.le_topologicalClosure _ hx
    rw [Set.eq_univ_iff_forall]
    intro v
    show (v : Carrier F Φ₀ σ) ∈ closure (Subtype.val '' s)
    rw [himg]
    have : (v : Carrier F Φ₀ σ) ∈ (cuspSubcarrier F hΦ₀ σ ξ) := v.2
    unfold cuspSubcarrier at this
    rw [← Submodule.topologicalClosure_coe]
    exact this
  refine ContinuousLinearMap.ext fun v => ?_
  have hEq : Set.EqOn T₁ T₂ s := by
    rintro v ⟨m, hm, hmv⟩
    have hφ : (m : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := hm
    have hv : v = toCuspSubcarrier F hΦ₀ σ ξ ⟨m, hφ⟩ := by
      apply Subtype.ext
      rw [toCuspSubcarrier_apply_coe, ← hmv]
    rw [hv]
    exact h ⟨m, hφ⟩
  exact congrFun (Continuous.ext_on hs T₁.continuous T₂.continuous hEq) v

theorem comp_comm_of_isCuspLift {a b : AdelicGL2 (𝓞 F) F} (hab : Commute a b)
    (Sa Sb : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (ha : IsCuspLift F hΦ₀ σ ξ (rightTranslate F a) Sa) (hb : IsCuspLift F hΦ₀ σ ξ (rightTranslate F b) Sb) :
    Sa.comp Sb = Sb.comp Sa := by
  refine clm_eq_of_forall_toCuspSubcarrier hΦ₀ σ ξ _ _ fun φ => ?_
  have hbφ : rightTranslate F b φ ∈ cuspMemberSubmodule F Φ₀ ξ :=
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ b φ φ.2
  have haφ : rightTranslate F a φ ∈ cuspMemberSubmodule F Φ₀ ξ :=
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ a φ φ.2
  have habφ : rightTranslate F a (rightTranslate F b φ) ∈ cuspMemberSubmodule F Φ₀ ξ :=
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ a _ hbφ
  have hbaφ : rightTranslate F b (rightTranslate F a φ) ∈ cuspMemberSubmodule F Φ₀ ξ :=
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ b _ haφ
  show Sa (Sb (toCuspSubcarrier F hΦ₀ σ ξ φ)) = Sb (Sa (toCuspSubcarrier F hΦ₀ σ ξ φ))
  rw [hb φ hbφ, ha ⟨_, hbφ⟩ habφ, ha φ haφ, hb ⟨_, haφ⟩ hbaφ]
  congr 1
  apply Subtype.ext
  show rightTranslate F a (rightTranslate F b φ) = rightTranslate F b (rightTranslate F a φ)
  rw [rightTranslate_rightTranslate, rightTranslate_rightTranslate, hab.eq]

end PFin

end

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F) :
    ∃ A : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      A.comp A = A ∧
      (∀ M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ), IsClosedCuspSubrep F hΦ₀ σ ξ M → M.map (A : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M) ∧
      (∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        (∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ (g * k) = φ g) →
        A (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) ∧
      (∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        ∃ (φ' : AdelicGL2 (𝓞 F) F → ℂ) (hφ' : φ' ∈ cuspMemberSubmodule F Φ₀ ξ),
          (∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ' (g * k) = φ' g) ∧
          (∀ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys → φ' ∈ archCutSubmodule F tys) ∧
          (∀ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
            (∀ g ∈ finiteAdelicGL2Subgroup F, ∀ ψ ∈ V, rightTranslate F g ψ ∈ V) → φ ∈ V → φ' ∈ V) ∧
          A (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ', hφ'⟩) ∧
      (∀ Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
        (∀ u ∈ U, ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
          IsCuspLift F hΦ₀ σ ξ (rightTranslate F u) S → S.comp Tc = Tc.comp S) →
        A.comp Tc = Tc.comp A) ∧
      (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
        IsCuspLift F hΦ₀ σ ξ (rightTranslate F (rowIsometryInclAt₀ F w k)) S → A.comp S = S.comp A)  := by
  classical
  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    unfold cuspSubcarrier; exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hUf : U ≤ finiteAdelicGL2Subgroup F := by rw [hUO]; exact inf_le_right

  haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU
  letI : MeasurableSpace U := borel U
  haveI : BorelSpace U := ⟨rfl⟩
  set μ : Measure U := Measure.haarMeasure ⊤ with hμ
  haveI : μ.IsHaarMeasure := by rw [hμ]; infer_instance
  haveI : IsProbabilityMeasure μ :=
    ⟨by rw [hμ, ← TopologicalSpace.PositiveCompacts.coe_top]; exact Measure.haarMeasure_self⟩

  obtain ⟨π, hπL, hπn, hπc⟩ :=
    AutomorphicForm.CuspidalSpectrum.exists_monoidHom_isCuspLift_rightTranslate_coe_and_norm_eq_and_continuous_of_isCompact
      F hΦ₀ σ ξ hσ U hU
  have hπb : ∀ u : U, ‖π u‖ ≤ 1 := fun u =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [hπn, one_mul]

  obtain ⟨A, hA, -, hAcl, hAcomm⟩ :=
    ContinuousLinearMap.exists_forall_apply_eq_integral_smul_apply_of_forall_norm_le_of_continuous μ π 1 hπb hπc
      (fun _ => (1 : ℂ)) continuous_const
  have hA1 : ∀ v, A v = ∫ u, π u v ∂μ := fun v => by
    rw [hA]; congr 1; funext u; rw [one_smul]
  obtain ⟨-, hone⟩ :=
    ContinuousLinearMap.comp_eq_of_forall_apply_eq_integral_smul_apply_of_convolution μ π 1 hπb hπc
  obtain ⟨hfix, hidem⟩ := hone A hA1
  refine ⟨A, hidem, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro M hM
    exact hAcl M hM.isClosed fun u => hM.map_le_of_rightTranslate_fin u (hUf u.2) (π u) (hπL u)
  ·
    intro φ hφ hφU
    refine (hfix _).mpr fun u => ?_
    have hmem : rightTranslate F (u : AdelicGL2 (𝓞 F) F) φ ∈ cuspMemberSubmodule F Φ₀ ξ :=
      AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ _ φ hφ
    rw [hπL u ⟨φ, hφ⟩ hmem]
    congr 1
    apply Subtype.ext
    funext x
    exact hφU x u u.2
  ·
    intro φ hφ
    obtain ⟨hψm, hAψ⟩ :=
      AutomorphicForm.CuspidalSpectrum.integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact
        F hΦ₀ σ ξ U hU hUf μ π hπL hπc (fun _ => (1 : ℂ)) continuous_const φ hφ
    set ψ : AdelicGL2 (𝓞 F) F → ℂ := fun x => ∫ u, (fun _ => (1 : ℂ)) u * φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂μ with hψ

    let Hs : Subgroup U :=
      { carrier := {u | ∀ x : AdelicGL2 (𝓞 F) F, φ (x * (u : AdelicGL2 (𝓞 F) F)) = φ x}
        mul_mem' := fun {a b} ha hb x => by
          show φ (x * ((a : AdelicGL2 (𝓞 F) F) * b)) = φ x
          rw [← mul_assoc, hb, ha]
        one_mem' := fun x => by simp
        inv_mem' := fun {a} ha x => by
          have := ha (x * (a⁻¹ : U))
          rw [mul_assoc] at this
          simp only [Subgroup.coe_inv, inv_mul_cancel, mul_one] at this
          exact this.symm }
    have hHs : IsOpen (Hs : Set U) := by
      have hsm : IsKfSmooth F φ := hφ.1.2
      unfold IsKfSmooth FLT.SmoothVectors.IsSmoothVector at hsm
      let incl : U → finiteAdelicGL2Subgroup F := fun u => ⟨u, hUf u.2⟩
      have hincl : Continuous incl := continuous_subtype_val.subtype_mk _
      have hset : (Hs : Set U) = incl ⁻¹'
          ((MulAction.stabilizer (finiteAdelicGL2Subgroup F)
            (FLT.SmoothVectors.RightTranslationFn.mk φ : FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) :
              Subgroup (finiteAdelicGL2Subgroup F)) : Set (finiteAdelicGL2Subgroup F)) := by
        ext u
        simp only [Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff]
        constructor
        · intro hu
          refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
          simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
            FLT.SmoothVectors.RightTranslationFn.toFun_mk]
          exact hu x
        · intro hu x
          have h1 := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f x) hu
          simp only [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul,
            FLT.SmoothVectors.RightTranslationFn.toFun_mk] at h1
          exact h1
      rw [hset]
      exact hsm.preimage hincl
    obtain ⟨n, r, -, hn, -, -, havg⟩ :=
      MeasureTheory.exists_integral_eq_inv_card_mul_sum_of_isOpen_subgroup μ Hs hHs
    have hψsum : ψ = (n : ℂ)⁻¹ • ∑ i, rightTranslate F (r i : AdelicGL2 (𝓞 F) F) φ := by
      funext x
      rw [hψ]
      simp only [one_mul, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      have := havg (fun u => φ (x * (u : AdelicGL2 (𝓞 F) F))) fun v w hw => by
        show φ (x * ((v : AdelicGL2 (𝓞 F) F) * w)) = φ (x * v)
        rw [← mul_assoc]; exact hw (x * v)
      rw [this]
      rfl
    refine ⟨ψ, hψm, ?_, ?_, ?_, ?_⟩
    ·
      intro g k hk
      rw [hψ]
      simp only [one_mul]
      have := integral_mul_left_eq_self (μ := μ) (fun u : U => φ (g * (u : AdelicGL2 (𝓞 F) F))) ⟨k, hk⟩
      simp only [Subgroup.coe_mul] at this
      rw [← this]
      congr 1; funext u; rw [mul_assoc]
    ·
      intro tys htys
      rw [hψsum]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
      exact PFin.rightTranslate_mem_archCutSubmodule_of_mem_finiteAdelic F tys (hUf (r i).2) φ htys
    ·
      intro V hV hφV
      rw [hψsum]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
      exact hV _ (hUf (r i).2) φ hφV
    · rw [hA1, ← hAψ]
      congr 1; funext u; rw [one_smul]
  ·
    intro Tc hTc
    exact (hAcomm Tc fun u => (hTc u u.2 (π u) (hπL u)).symm).symm
  ·
    intro w k S hS
    refine (hAcomm S fun u => ?_).symm
    · exact PFin.comp_comm_of_isCuspLift hΦ₀ σ ξ
        (PFin.commute_of_glArch_eq_one_of_glFin_eq_one F
          ((mem_finiteAdelicGL2Subgroup_iff F _).mp (hUf u.2)) (glFin_rowIsometryInclAt₀ F w k)).symm
        S (π u) hS (hπL u)

end S_AutomorphicForm_CuspidalSpectrum_exists_idempotent_levelAverage_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_idempotent_levelAverage_of_isCompact (solution)
