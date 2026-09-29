-- Prove2me | solution 1 for AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_tsum_finsum_setIntegral_twistedConvOp_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a5777bd4-88ca-565e-8911-039ea4422d34

import Theorems.Thm_AutomorphicForm_forall_integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_tsum_finsum_setIntegral_of_orthonormal_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_twistedConvOp_chiDet_mul_chiDet_inv
import Theorems.Thm_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_sub_lambdaT_tsum_finsum_twistedConvOp_sub_lambdaT_finsum_twistedConvOp_chiDet_sub
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_tsum_finsum_setIntegral_twistedConvOp_sub
p2m_attr_erase "instance" "AutomorphicForm.GaussTwist.instFiniteLocalGaussFactorValHeightOneSpectrumRingOfIntegersMemFinsetModulusPrimes AutomorphicForm.GaussTwist.instFintypeGaussIndex AutomorphicForm.GaussTwist.instCommGroupGaussIndex AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val AutomorphicForm.iotaZsqrtdNegTwo_apply AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.cpowChar_apply_val AutomorphicForm.gl2Weyl_val AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec LanglandsTunnell.Converse.ArchDatumC.mk.injEq LanglandsTunnell.Converse.ArchDatumC.mk.sizeOf_spec LanglandsTunnell.Converse.FinWhittakerDatum.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.sizeOf_spec LanglandsTunnell.Converse.ArchDatumR.mk.injEq LanglandsTunnell.Converse.FinWhittakerDatum.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.sizeOf_spec LanglandsTunnell.Converse.JLData.mk.injEq LanglandsTunnell.Converse.SOrderReps.mk.injEq LanglandsTunnell.Converse.JLData.mk.sizeOf_spec UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply"
p2m_attr_erase "simp" "GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace R4SigmaThreeWay

open Filter Topology

theorem lambdaT_const_mul {Q : Type*} {mQ : MeasurableSpace Q} {G : Type*} [Group G]
    (μ : Measure Q) (u : Q → G) (H : G → ℝ) (T : ℝ) (c : ℂ) (φ : G → ℂ) (g : G) :
    AutomorphicForm.lambdaT μ u H T (fun y => c * φ y) g = c * AutomorphicForm.lambdaT μ u H T φ g := by
  have hct : AutomorphicForm.constantTerm μ u (fun y => c * φ y) =
      fun g' => c * AutomorphicForm.constantTerm μ u φ g' := by
    funext g'
    simp only [AutomorphicForm.constantTerm, AutomorphicForm.constantTermIntegrand]
    exact integral_const_mul c _
  rw [AutomorphicForm.lambdaT_apply, AutomorphicForm.lambdaT_apply, hct]
  by_cases hg : g ∈ AutomorphicForm.highSet H T
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, mul_sub]
  · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, sub_zero, sub_zero]

theorem assembly {Y : Type*} {mY : MeasurableSpace Y} (μ : Measure Y) (Φ₀ : Set Y)
    (F Cb Cn Rs : ℝ → Y → ℂ) (band Cst A₁ A₂ νg μg S : ℂ)
    (hlin : ∀ R x, Cb R x = band * Cn R x)
    (hK : ∀ R : ℝ, IntegrableOn (Cn R) Φ₀ μ ∧ ∫ x in Φ₀, Cn R x ∂μ = Cst)
    (hRi : ∀ R : ℝ, IntegrableOn (Rs R) Φ₀ μ)
    (hRt : Tendsto (fun R : ℝ => ∫ x in Φ₀, Rs R x ∂μ) atTop (𝓝 A₁))
    (hCi : ∀ᶠ R : ℝ in atTop, IntegrableOn (fun x => F R x - Cb R x - Rs R x) Φ₀ μ)
    (hCt : Tendsto (fun R : ℝ => (∫ x in Φ₀, (F R x - Cb R x - Rs R x) ∂μ) -
      ((R : ℂ) * νg + A₂ + μg)) atTop (𝓝 0))
    (hS : S = A₁ + A₂) :
    Tendsto (fun R : ℝ => (∫ x in Φ₀, F R x ∂μ) - (band * Cst + ((R : ℂ) * νg + S + μg)))
      atTop (𝓝 0) := by
  have h2 : Tendsto (fun R : ℝ => (∫ x in Φ₀, Rs R x ∂μ) - A₁) atTop (𝓝 0) :=
    tendsto_sub_nhds_zero_iff.mpr hRt
  have h := hCt.add h2
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [hCi] with R hint
  obtain ⟨hCn, hCst⟩ := hK R
  have hCbfun : Cb R = fun x => band * Cn R x := funext (hlin R)
  have hCb : IntegrableOn (Cb R) Φ₀ μ := by
    rw [hCbfun]
    exact hCn.const_mul band
  have hCbint : ∫ x in Φ₀, Cb R x ∂μ = band * Cst := by
    rw [show (fun x => Cb R x) = fun x => band * Cn R x from funext (hlin R), integral_const_mul, hCst]
  have hsplit : ∫ x in Φ₀, F R x ∂μ =
      (∫ x in Φ₀, (F R x - Cb R x - Rs R x) ∂μ) + (∫ x in Φ₀, Cb R x ∂μ) + ∫ x in Φ₀, Rs R x ∂μ := by
    have hF : (fun x => F R x) = fun x => (F R x - Cb R x - Rs R x) + Cb R x + Rs R x :=
      funext fun x => by ring
    rw [hF, integral_add _ (hRi R), integral_add hint hCb]
    exact hint.add hCb
  rw [hsplit, hCbint, hS]
  ring

theorem exists_interleave {τ : Type} (X : Set τ) (t₁ t₂ : ℕ → τ) (ht₁ : ∀ n, t₁ n ∈ X)
    (ht₂ : ∀ n, t₂ n ∈ X) (c₁ c₂ : ℕ → ℂ) :
    ∃ (t : ℕ → τ) (_ : ∀ n, t n ∈ X) (c : ℕ → ℂ),
      (∀ k, t (2 * k) = t₁ k) ∧ (∀ k, t (2 * k + 1) = t₂ k) ∧
      (∀ k, c (2 * k) = c₁ k) ∧ (∀ k, c (2 * k + 1) = c₂ k) := by
  refine ⟨fun n => if n % 2 = 0 then t₁ (n / 2) else t₂ (n / 2), fun n => ?_,
    fun n => if n % 2 = 0 then c₁ (n / 2) else c₂ (n / 2), fun k => ?_, fun k => ?_, fun k => ?_,
    fun k => ?_⟩
  · dsimp only
    split_ifs
    · exact ht₁ _
    · exact ht₂ _
  · dsimp only
    rw [if_pos (Nat.mul_mod_right 2 k), Nat.mul_div_cancel_left k Nat.two_pos]
  · dsimp only
    rw [if_neg (by omega), show (2 * k + 1) / 2 = k by omega]
  · dsimp only
    rw [if_pos (Nat.mul_mod_right 2 k), Nat.mul_div_cancel_left k Nat.two_pos]
  · dsimp only
    rw [if_neg (by omega), show (2 * k + 1) / 2 = k by omega]

theorem tsum_interleave (F F₁ F₂ : ℕ → ℂ) (he : ∀ k, F (2 * k) = F₁ k) (ho : ∀ k, F (2 * k + 1) = F₂ k)
    (h₁ : Summable F₁) (h₂ : Summable F₂) : ∑' n, F n = ∑' k, F₁ k + ∑' k, F₂ k := by
  have he' : (fun k => F (2 * k)) = F₁ := funext he
  have ho' : (fun k => F (2 * k + 1)) = F₂ := funext ho
  have hse : Summable fun k => F (2 * k) := by rw [he']; exact h₁
  have hso : Summable fun k => F (2 * k + 1) := by rw [ho']; exact h₂
  have hsplit := tsum_even_add_odd hse hso
  rw [he', ho'] at hsplit
  exact hsplit.symm

end R4SigmaThreeWay

open AutomorphicForm R4SigmaThreeWay in
open scoped TensorProduct.RightActions in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ))
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ι : Type) (b : ι → AdelicGL2 (𝓞 L) L → ℂ) (cls : ι → HeckeEigensystem L ℂ)
    (hb : ∀ i, cls i ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL ∧
      b i ∈ isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL (cls i) ⊓ archCutSubmodule L tysL)
    (hb₁ : ∀ i, ∫ g in ΦL, b i g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ g in ΦL, b i g * conj (b j g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0)
    (hbs : ∀ π ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL,
      {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL π ⊓ archCutSubmodule L tysL)
    (hbc : ∀ ψ : AdelicGL2 (𝓞 L) L → ℂ,
      IsSmoothCuspAutomorphicFnAt L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL ψ →
      Continuous ψ →
      (∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).U N, ψ (g * k) = ψ g) →
      ψ ∈ archCutSubmodule L tysL →
      (∀ i, ∫ g in ΦL, ψ g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0) →
      ψ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL] 0) :
    ∃ (tabs : ℕ → (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (htabs : ∀ n, tabs n ∈ X) (cs : ℕ → ℂ),
    (Summable fun n => ‖cs n‖) ∧
    (∀ n, cs n ≠ 0 →
      (∀ w w' : HeightOneSpectrum (𝓞 L), w ∉ SL → w' ∉ SL →
          HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → tabs n w = tabs n w') ∧
      ∃ (M : Ideal (𝓞 L)) (hM : M ≠ ⊥) (χ₁ χ₂ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₁ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
            χ₁ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ₂ z : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
            χ₂ z = 1) ∧
        ∀ w : HeightOneSpectrum (𝓞 L), w ∉ SL →
          tabs n w = ((LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).a w,
            (LanglandsTunnell.Converse.eisensteinTableOf L M hM χ₁ χ₂).b w)) ∧
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T S → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →
      ∃ μ ν : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖μ g‖ < ε) ∧
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
        IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ →
        IsArchBiFinite L tysL φ →
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
    Filter.Tendsto (fun R : ℝ =>
      (∫ x in Φ₀,
          @AutomorphicForm.lambdaT _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
            (fun t => AutomorphicForm.unipotentGL2 t)
            (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
            (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
              ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                  AutomorphicForm.sigmaAdelicAct K L D σ.symm
                    (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
            x
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) -
      ((((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                    (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                    Ψ ∈ cuspClasses L
                      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                  ∑ᶠ i : {i // cls i = Ψ.1},
                    ∫ x in Φ₀, twistedConvOp K L D σ φ (b i) x * conj (b i x)
                      ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) +
            ((R : ℂ) * ν g + (∑' n, cs n * g ⟨tabs n, htabs n⟩) + μ g)))
      Filter.atTop (nhds 0) := by

  have hK :=
    AutomorphicForm.forall_integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_tsum_finsum_setIntegral_of_orthonormal_of_isFundamentalDomain_slab
      K L D σ α β hα hαβ ΦL hΦs hΦ ξL SL hSL N hN tysL Φ₀ hΦ₀s hΦ₀ ι b cls hb hb₁ hb₀ hbs

  obtain ⟨tabs₁, htabs₁, cs₁, hsum₁, hat₁, hres⟩ :=
    AutomorphicForm.exists_atomic_forall_integrableOn_and_tendsto_setIntegral_lambdaT_finsum_twistedConvOp_chiDet_mul_chiDet_inv
      K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen SL ξL hSL hξc hξt N hN tysL S φa φS X hX c u d₁ d₂ hc
      Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀

  obtain ⟨tabs₂, htabs₂, cs₂, hsum₂, hat₂, hcont⟩ :=
    AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_sub_lambdaT_tsum_finsum_twistedConvOp_sub_lambdaT_finsum_twistedConvOp_chiDet_sub
      K L α β hα hαβ ΦL hΦs hΦ νZL ΩL hΩL D σ hgen SL ξL hSL hξc hξt N hN tysL S φa φS X hX c u d₁ d₂ hc
      Tc hTc Φ₀ hΦ₀S hΦ₀s hΦ₀ ι b cls hb hb₁ hb₀ hbs hbc

  obtain ⟨tabs, htabs, cs, ht_even, ht_odd, hc_even, hc_odd⟩ :=
    exists_interleave X tabs₁ tabs₂ htabs₁ htabs₂ cs₁ cs₂
  have hsum : Summable fun n => ‖cs n‖ := by
    refine Summable.even_add_odd (f := fun n => ‖cs n‖) ?_ ?_
    · simpa only [hc_even] using hsum₁
    · simpa only [hc_odd] using hsum₂
  refine ⟨tabs, htabs, cs, hsum, ?_, ?_⟩
  ·
    intro n hn
    obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
    · rw [hc_even] at hn
      obtain ⟨hfib, M, hM, χ₁, χ₂, h1, h2, h3, h4, h6⟩ := hat₁ k hn
      exact ⟨fun w w' hw hw' hu => by rw [ht_even]; exact hfib w w' hw hw' hu, M, hM, χ₁, χ₂, h1, h2,
        h3, h4, fun w hw => by rw [ht_even]; exact h6 w hw⟩
    · rw [hc_odd] at hn
      obtain ⟨hfib, M, hM, χ₁, χ₂, h1, h2, h3, h4, h6⟩ := hat₂ k hn
      exact ⟨fun w w' hw hw' hu => by rw [ht_odd]; exact hfib w w' hw hw' hu, M, hM, χ₁, χ₂, h1, h2,
        h3, h4, fun w hw => by rw [ht_odd]; exact h6 w hw⟩
  intro T hTS hT2 hTSL ws w' hw' ϖs hirr hϖ0 ns rTs hcos zs hz
  obtain ⟨μf, νf, hnoatom, hmain⟩ := hcont T hTS hT2 hTSL ws w' hw' ϖs hirr hϖ0 ns rTs hcos zs hz
  refine ⟨μf, νf, hnoatom, ?_⟩
  intro ks js φ hφ hφc φf hfact hbi hfin g hg
  have hC := hmain ks js φ hφ hφc φf hfact hbi hfin g hg
  have hR := hres T hTS hT2 hTSL ws w' hw' ϖs hirr hϖ0 ns rTs hcos zs hz ks js φ hφ hφc φf hfact hbi
    hfin g hg

  have hφf : IsFactorizableTestFn L φ := ⟨φa, φf, hfact.1, hfact.2.1, hfact.2.2.2.2.2⟩
  have hKφ := hK φ hφ hφc hφf hbi hfin

  have hL : (∑' n, cs n * g ⟨tabs n, htabs n⟩) =
      (∑' k, cs₁ k * g ⟨tabs₁ k, htabs₁ k⟩) + ∑' k, cs₂ k * g ⟨tabs₂ k, htabs₂ k⟩ := by
    refine tsum_interleave (fun n => cs n * g ⟨tabs n, htabs n⟩) (fun k => cs₁ k * g ⟨tabs₁ k, htabs₁ k⟩)
      (fun k => cs₂ k * g ⟨tabs₂ k, htabs₂ k⟩) (fun k => ?_) (fun k => ?_) hR.2.1 hC.2.1
    · show cs (2 * k) * g ⟨tabs (2 * k), htabs (2 * k)⟩ = cs₁ k * g ⟨tabs₁ k, htabs₁ k⟩
      rw [hc_even, show (⟨tabs (2 * k), htabs (2 * k)⟩ : X) = ⟨tabs₁ k, htabs₁ k⟩ from
        Subtype.ext (ht_even k)]
    · show cs (2 * k + 1) * g ⟨tabs (2 * k + 1), htabs (2 * k + 1)⟩ = cs₂ k * g ⟨tabs₂ k, htabs₂ k⟩
      rw [hc_odd, show (⟨tabs (2 * k + 1), htabs (2 * k + 1)⟩ : X) = ⟨tabs₂ k, htabs₂ k⟩ from
        Subtype.ext (ht_odd k)]

  exact assembly (adelicGLHaar (Fin 2) (𝓞 L) L) Φ₀
    (fun (R : ℝ) (x : AdelicGL2 (𝓞 L) L) =>
            (@AutomorphicForm.lambdaT _
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
              (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (fun y => ∑ᶠ q : GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L),
                ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
                  φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L q.out *
                    AutomorphicForm.sigmaAdelicAct K L D σ.symm
                      (AutomorphicForm.centralScalar (𝓞 L) L z * y)) ∂νZL)
              x))
    (fun (R : ℝ) (x : AdelicGL2 (𝓞 L) L) =>
            (@AutomorphicForm.lambdaT _
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
              (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                    (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                  ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                      Ψ ∈ cuspClasses L
                        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                    ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
              x))
    (fun (R : ℝ) (x : AdelicGL2 (𝓞 L) L) =>
            (@AutomorphicForm.lambdaT _
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
              (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (fun y => ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                    Ψ ∈ cuspClasses L
                      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                  ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
              x))
    (fun (R : ℝ) (x : AdelicGL2 (𝓞 L) L) =>
            (@AutomorphicForm.lambdaT _
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
              (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
              (fun t => AutomorphicForm.unipotentGL2 t)
              (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
              (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                    (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) /
                    (((adelicGLHaar (Fin 2) (𝓞 L) L) Φ₀).toReal : ℂ) *
                  ∑ᶠ (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (_ : χ ∈ {χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ |
                        SquaresToXi (𝓞 L) L ⊤ ξL χ ∧
                        (∀ z : (AdeleRing (𝓞 L) L)ˣ,
                          z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
                            χ z = 1) ∧
                        Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ)}),
                    twistedConvOp K L D σ φ (chiDet (𝓞 L) L χ) x * chiDet (𝓞 L) L χ⁻¹ y)
              x))
    ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
          (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ)
    (∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
          Ψ ∈ cuspClasses L
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
        ∑ᶠ i : {i // cls i = Ψ.1},
          ∫ x in Φ₀, twistedConvOp K L D σ φ (b i) x * conj (b i x)
            ∂(adelicGLHaar (Fin 2) (𝓞 L) L))
    (∑' k, cs₁ k * g ⟨tabs₁ k, htabs₁ k⟩) (∑' k, cs₂ k * g ⟨tabs₂ k, htabs₂ k⟩) (νf g) (μf g)
    (∑' n, cs n * g ⟨tabs n, htabs n⟩)
    (fun R x => lambdaT_const_mul _ _ _ _ _
      (fun y => ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
          Ψ ∈ cuspClasses L
            (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
              (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
        ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
      x)
    hKφ hR.1 hR.2.2 hC.1 hC.2.2 hL

end S_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_tsum_finsum_setIntegral_twistedConvOp_sub
end P2MW
export P2MW.S_AutomorphicForm_exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_integral_sigmaAdelicAct_centralScalar_sub_tsum_finsum_setIntegral_twistedConvOp_sub (solution)
