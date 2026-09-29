-- Prove2me | solution 1 for AutomorphicForm.exists_torusFamily_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/814b9f1f-8229-5ba9-ae34-0569e6187ab5

import Mathlib
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Theorems.Thm_AutomorphicForm_centralizer_secondCountableTopology_locallyCompactSpace_and_exists_glArch_finComponent_localIntegralSet_isOpen_surjective_isCompact_restrictedProduct
import Theorems.Thm_AutomorphicForm_exists_forall_isHaarMeasure_centralizer_centralScalar_mul_diagUnits2_and_integral_eq_mul_integral_prod_of_ne_one
import Theorems.Thm_MeasureTheory_Measure_exists_haar_forall_lintegral_mul_prod_mul_indicator_eq_mul_lintegral_mul_prod_lintegral_of_restrictedProduct
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_torusFamily_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty RestrictedProduct.instIsDirectLimit' RestrictedProduct.instIsDirectLimit RestrictedProduct.instNonemptyOrderDualElemSetSets_definitions RestrictedProduct.instDirectedSystem RestrictedProduct.instDirectedSystemCoeSubmoduleCoeLinearMapIdInclusionLinearMap RestrictedProduct.directed RestrictedProduct.instDirectedSystemOrderDualElemSetSetsCoeSubmodulePrincipalValMemCoeLinearMapIdInclusionLinearMap M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.JPSSCubicLiftPackage.mk.sizeOf_spec AutomorphicForm.formalBaseChange_a"
p2m_attr_erase "simp" "AutomorphicForm.JPSSCubicLiftPackage.mk.injEq AutomorphicForm.formalBaseChange_b LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv LocalGL2.transposeGL_val LocalGL2.transposeGL_one LocalGL2.swapUnit_val M4aHerbrand.AdeleBaseChange.mk.sizeOf_spec M4aHerbrand.AdeleBaseChange.mk.injEq M4aHerbrand.Bridge.prodTensorAlgEquiv_tmul M4aHerbrand.Bridge.genuineβ_fst M4aHerbrand.Bridge.genuineβ_snd M4aHerbrand.Bridge.finiteConorm_apply M4aHerbrand.Bridge.tensorAdeleRingEquiv_apply M4aHerbrand.Bridge.flattenPlaces_apply M4aHerbrand.Bridge.congrPlaces_apply M4aHerbrand.Bridge.integralTensorRingEquiv_tmul M4aHerbrand.Bridge.moduleStructureBridge_apply RestrictedProduct.lTensorEquivLeft_tmul RestrictedProduct.lTensorEquiv_tmul RestrictedProduct.lTensorLeft_tmul RestrictedProduct.lTensor_tmul IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply LT.TwistedNorm.sigmaPartialNorm_zero LT.TwistedNorm.GL2.traceDetCompanion_apply_10 LT.TwistedNorm.GL2.traceDetCompanion_apply_00 LT.TwistedNorm.GL2.traceDetCompanion_apply_01 LT.TwistedNorm.GL2.traceDetCompanion_apply_11 AdelicDock.coe_finEmbed AdelicDock.splice_apply_self"
p2m_attr_erase "simp" "AdelicDock.coe_localEmbed AutomorphicForm.gl2Weyl_val"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

noncomputable section

namespace TorusFamilyK

section Bochner

open scoped ENNReal

variable {B : Type*} [MeasurableSpace B] {A : Type} [MeasurableSpace A]
  {κ : Type} {G : κ → Type} [∀ k, MeasurableSpace (G k)]

def OptTy (A : Type) (G : κ → Type) (Sf : Finset κ) : Option (↥Sf) → Type :=
  fun i => Option.elim i A (fun k => G (k : κ))

scoped instance instMeasurableSpaceOptTy (Sf : Finset κ) :
    ∀ i, MeasurableSpace (OptTy A G Sf i)
  | none => (inferInstance : MeasurableSpace A)
  | some k => (inferInstance : MeasurableSpace (G (k : κ)))

def optMap (Sf : Finset κ) (q : B → A) (p : ∀ k, B → G k) (b : B) : ∀ i, OptTy A G Sf i
  | none => q b
  | some k => p k b

def optMeas (Sf : Finset κ) (νA : Measure A) (νG : ∀ k, Measure (G k)) : ∀ i, Measure (OptTy A G Sf i)
  | none => νA
  | some k => νG k

theorem measurable_optMap (Sf : Finset κ) {q : B → A} (hq : Measurable q) {p : ∀ k, B → G k}
    (hp : ∀ k, Measurable (p k)) : Measurable (optMap Sf q p) := by
  rw [measurable_pi_iff]
  rintro (_ | k)
  · exact hq
  · exact hp k

scoped instance sigmaFinite_optMeas (Sf : Finset κ) (νA : Measure A) (νG : ∀ k, Measure (G k))
    [SigmaFinite νA] [∀ k, SigmaFinite (νG k)] : ∀ i, SigmaFinite (optMeas Sf νA νG i)
  | none => (inferInstance : SigmaFinite νA)
  | some k => (inferInstance : SigmaFinite (νG k))

theorem map_optMap_restrict_eq_pi (Sf : Finset κ) {q : B → A} (hq : Measurable q) {p : ∀ k, B → G k}
    (hp : ∀ k, Measurable (p k)) (U : ∀ k, Set (G k))
    (hPm : MeasurableSet {b : B | ∀ k, k ∉ Sf → p k b ∈ U k})
    (ν : Measure B) (νA : Measure A) (νG : ∀ k, Measure (G k)) [SigmaFinite νA] [∀ k, SigmaFinite (νG k)]
    (H : ∀ (g : A → ℝ≥0∞) (f : ∀ k, G k → ℝ≥0∞), Measurable g → (∀ k ∈ Sf, Measurable (f k)) →
      ∫⁻ b, g (q b) * (∏ k ∈ Sf, f k (p k b)) *
          Set.indicator {b : B | ∀ k, k ∉ Sf → p k b ∈ U k} (fun _ => (1 : ℝ≥0∞)) b ∂ν =
        (∫⁻ y, g y ∂νA) * ∏ k ∈ Sf, ∫⁻ x, f k x ∂(νG k)) :
    Measure.map (optMap Sf q p) (ν.restrict {b : B | ∀ k, k ∉ Sf → p k b ∈ U k}) =
      Measure.pi (optMeas Sf νA νG) := by
  classical
  symm
  apply Measure.pi_eq
  intro s hs
  set P : Set B := {b : B | ∀ k, k ∉ Sf → p k b ∈ U k} with hPdef
  rw [Measure.map_apply (measurable_optMap Sf hq hp) (MeasurableSet.univ_pi hs),
    Measure.restrict_apply ((measurable_optMap Sf hq hp) (MeasurableSet.univ_pi hs))]

  set g : A → ℝ≥0∞ := (s none).indicator 1 with hgdef
  set f : ∀ k, G k → ℝ≥0∞ := fun k =>
    if hk : k ∈ Sf then (s (some ⟨k, hk⟩)).indicator 1 else 1 with hfdef
  have hgm : Measurable g := measurable_one.indicator (hs none)
  have hfm : ∀ k ∈ Sf, Measurable (f k) := by
    intro k hk
    simp only [hfdef, dif_pos hk]
    exact measurable_one.indicator (hs (some ⟨k, hk⟩))
  have key := H g f hgm hfm

  have hind : ∀ b, g (q b) * (∏ k ∈ Sf, f k (p k b)) * P.indicator (fun _ => (1 : ℝ≥0∞)) b =
      ((optMap Sf q p) ⁻¹' (Set.univ.pi s) ∩ P).indicator 1 b := by
    intro b
    by_cases hb : b ∈ (optMap Sf q p) ⁻¹' (Set.univ.pi s) ∩ P
    · rw [Set.indicator_of_mem hb]
      obtain ⟨hb1, hb2⟩ := hb
      rw [Set.mem_preimage, Set.mem_univ_pi] at hb1
      have h1 : g (q b) = 1 := by
        rw [hgdef]; exact Set.indicator_of_mem (hb1 none) 1
      have h2 : ∏ k ∈ Sf, f k (p k b) = 1 := by
        refine Finset.prod_eq_one fun k hk => ?_
        simp only [hfdef, dif_pos hk]
        exact Set.indicator_of_mem (hb1 (some ⟨k, hk⟩)) 1
      rw [h1, h2, Set.indicator_of_mem hb2, Pi.one_apply]; simp
    · rw [Set.indicator_of_notMem hb]
      by_cases hbP : b ∈ P
      · have hb1 : ¬ optMap Sf q p b ∈ Set.univ.pi s := fun h => hb ⟨h, hbP⟩
        rw [Set.mem_univ_pi] at hb1
        push_neg at hb1
        obtain ⟨i, hi⟩ := hb1
        cases i with
        | none =>
          have h1 : g (q b) = 0 := by rw [hgdef]; exact Set.indicator_of_notMem hi 1
          rw [h1]; simp
        | some k =>
          have h2 : ∏ k ∈ Sf, f k (p k b) = 0 := by
            refine Finset.prod_eq_zero k.2 ?_
            simp only [hfdef, dif_pos k.2]
            exact Set.indicator_of_notMem hi 1
          rw [h2]; simp
      · rw [Set.indicator_of_notMem hbP]; simp
  simp_rw [hind] at key
  rw [lintegral_indicator_one (((measurable_optMap Sf hq hp) (MeasurableSet.univ_pi hs)).inter hPm)]
    at key
  rw [key]

  have hgi : ∫⁻ y, g y ∂νA = νA (s none) := by
    rw [hgdef]; exact lintegral_indicator_one (hs none)
  have hfi : ∏ k ∈ Sf, ∫⁻ x, f k x ∂(νG k) = ∏ k : ↥Sf, νG k (s (some k)) := by
    rw [← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [hfdef, dif_pos k.2]
    exact lintegral_indicator_one (hs (some ⟨k, k.2⟩))
  rw [hgi, hfi, Fintype.prod_option]
  rfl

theorem integral_eq_mul_prod_of_lintegral_factorisation (Sf : Finset κ) {q : B → A} (hq : Measurable q)
    {p : ∀ k, B → G k} (hp : ∀ k, Measurable (p k)) (U : ∀ k, Set (G k))
    (hPm : MeasurableSet {b : B | ∀ k, k ∉ Sf → p k b ∈ U k})
    (ν : Measure B) (νA : Measure A) (νG : ∀ k, Measure (G k)) [SigmaFinite νA] [∀ k, SigmaFinite (νG k)]
    (H : ∀ (g : A → ℝ≥0∞) (f : ∀ k, G k → ℝ≥0∞), Measurable g → (∀ k ∈ Sf, Measurable (f k)) →
      ∫⁻ b, g (q b) * (∏ k ∈ Sf, f k (p k b)) *
          Set.indicator {b : B | ∀ k, k ∉ Sf → p k b ∈ U k} (fun _ => (1 : ℝ≥0∞)) b ∂ν =
        (∫⁻ y, g y ∂νA) * ∏ k ∈ Sf, ∫⁻ x, f k x ∂(νG k))
    (W : B → ℂ) (Wa : A → ℂ) (WS : ∀ k, G k → ℂ)
    (hWa : AEStronglyMeasurable Wa νA) (hWS : ∀ k ∈ Sf, AEStronglyMeasurable (WS k) (νG k))
    (hW1 : ∀ b, (∀ k ∉ Sf, p k b ∈ U k) → W b = Wa (q b) * ∏ k ∈ Sf, WS k (p k b))
    (hW0 : ∀ b, (∃ k ∉ Sf, p k b ∉ U k) → W b = 0) :
    ∫ b, W b ∂ν = (∫ y, Wa y ∂νA) * ∏ k ∈ Sf, ∫ x, WS k x ∂(νG k) := by
  classical
  set P : Set B := {b : B | ∀ k, k ∉ Sf → p k b ∈ U k} with hPdef

  let fi : ∀ i, OptTy A G Sf i → ℂ := fun i => match i with
    | none => Wa
    | some k => WS k
  set F : (∀ i, OptTy A G Sf i) → ℂ := fun x => ∏ i, fi i (x i) with hFdef
  have hFopt : ∀ b, F (optMap Sf q p b) = Wa (q b) * ∏ k ∈ Sf, WS k (p k b) := by
    intro b
    rw [hFdef]
    dsimp only
    rw [Fintype.prod_option]
    change Wa (q b) * ∏ i : ↥Sf, WS (i : κ) (p (i : κ) b) = _
    rw [Finset.prod_coe_sort Sf (fun k => WS k (p k b))]
  have hW : W = P.indicator (fun b => F (optMap Sf q p b)) := by
    funext b
    by_cases hb : b ∈ P
    · rw [Set.indicator_of_mem hb, hFopt, hW1 b hb]
    · rw [Set.indicator_of_notMem hb]
      apply hW0
      simpa [hPdef] using hb
  have hΨ := measurable_optMap Sf hq hp
  have hpi := map_optMap_restrict_eq_pi Sf hq hp U hPm ν νA νG H
  have hFm : AEStronglyMeasurable F (Measure.pi (optMeas Sf νA νG)) := by
    have hFeq : F = ∏ i ∈ Finset.univ, (fun x : (∀ i, OptTy A G Sf i) => fi i (x i)) := by
      funext x
      rw [hFdef, Finset.prod_apply]
    rw [hFeq]
    refine Finset.aestronglyMeasurable_prod _ fun i _ => ?_
    have hqmp := Measure.quasiMeasurePreserving_eval (optMeas Sf νA νG) i
    rcases i with (_ | k)
    · exact hWa.comp_quasiMeasurePreserving hqmp
    · exact (hWS k k.2).comp_quasiMeasurePreserving hqmp
  calc ∫ b, W b ∂ν = ∫ b in P, F (optMap Sf q p b) ∂ν := by
        rw [hW, integral_indicator hPm]
    _ = ∫ x, F x ∂(Measure.map (optMap Sf q p) (ν.restrict P)) := by
        rw [integral_map hΨ.aemeasurable]
        rw [hpi]; exact hFm
    _ = ∫ x, F x ∂(Measure.pi (optMeas Sf νA νG)) := by rw [hpi]
    _ = ∏ i, ∫ x, fi i x ∂(optMeas Sf νA νG i) := by
        rw [hFdef]
        exact integral_fintype_prod_eq_prod (𝕜 := ℂ) fi
    _ = (∫ y, Wa y ∂νA) * ∏ k ∈ Sf, ∫ x, WS k x ∂(νG k) := by
        rw [Fintype.prod_option]
        change (∫ y, Wa y ∂νA) * ∏ i : ↥Sf, ∫ x, WS (i : κ) x ∂(νG i) = _
        rw [Finset.prod_coe_sort Sf (fun k => ∫ x, WS k x ∂(νG k))]

end Bochner

section PerClass

open scoped ENNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.localCentralizerBorel

variable (K : Type) [Field K] [NumberField K]

def evalCME (M : Type) [Group M] [TopologicalSpace M] : (Unit → M) ≃ₜ* M :=
  { MulEquiv.funUnique Unit M with
    continuous_toFun := continuous_apply ()
    continuous_invFun := continuous_pi fun _ => continuous_id }

theorem evalCME_apply (M : Type) [Group M] [TopologicalSpace M] (y : Unit → M) : evalCME M y = y () := rfl

theorem perClass (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) (τ : Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))) [τ.IsHaarMeasure] :
    ∃ (τA : Measure (Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))) (τF : ∀ v : HeightOneSpectrum (𝓞 K), Measure (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))),
      τA.IsHaarMeasure ∧ (∀ v, (τF v).IsHaarMeasure) ∧
      (∀ v, τF v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1) ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable (fun t : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))) => Wa t) τA →
        (∀ v ∈ S, AEStronglyMeasurable (fun t : AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) => WS v t) (τF v)) →
        (∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂τ = (∫ t, Wa t ∂τA) * ∏ v ∈ S, ∫ t, WS v t ∂(τF v) := by
  obtain ⟨hT1, hT2, hA1, hA2, hV, q, p, U, hq, hp, hU, hqc, hpc, hUc, hUo, hP, hsurj, hbox⟩ :=
    AutomorphicForm.centralizer_secondCountableTopology_locallyCompactSpace_and_exists_glArch_finComponent_localIntegralSet_isOpen_surjective_isCompact_restrictedProduct K γ
  haveI := hT1; haveI := hT2; haveI := hA1; haveI := hA2
  haveI : ∀ v, SecondCountableTopology (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))) := fun v => (hV v).1
  haveI : ∀ v, LocallyCompactSpace (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))) := fun v => (hV v).2
  haveI : BorelSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))) := ⟨rfl⟩
  haveI : BorelSpace (Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))) := fun v => ⟨rfl⟩
  haveI : SigmaCompactSpace (Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : ∀ v, SigmaCompactSpace (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))) := fun v => sigmaCompactSpace_of_locallyCompact_secondCountable

  obtain ⟨νA, νG, hνA, hνG, hfac⟩ :=
    MeasureTheory.Measure.exists_haar_forall_lintegral_mul_prod_mul_indicator_eq_mul_lintegral_mul_prod_lintegral_of_restrictedProduct
      (B := Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))) (α := Unit) (A := fun _ => Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) (G := fun v => AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))
      (fun _ => q) (fun _ => hqc) p hpc U hUc hUo hP
      (fun Sf y x hx => by
        obtain ⟨b, hb1, hb2⟩ := hsurj Sf (y ()) x hx
        exact ⟨b, fun a => hb1, hb2⟩)
      (fun D C hD hC hfin => by
        have hset : {b : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) | (∀ a : Unit, q b ∈ D a) ∧ ∀ k, p k b ∈ C k} =
            {b : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) | q b ∈ D () ∧ ∀ k, p k b ∈ C k} := by
          ext b
          simp only [Set.mem_setOf_eq]
          exact ⟨fun h => ⟨h.1 (), h.2⟩, fun h => ⟨fun a => h.1, h.2⟩⟩
        show IsCompact {b : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) | (∀ a : Unit, q b ∈ D a) ∧ ∀ k, p k b ∈ C k}
        rw [hset]
        exact hbox (D ()) C (hD ()) hC hfin)
      τ
  haveI := hνA
  haveI : ∀ v, (νG v).IsHaarMeasure := fun v => (hνG v).1
  set τA : Measure (Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := Measure.map (evalCME (Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))) νA with hτA
  haveI hτAh : τA.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map νA _
  refine ⟨τA, νG, hτAh, fun v => (hνG v).1, fun v => ?_, ?_⟩
  · rw [← hU v]; exact (hνG v).2
  intro S W Wa WS hWa hWS hW1 hW0
  have hqm : Measurable (q : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) → Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) := hqc.measurable
  have hpm : ∀ v, Measurable (p v : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) → AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))) := fun v => (hpc v).measurable

  have H : ∀ (g : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))) → ℝ≥0∞) (f : ∀ v, AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)) → ℝ≥0∞), Measurable g → (∀ k ∈ S, Measurable (f k)) →
      ∫⁻ b, g (q b) * (∏ k ∈ S, f k (p k b)) *
          Set.indicator {b : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) | ∀ k, k ∉ S → p k b ∈ U k} (fun _ => (1 : ℝ≥0∞)) b ∂τ =
        (∫⁻ y, g y ∂τA) * ∏ k ∈ S, ∫⁻ x, f k x ∂(νG k) := by
    intro g f hg hf
    have h := hfac S (fun y => g (y ())) f (hg.comp (measurable_pi_apply ())) hf
    rw [hτA, lintegral_map hg (map_continuous (evalCME _)).measurable]
    exact h
  have main := integral_eq_mul_prod_of_lintegral_factorisation (B := Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))) (A := Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) (G := fun v => AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))) S hqm hpm
    (fun v => ((U v : Subgroup (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))) : Set (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))))) (hP S).measurableSet τ τA νG H
    (fun t => W t) (fun t => Wa t) (fun v t => WS v t) hWa hWS
    (fun b hb => by
      have hb' : ∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (b : GL (Fin 2) (AdeleRing (𝓞 K) K))) ∈
          AutomorphicForm.localIntegralSet K v := fun v hv => by
        have h1 : (p v b) ∈ ((U v : Subgroup (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))) : Set (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))) := hb v hv
        rw [hU v, Set.mem_preimage, hp] at h1
        exact h1
      beta_reduce
      rw [hW1 b hb', hq]
      simp only [hp])
    (fun b hb => by
      obtain ⟨v, hv, hbv⟩ := hb
      refine hW0 b ⟨v, hv, fun h => hbv ?_⟩
      show (p v b) ∈ ((U v : Subgroup (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))) : Set (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))))
      rw [hU v, Set.mem_preimage, hp]
      exact h)
  exact main

end PerClass

end TorusFamilyK
p2m_reactivate "P2MW.S_AutomorphicForm_exists_torusFamily_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct.TorusFamilyK"

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in
open AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (cτK : ℝ) (hcτK : 0 < cτK) :
    ∃ (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))) (τA : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))) (cT : ℝ),
      (∀ u z, ((u : Kˣ) : K) ≠ 1 → (τG u z).IsHaarMeasure) ∧ (∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG u z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK)) ∧ (∀ u z, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA u z)) ∧ (∀ u z v, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF u z v)) ∧ (∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF u z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1) ∧ 0 < cT ∧ (∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA u z) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF u z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG u z) = cT * (∫ t, Wa t ∂(τA u z)) * ∏ v ∈ S, ∫ t, WS v t ∂(τF u z v)) := by
  classical
  obtain ⟨τG, hτG1, hτG2⟩ :=
    AutomorphicForm.exists_forall_isHaarMeasure_centralizer_centralScalar_mul_diagUnits2_and_integral_eq_mul_integral_prod_of_ne_one
      K νZK cτK hcτK
  have key : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), ((u : Kˣ) : K) ≠ 1 → _ :=
    fun u z hu => by
      haveI := hτG1 u z hu
      exact TorusFamilyK.perClass K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) (τG u z)
  refine ⟨τG,
    fun u z => if hu : ((u : Kˣ) : K) ≠ 1 then (key u z hu).choose else 0,
    fun u z v => if hu : ((u : Kˣ) : K) ≠ 1 then (key u z hu).choose_spec.choose v else 0,
    1, hτG1, hτG2, ?_, ?_, ?_, one_pos, ?_⟩
  · intro u z hu
    simp only [dif_pos hu]
    exact (key u z hu).choose_spec.choose_spec.1
  · intro u z v hu
    simp only [dif_pos hu]
    exact (key u z hu).choose_spec.choose_spec.2.1 v
  · intro u z v hu
    simp only [dif_pos hu]
    exact (key u z hu).choose_spec.choose_spec.2.2.1 v
  · intro u z hu S W Wa WS hWa hWS hW1 hW0
    simp only [dif_pos hu] at hWa hWS ⊢
    rw [Complex.ofReal_one, one_mul]
    exact (key u z hu).choose_spec.choose_spec.2.2.2 S W Wa WS hWa hWS hW1 hW0

end
end S_AutomorphicForm_exists_torusFamily_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct
end P2MW
export P2MW.S_AutomorphicForm_exists_torusFamily_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct (solution)
