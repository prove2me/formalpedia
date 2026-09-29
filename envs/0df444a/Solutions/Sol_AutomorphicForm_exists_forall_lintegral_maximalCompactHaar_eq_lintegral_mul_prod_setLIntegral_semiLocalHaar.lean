-- Prove2me | solution 1 for AutomorphicForm.exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/0f756af7-7f4b-53aa-847a-43da9c60b103

import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

section CribSection
p2m_open "Measure MeasureTheory.Measure Filter Set TopologicalSpace AutomorphicForm"
open scoped Topology NNReal

namespace ArchcKProdCrib

section Generic

private theorem preimage_preimage_mul_inter {G P : Type*} [Group G] [Group P] (π : G →* P) (H : Subgroup G) {h : G}
    (hh : h ∈ H) (A : Set P) :
    π ⁻¹' ((fun x => π h * x) ⁻¹' A) ∩ (H : Set G) = (fun g => h * g) ⁻¹' (π ⁻¹' A ∩ (H : Set G)) := by
  ext g
  simp only [mem_inter_iff, mem_preimage, map_mul, SetLike.mem_coe]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, H.mul_mem hh h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := H.mul_mem (H.inv_mem hh) h2
    rwa [inv_mul_cancel_left] at this

variable {G P : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [MeasurableSpace P] [BorelSpace P]

private theorem isMulLeftInvariant_map_restrict (μ : Measure G) [μ.IsMulLeftInvariant] (π : G →* P)
    (hπ : Continuous π) (H : Subgroup G) (hsurj : ∀ p : P, ∃ h ∈ H, π h = p) :
    (Measure.map π (μ.restrict H)).IsMulLeftInvariant := by
  refine ⟨fun p => ?_⟩
  obtain ⟨h, hh, rfl⟩ := hsurj p
  have hπm : Measurable π := hπ.measurable
  ext A hA
  have hA' : MeasurableSet ((fun x => π h * x) ⁻¹' A) := measurable_const_mul _ hA
  rw [Measure.map_apply (measurable_const_mul _) hA, Measure.map_apply hπm hA', Measure.map_apply hπm hA,
    Measure.restrict_apply (hπm hA'), Measure.restrict_apply (hπm hA),
    preimage_preimage_mul_inter π H hh A, measure_preimage_mul]

private theorem isFiniteMeasureOnCompacts_map_restrict [T2Space P] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (π : G →* P)
    (hπ : Continuous π) (H : Subgroup G) (H₀ : Set G) (hH₀ : IsCompact H₀)
    (U : Subgroup P) (hUo : IsOpen (U : Set P)) (hU : ∀ g ∈ H, π g ∈ U → g ∈ H₀)
    (hsurj : ∀ p : P, ∃ h ∈ H, π h = p) :
    IsFiniteMeasureOnCompacts (Measure.map π (μ.restrict H)) := by
  have hπm : Measurable π := hπ.measurable
  refine ⟨fun C hC => ?_⟩

  obtain ⟨t, hcov⟩ := hC.elim_finite_subcover (fun p : P => (fun x => p * x) '' (U : Set P))
    (fun p => (Homeomorph.mulLeft p).isOpenMap _ hUo)
    (fun p hp => mem_iUnion.2 ⟨p, ⟨1, U.one_mem, mul_one p⟩⟩)
  rw [Measure.map_apply hπm hC.measurableSet, Measure.restrict_apply (hπm hC.measurableSet)]

  have hpiece : ∀ p : P, ∃ h : G, π ⁻¹' ((fun x => p * x) '' (U : Set P)) ∩ (H : Set G) ⊆
      (fun g => h * g) '' H₀ := by
    intro p
    obtain ⟨h, hh, rfl⟩ := hsurj p
    refine ⟨h, fun g hg => ?_⟩
    obtain ⟨⟨u, hu, hgu⟩, hgH⟩ := hg
    refine ⟨h⁻¹ * g, hU _ (H.mul_mem (H.inv_mem hh) hgH) ?_, mul_inv_cancel_left h g⟩
    have : π (h⁻¹ * g) = u := by
      rw [map_mul, map_inv, ← hgu, inv_mul_cancel_left]
    rw [this]
    exact hu
  choose hsel hsub using hpiece
  calc μ (π ⁻¹' C ∩ (H : Set G))
      ≤ μ (⋃ p ∈ t, (fun g => hsel p * g) '' H₀) := by
        refine measure_mono fun g hg => ?_
        obtain ⟨hgC, hgH⟩ := hg
        obtain ⟨p, hp, hgp⟩ := mem_iUnion₂.1 (hcov hgC)
        exact mem_iUnion₂.2 ⟨p, hp, hsub p ⟨hgp, hgH⟩⟩
    _ ≤ ∑ p ∈ t, μ ((fun g => hsel p * g) '' H₀) := measure_biUnion_finset_le t _
    _ < ⊤ := by
        refine ENNReal.sum_lt_top.2 fun p _ => ?_
        exact (hH₀.image (continuous_const_mul _)).measure_lt_top

omit [IsTopologicalGroup G] [IsTopologicalGroup P] in

private theorem isOpenPosMeasure_map_restrict (μ : Measure G) [μ.IsOpenPosMeasure] (π : G →* P) (hπ : Continuous π)
    (H : Subgroup G) (hHo : IsOpen (H : Set G)) (hsurj : ∀ p : P, ∃ h ∈ H, π h = p) :
    (Measure.map π (μ.restrict H)).IsOpenPosMeasure := by
  have hπm : Measurable π := hπ.measurable
  refine ⟨fun O hO hOne => ?_⟩
  obtain ⟨p, hp⟩ := hOne
  obtain ⟨h, hh, rfl⟩ := hsurj p
  rw [Measure.map_apply hπm hO.measurableSet, Measure.restrict_apply (hπm hO.measurableSet)]
  exact ((hO.preimage hπ).inter hHo).measure_ne_zero μ ⟨h, hp, hh⟩

private theorem isHaarMeasure_map_restrict [T2Space P] (μ : Measure G) [μ.IsHaarMeasure] (π : G →* P)
    (hπ : Continuous π) (H : Subgroup G) (hHo : IsOpen (H : Set G)) (H₀ : Set G) (hH₀ : IsCompact H₀)
    (U : Subgroup P) (hUo : IsOpen (U : Set P)) (hU : ∀ g ∈ H, π g ∈ U → g ∈ H₀)
    (hsurj : ∀ p : P, ∃ h ∈ H, π h = p) :
    (Measure.map π (μ.restrict H)).IsHaarMeasure :=
  have h1 := isFiniteMeasureOnCompacts_map_restrict μ π hπ H H₀ hH₀ U hUo hU hsurj
  have h2 := isMulLeftInvariant_map_restrict μ π hπ H hsurj
  have h3 := isOpenPosMeasure_map_restrict μ π hπ H hHo hsurj
  @Measure.IsHaarMeasure.mk _ _ _ _ _ h1 h2 h3

private theorem exists_pos_setIntegral_comp_eq_mul_integral [T2Space P] [LocallyCompactSpace P]
    [SecondCountableTopology P] (μ : Measure G) [μ.IsHaarMeasure] (ν : Measure P) [ν.IsHaarMeasure]
    (π : G →* P) (hπ : Continuous π) (H : Subgroup G) (hHo : IsOpen (H : Set G)) (H₀ : Set G)
    (hH₀ : IsCompact H₀) (U : Subgroup P) (hUo : IsOpen (U : Set P)) (hU : ∀ g ∈ H, π g ∈ U → g ∈ H₀)
    (hsurj : ∀ p : P, ∃ h ∈ H, π h = p) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : P → ℂ, Continuous f →
      ∫ g in (H : Set G), f (π g) ∂μ = (c : ℂ) * ∫ p, f p ∂ν := by
  haveI := isHaarMeasure_map_restrict μ π hπ H hHo H₀ hH₀ U hUo hU hsurj
  have hπm : Measurable π := hπ.measurable
  refine ⟨(haarScalarFactor (Measure.map π (μ.restrict H)) ν : ℝ),
    NNReal.coe_pos.2 (haarScalarFactor_pos_of_isHaarMeasure _ _), fun f hf => ?_⟩
  have hmap : ∫ g in (H : Set G), f (π g) ∂μ = ∫ p, f p ∂(Measure.map π (μ.restrict H)) :=
    (integral_map hπm.aemeasurable hf.aestronglyMeasurable).symm
  have hint : ∫ p, f p ∂(Measure.map π (μ.restrict H)) =
      ∫ p, f p ∂(haarScalarFactor (Measure.map π (μ.restrict H)) ν • ν) := by
    rw [← isMulLeftInvariant_eq_smul (Measure.map π (μ.restrict H)) ν]
  rw [hmap, hint, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

end Generic

noncomputable section

open scoped Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

private abbrev SemiLoc (v : HeightOneSpectrum (𝓞 K)) : Type := L ⊗[K] v.adicCompletion K

private abbrev bcE (v : HeightOneSpectrum (𝓞 K)) :
    SemiLoc K L v ≃ₐ[L] Π w : v.Extension (𝓞 L), w.1.adicCompletion L :=
  HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v

private def evalAt
    (w : HeightOneSpectrum (𝓞 L)) : SemiLoc K L (HeightOneSpectrum.under (𝓞 K) w) →+* w.adicCompletion L :=
  (Pi.evalRingHom (fun w' : (HeightOneSpectrum.under (𝓞 K) w).Extension (𝓞 L) => w'.1.adicCompletion L)
      ⟨w, rfl⟩).comp (bcE K L (HeightOneSpectrum.under (𝓞 K) w)).toRingEquiv.toRingHom

variable {K L S} in

private def liftFun (x : ∀ v : S, SemiLoc K L v) (d : ℕ) (w : HeightOneSpectrum (𝓞 L)) : w.adicCompletion L :=
  if hv : HeightOneSpectrum.under (𝓞 K) w ∈ S then evalAt K L w (x ⟨_, hv⟩) else d

variable {K L S} in
private theorem liftFun_of_not_mem (x : ∀ v : S, SemiLoc K L v) (d : ℕ) {w : HeightOneSpectrum (𝓞 L)}
    (hw : HeightOneSpectrum.under (𝓞 K) w ∉ S) : liftFun x d w = d := by
  simp only [liftFun, dif_neg hw]

variable {K L S} in

private theorem liftFun_of_under_eq (x : ∀ v : S, SemiLoc K L v) (d : ℕ) (w : HeightOneSpectrum (𝓞 L))
    (v : HeightOneSpectrum (𝓞 K)) (hvS : v ∈ S) (h : HeightOneSpectrum.under (𝓞 K) w = v) :
    liftFun x d w = bcE K L v (x ⟨v, hvS⟩) ⟨w, h⟩ := by
  subst h
  simp only [liftFun, dif_pos hvS]
  rfl

variable {K L} in

private theorem finite_setOf_under_mem
    : {w : HeightOneSpectrum (𝓞 L) | HeightOneSpectrum.under (𝓞 K) w ∈ S}.Finite := by
  refine (S.finite_toSet.preimage' fun v _ => ?_)
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  exact (Set.finite_range fun w' : v.Extension (𝓞 L) => (w'.1 : HeightOneSpectrum (𝓞 L))).subset
    fun w hw => ⟨⟨w, hw⟩, rfl⟩

variable {K L S} in
private theorem liftFun_eventually (x : ∀ v : S, SemiLoc K L v) (d : ℕ) :
    ∀ᶠ w in Filter.cofinite, liftFun x d w ∈ (w.adicCompletionIntegers L : Set (w.adicCompletion L)) := by
  rw [Filter.eventually_cofinite]
  refine (finite_setOf_under_mem S).subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hv
  exact hw (by rw [liftFun_of_not_mem x d hv]; exact natCast_mem _ d)

variable {K L S} in

private def liftEntry (x : ∀ v : S, SemiLoc K L v) (d : ℕ) : FiniteAdeleRing (𝓞 L) L :=
  ⟨liftFun x d, liftFun_eventually x d⟩

variable {K L S} in
@[scoped simp] private theorem liftEntry_apply (x : ∀ v : S, SemiLoc K L v) (d : ℕ) (w : HeightOneSpectrum (𝓞 L)) :
    liftEntry x d w = liftFun x d w := rfl

variable {K L} in
private theorem semiLocalEval_apply (v : HeightOneSpectrum (𝓞 K)) (a : FiniteAdeleRing (𝓞 L) L) :
    semiLocalEval K L v a = (bcE K L v).symm (fun w' => a w'.1) := rfl

variable {K L S} in

private theorem semiLocalEval_liftEntry (x : ∀ v : S, SemiLoc K L v) (d : ℕ) (v : S) :
    semiLocalEval K L v (liftEntry x d) = x v := by
  rw [semiLocalEval_apply]
  have : (fun w' : (v : HeightOneSpectrum (𝓞 K)).Extension (𝓞 L) => liftEntry x d w'.1) = bcE K L v (x v) := by
    funext w'
    obtain ⟨w', hw'⟩ := w'
    obtain ⟨v, hvS⟩ := v
    rw [liftEntry_apply, liftFun_of_under_eq x d w' v hvS hw']
  rw [this, AlgEquiv.symm_apply_apply]

variable {K L S} in

private theorem semiLocalEval_liftEntry_of_not_mem (x : ∀ v : S, SemiLoc K L v) (d : ℕ)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) : semiLocalEval K L v (liftEntry x d) = d := by
  rw [semiLocalEval_apply]
  have : (fun w' : v.Extension (𝓞 L) => liftEntry x d w'.1) =
      (d : Π w' : v.Extension (𝓞 L), w'.1.adicCompletion L) := by
    funext w'
    have hw : HeightOneSpectrum.under (𝓞 K) w'.1 ∉ S := by rw [w'.2]; exact hv
    rw [liftEntry_apply, liftFun_of_not_mem x d hw]
    rfl
  rw [this, map_natCast]

private def liftMat (m : ∀ v : S, Matrix (Fin 2) (Fin 2) (SemiLoc K L v)) :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
  Matrix.of fun i j => liftEntry (fun v => m v i j) (if i = j then 1 else 0)

variable {K L S} in
private theorem semiLocalEval_map_liftMat (m : ∀ v : S, Matrix (Fin 2) (Fin 2) (SemiLoc K L v)) (v : S) :
    (liftMat K L S m).map (semiLocalEval K L v) = m v := by
  ext i j
  simp only [Matrix.map_apply, liftMat, Matrix.of_apply, semiLocalEval_liftEntry]

variable {K L S} in
private theorem semiLocalEval_map_liftMat_of_not_mem (m : ∀ v : S, Matrix (Fin 2) (Fin 2) (SemiLoc K L v))
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) : (liftMat K L S m).map (semiLocalEval K L v) = 1 := by
  ext i j
  simp only [Matrix.map_apply, liftMat, Matrix.of_apply, semiLocalEval_liftEntry_of_not_mem _ _ hv,
    Matrix.one_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

variable {K L} in

private theorem matrix_ext_of_semiLocalEval {A B : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)}
    (h : ∀ v : HeightOneSpectrum (𝓞 K), A.map (semiLocalEval K L v) = B.map (semiLocalEval K L v)) :
    A = B := by
  ext i j w : 2
  have hij := congrFun (congrFun (h (HeightOneSpectrum.under (𝓞 K) w)) i) j
  simp only [Matrix.map_apply, semiLocalEval_apply] at hij
  exact congrFun ((bcE K L (HeightOneSpectrum.under (𝓞 K) w)).symm.injective hij) ⟨w, rfl⟩

private def liftMatHom
    : (∀ v : S, Matrix (Fin 2) (Fin 2) (SemiLoc K L v)) →* Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)
    where
  toFun := liftMat K L S
  map_one' := matrix_ext_of_semiLocalEval fun v => by
    by_cases hv : v ∈ S
    · rw [semiLocalEval_map_liftMat _ ⟨v, hv⟩, Pi.one_apply, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [semiLocalEval_map_liftMat_of_not_mem _ hv, Matrix.map_one _ (map_zero _) (map_one _)]
  map_mul' m n := matrix_ext_of_semiLocalEval fun v => by
    by_cases hv : v ∈ S
    · rw [Matrix.map_mul, semiLocalEval_map_liftMat _ ⟨v, hv⟩, semiLocalEval_map_liftMat _ ⟨v, hv⟩,
        semiLocalEval_map_liftMat _ ⟨v, hv⟩, Pi.mul_apply]
    · rw [Matrix.map_mul, semiLocalEval_map_liftMat_of_not_mem _ hv, semiLocalEval_map_liftMat_of_not_mem _ hv,
        semiLocalEval_map_liftMat_of_not_mem _ hv, one_mul]

private def liftGL : (∀ v : S, GL (Fin 2) (SemiLoc K L v)) →* GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
  (Units.map (liftMatHom K L S)).comp MulEquiv.piUnits.symm.toMonoidHom

variable {K L S} in
private theorem val_liftGL (t : ∀ v : S, GL (Fin 2) (SemiLoc K L v)) :
    ((liftGL K L S t : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)) =
      liftMat K L S fun v => (t v : Matrix (Fin 2) (Fin 2) (SemiLoc K L v)) := rfl

variable {K L S} in

private theorem semiLocalComponent_liftGL (t : ∀ v : S, GL (Fin 2) (SemiLoc K L v)) (v : S) :
    semiLocalComponent K L v (liftGL K L S t) = t v := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [semiLocalComponent, Matrix.GeneralLinearGroup.map_apply]
  show semiLocalEval K L v (liftMat K L S (fun v => (t v : Matrix (Fin 2) (Fin 2) (SemiLoc K L v))) i j) = _
  rw [liftMat, Matrix.of_apply, semiLocalEval_liftEntry]

variable {K L S} in

private theorem semiLocalComponent_liftGL_of_not_mem (t : ∀ v : S, GL (Fin 2) (SemiLoc K L v))
    {v : HeightOneSpectrum (𝓞 K)} (hv : v ∉ S) : semiLocalComponent K L v (liftGL K L S t) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [semiLocalComponent, Matrix.GeneralLinearGroup.map_apply, Units.val_one]
  show semiLocalEval K L v (liftMat K L S (fun v => (t v : Matrix (Fin 2) (Fin 2) (SemiLoc K L v))) i j) = _
  rw [liftMat, Matrix.of_apply, semiLocalEval_liftEntry_of_not_mem _ _ hv, Matrix.one_apply, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

variable {K L S} in

private theorem exists_integralOutside_semiLocalComponent_eq (t : ∀ v : S, GL (Fin 2) (SemiLoc K L v)) :
    ∃ h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L),
      (∀ v ∉ S, semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v) ∧
        ∀ v : S, semiLocalComponent K L v h = t v :=
  ⟨liftGL K L S t,
    fun v hv => by rw [semiLocalComponent_liftGL_of_not_mem t hv]; exact one_mem_semiLocalIntegralSet K L v,
    semiLocalComponent_liftGL t⟩

end

section GLMap

variable {R S : Type} [CommRing R] [TopologicalSpace R] [CommRing S] [TopologicalSpace S]

private theorem continuous_generalLinearGroup_map (f : R →+* S) (hf : Continuous f) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) f) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hf
  · exact Units.continuous_coe_inv.matrix_map hf

end GLMap

section SemiLocal

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

private theorem continuous_semiLocalEval : Continuous (semiLocalEval K L v) :=
  (HeightOneSpectrum.adicCompletion.baseChangeContinuousAlgEquiv K L (𝓞 L) v).symm.continuous.comp
    (continuous_pi fun w : v.Extension (𝓞 L) => AdelicLevel.continuous_finAdeleEval (𝓞 L) L w.1)

private theorem continuous_semiLocalComponent : Continuous (semiLocalComponent K L v) :=
  continuous_generalLinearGroup_map (semiLocalEval K L v) (continuous_semiLocalEval K L v)

private theorem isClosed_semiLocalIntegralSet : IsClosed (semiLocalIntegralSet K L v) := by
  haveI := t2Space_tensorGL K L (v.adicCompletion K)
  exact (isCompact_semiLocalIntegralSet K L v).isClosed

private theorem isClosed_setOf_integralOutside (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsClosed {h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) |
      ∀ w ∉ S, semiLocalComponent K L w h ∈ semiLocalIntegralSet K L w} := by
  have : {h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) |
        ∀ w ∉ S, semiLocalComponent K L w h ∈ semiLocalIntegralSet K L w} =
      ⋂ w : HeightOneSpectrum (𝓞 K), ⋂ (_ : w ∉ S), semiLocalComponent K L w ⁻¹' semiLocalIntegralSet K L w := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [this]
  exact isClosed_iInter fun w => isClosed_iInter fun _ =>
    (isClosed_semiLocalIntegralSet K L w).preimage (continuous_semiLocalComponent K L w)

end SemiLocal

section IntegralClosure

variable {A : Type} [CommRing A]

private theorem integralMatrixSet_mul_mem {U : Set A} (hadd : ∀ a ∈ U, ∀ b ∈ U, a + b ∈ U)
    (hmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) {m n : Matrix (Fin 2) (Fin 2) A} (hm : m ∈ integralMatrixSet U)
    (hn : n ∈ integralMatrixSet U) : m * n ∈ integralMatrixSet U := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact hadd _ (hmul _ (hm i 0) _ (hn 0 j)) _ (hmul _ (hm i 1) _ (hn 1 j))

private theorem mul_mem_integralUnitsSet {U : Set A} (hadd : ∀ a ∈ U, ∀ b ∈ U, a + b ∈ U)
    (hmul : ∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) {g h : GL (Fin 2) A} (hg : g ∈ integralUnitsSet U)
    (hh : h ∈ integralUnitsSet U) : g * h ∈ integralUnitsSet U := by
  refine ⟨?_, ?_⟩
  · exact integralMatrixSet_mul_mem hadd hmul hg.1 hh.1
  · rw [mul_inv_rev]
    exact integralMatrixSet_mul_mem hadd hmul hh.2 hg.2

private theorem inv_mem_integralUnitsSet {U : Set A} {g : GL (Fin 2) A} (hg : g ∈ integralUnitsSet U) :
    g⁻¹ ∈ integralUnitsSet U := by
  refine ⟨hg.2, ?_⟩
  rw [inv_inv]
  exact hg.1

end IntegralClosure

section SemiLocalClosure

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

omit [NumberField L] in
private theorem semiLocalIntegers_add_mem {a b : L ⊗[K] v.adicCompletion K} (ha : a ∈ semiLocalIntegers K L v)
    (hb : b ∈ semiLocalIntegers K L v) : a + b ∈ semiLocalIntegers K L v := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x + y, map_add _ _ _⟩

omit [NumberField L] in
private theorem semiLocalIntegers_mul_mem {a b : L ⊗[K] v.adicCompletion K} (ha : a ∈ semiLocalIntegers K L v)
    (hb : b ∈ semiLocalIntegers K L v) : a * b ∈ semiLocalIntegers K L v := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x * y, map_mul _ _ _⟩

omit [NumberField L] in
private theorem mul_mem_semiLocalIntegralSet {g h : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ semiLocalIntegralSet K L v) (hh : h ∈ semiLocalIntegralSet K L v) :
    g * h ∈ semiLocalIntegralSet K L v :=
  mul_mem_integralUnitsSet (fun _ ha _ hb => semiLocalIntegers_add_mem K L v ha hb)
    (fun _ ha _ hb => semiLocalIntegers_mul_mem K L v ha hb) hg hh

omit [NumberField L] in
private theorem inv_mem_semiLocalIntegralSet {g : GL (Fin 2) (L ⊗[K] v.adicCompletion K)}
    (hg : g ∈ semiLocalIntegralSet K L v) : g⁻¹ ∈ semiLocalIntegralSet K L v :=
  inv_mem_integralUnitsSet hg

end SemiLocalClosure

noncomputable section

section Subgroups

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 K)))

private def integralSubgroup (v : HeightOneSpectrum (𝓞 K)) : Subgroup (GL (Fin 2) (SemiLoc K L v)) where
  carrier := semiLocalIntegralSet K L v
  mul_mem' := fun ha hb => mul_mem_semiLocalIntegralSet K L v ha hb
  one_mem' := one_mem_semiLocalIntegralSet K L v
  inv_mem' := fun ha => inv_mem_semiLocalIntegralSet K L v ha

private def integralOutside : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) where
  carrier := {h | ∀ v ∉ S, semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v}
  mul_mem' := fun {a b} ha hb v hv => by
    rw [Set.mem_setOf_eq] at ha hb
    rw [map_mul]
    exact mul_mem_semiLocalIntegralSet K L v (ha v hv) (hb v hv)
  one_mem' := fun v _ => by rw [map_one]; exact one_mem_semiLocalIntegralSet K L v
  inv_mem' := fun {a} ha v hv => by
    rw [Set.mem_setOf_eq] at ha
    rw [map_inv]
    exact inv_mem_semiLocalIntegralSet K L v (ha v hv)

private def piComponent : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) →* ∀ v : S, GL (Fin 2) (SemiLoc K L v) :=
  MonoidHom.pi fun v => semiLocalComponent K L (v : HeightOneSpectrum (𝓞 K))

variable {K L S} in
@[scoped simp] private theorem piComponent_apply (g : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (v : S) :
    piComponent K L S g v = semiLocalComponent K L v g := rfl

private theorem continuous_piComponent : Continuous (piComponent K L S) :=
  continuous_pi fun v => continuous_semiLocalComponent K L (v : HeightOneSpectrum (𝓞 K))

variable {K L} in
private theorem semiLocalHomeomorph_apply (v : HeightOneSpectrum (𝓞 K)) (a : SemiLoc K L v) :
    semiLocalHomeomorph K L v a = bcE K L v a := rfl

variable {K L} in

private theorem semiLocalEval_mem_semiLocalIntegers_iff (v : HeightOneSpectrum (𝓞 K)) (a : FiniteAdeleRing (𝓞 L) L) :
    semiLocalEval K L v a ∈ semiLocalIntegers K L v ↔
      ∀ w' : v.Extension (𝓞 L), a w'.1 ∈ (w'.1.adicCompletionIntegers L : Set (w'.1.adicCompletion L)) := by
  rw [semiLocalIntegers_eq_preimage, Set.mem_preimage, semiLocalHomeomorph_apply, semiLocalEval_apply,
    AlgEquiv.apply_symm_apply, piIntegers, Set.mem_univ_pi]

variable {K L} in

private theorem forall_semiLocalComponent_mem_iff (h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    (∀ v : HeightOneSpectrum (𝓞 K), semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v) ↔
      h ∈ AdelicLevel.finiteIntegralGL2 (𝓞 L) L := by
  rw [AdelicLevel.mem_finiteIntegralGL2_iff]
  simp only [semiLocalIntegralSet, mem_integralUnitsSet, ← map_inv, semiLocalComponent,
    Matrix.GeneralLinearGroup.map_apply, semiLocalEval_mem_semiLocalIntegers_iff, AdelicLevel.integralFiniteAdeles,
    Set.mem_setOf_eq]
  constructor
  · intro H
    exact ⟨fun i j w => (H (HeightOneSpectrum.under (𝓞 K) w)).1 i j ⟨w, rfl⟩,
      fun i j w => (H (HeightOneSpectrum.under (𝓞 K) w)).2 i j ⟨w, rfl⟩⟩
  · rintro ⟨H1, H2⟩ v
    exact ⟨fun i j (w' : v.Extension (𝓞 L)) => H1 i j w'.1, fun i j (w' : v.Extension (𝓞 L)) => H2 i j w'.1⟩

private theorem isOpen_integralOutside
    : IsOpen (integralOutside K L S : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L))) := by
  refine Subgroup.isOpen_mono (H₁ := AdelicLevel.finiteIntegralGL2 (𝓞 L) L) ?_
    (AdelicLevel.isOpen_finiteLevelZero (𝓞 L) L top_ne_bot)
  intro h hh v _
  exact (forall_semiLocalComponent_mem_iff h).2 hh v

private theorem isCompact_setOf_forall_mem :
    IsCompact {h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) |
      ∀ v : HeightOneSpectrum (𝓞 K), semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v} := by
  have : {h : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) |
      ∀ v : HeightOneSpectrum (𝓞 K), semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v} =
      (AdelicLevel.finiteIntegralGL2 (𝓞 L) L : Set _) := by
    ext h
    exact forall_semiLocalComponent_mem_iff h
  rw [this]
  exact AdelicLevel.isCompact_finiteLevelZero (𝓞 L) L ⊤

private theorem isOpen_piIntegralSubgroup :
    IsOpen ((Subgroup.pi Set.univ fun v : S => integralSubgroup K L (v : HeightOneSpectrum (𝓞 K))) :
      Set (∀ v : S, GL (Fin 2) (SemiLoc K L v))) := by
  rw [Subgroup.coe_pi]
  exact isOpen_set_pi Set.finite_univ fun v _ => isOpen_semiLocalIntegralSet K L (v : HeightOneSpectrum (𝓞 K))

end Subgroups

end

section Instances

private theorem secondCountableTopology_gl (R : Type) [CommRing R] [TopologicalSpace R] [SecondCountableTopology R] :
    SecondCountableTopology (GL (Fin 2) R) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → R))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) R)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph : Matrix (Fin 2) (Fin 2) R ≃ₜ (Matrix (Fin 2) (Fin 2) R)ᵐᵒᵖ).symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

private theorem secondCountableTopology_semiLocGL (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) : SecondCountableTopology (GL (Fin 2) (SemiLoc K L v)) := by
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  haveI : SecondCountableTopology (SemiLoc K L v) := (semiLocalHomeomorph K L v).secondCountableTopology
  exact secondCountableTopology_gl (SemiLoc K L v)

end Instances

end ArchcKProdCrib
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar.ArchcKProdCrib"

end CribSection
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar.ArchcKProdCrib"

namespace ArchcKProd

open ArchcKProdCrib

noncomputable section

open scoped Classical

section Lift1

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

def lift1Fun (x : L ⊗[K] v.adicCompletion K) (d : ℕ) (w : HeightOneSpectrum (𝓞 L)) : w.adicCompletion L :=
  if h : HeightOneSpectrum.under (𝓞 K) w = v then
    HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x ⟨w, h⟩
  else d

variable {K L v} in
theorem lift1Fun_of_ne (x : L ⊗[K] v.adicCompletion K) (d : ℕ) {w : HeightOneSpectrum (𝓞 L)}
    (hw : HeightOneSpectrum.under (𝓞 K) w ≠ v) : lift1Fun K L v x d w = d := by
  simp only [lift1Fun, dif_neg hw]

variable {K L v} in
theorem lift1Fun_of_eq (x : L ⊗[K] v.adicCompletion K) (d : ℕ) (w : HeightOneSpectrum (𝓞 L))
    (h : HeightOneSpectrum.under (𝓞 K) w = v) :
    lift1Fun K L v x d w = HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x ⟨w, h⟩ := by
  simp only [lift1Fun, dif_pos h]

variable {K L} in
theorem finite_setOf_under_eq :
    {w : HeightOneSpectrum (𝓞 L) | HeightOneSpectrum.under (𝓞 K) w = v}.Finite := by
  haveI := HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
  exact (Set.finite_range fun w' : v.Extension (𝓞 L) => (w'.1 : HeightOneSpectrum (𝓞 L))).subset
    fun w hw => ⟨⟨w, hw⟩, rfl⟩

variable {K L v} in
theorem lift1Fun_eventually (x : L ⊗[K] v.adicCompletion K) (d : ℕ) :
    ∀ᶠ w in Filter.cofinite, lift1Fun K L v x d w ∈ (w.adicCompletionIntegers L : Set (w.adicCompletion L)) := by
  rw [Filter.eventually_cofinite]
  refine (finite_setOf_under_eq (K := K) (L := L) v).subset fun w hw => ?_
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hv
  exact hw (by rw [lift1Fun_of_ne x d hv]; exact natCast_mem _ d)

variable {K L v} in

def lift1Entry (x : L ⊗[K] v.adicCompletion K) (d : ℕ) : FiniteAdeleRing (𝓞 L) L :=
  ⟨lift1Fun K L v x d, lift1Fun_eventually x d⟩

variable {K L v} in
@[scoped simp] theorem lift1Entry_apply (x : L ⊗[K] v.adicCompletion K) (d : ℕ) (w : HeightOneSpectrum (𝓞 L)) :
    lift1Entry x d w = lift1Fun K L v x d w := rfl

variable {K L} in
theorem semiLocalEval_apply' (v' : HeightOneSpectrum (𝓞 K)) (a : FiniteAdeleRing (𝓞 L) L) :
    semiLocalEval K L v' a =
      (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v').symm (fun w' => a w'.1) := rfl

variable {K L v} in
theorem semiLocalEval_lift1Entry (x : L ⊗[K] v.adicCompletion K) (d : ℕ) :
    semiLocalEval K L v (lift1Entry x d) = x := by
  rw [semiLocalEval_apply']
  have : (fun w' : v.Extension (𝓞 L) => lift1Entry x d w'.1) =
      HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v x := by
    funext w'
    obtain ⟨w', hw'⟩ := w'
    rw [lift1Entry_apply, lift1Fun_of_eq x d w' hw']
  rw [this, AlgEquiv.symm_apply_apply]

variable {K L v} in
theorem semiLocalEval_lift1Entry_of_ne (x : L ⊗[K] v.adicCompletion K) (d : ℕ)
    {v' : HeightOneSpectrum (𝓞 K)} (hv : v' ≠ v) : semiLocalEval K L v' (lift1Entry x d) = d := by
  rw [semiLocalEval_apply']
  have : (fun w' : v'.Extension (𝓞 L) => lift1Entry x d w'.1) =
      (d : Π w' : v'.Extension (𝓞 L), w'.1.adicCompletion L) := by
    funext w'
    have hw : HeightOneSpectrum.under (𝓞 K) w'.1 ≠ v := by rw [w'.2]; exact hv
    rw [lift1Entry_apply, lift1Fun_of_ne x d hw]
    rfl
  rw [this, map_natCast]

def lift1Mat (m : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
  Matrix.of fun i j => lift1Entry (m i j) (if i = j then 1 else 0)

variable {K L v} in
theorem semiLocalEval_map_lift1Mat (m : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    (lift1Mat K L v m).map (semiLocalEval K L v) = m := by
  ext i j
  simp only [Matrix.map_apply, lift1Mat, Matrix.of_apply, semiLocalEval_lift1Entry]

variable {K L v} in
theorem semiLocalEval_map_lift1Mat_of_ne (m : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K))
    {v' : HeightOneSpectrum (𝓞 K)} (hv : v' ≠ v) : (lift1Mat K L v m).map (semiLocalEval K L v') = 1 := by
  ext i j
  simp only [Matrix.map_apply, lift1Mat, Matrix.of_apply, semiLocalEval_lift1Entry_of_ne _ _ hv,
    Matrix.one_apply, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

def lift1MatHom : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K) →* Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 L) L)
    where
  toFun := lift1Mat K L v
  map_one' := ArchcKProdCrib.matrix_ext_of_semiLocalEval fun v' => by
    by_cases hv : v' = v
    · rw [hv, semiLocalEval_map_lift1Mat, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [semiLocalEval_map_lift1Mat_of_ne _ hv, Matrix.map_one _ (map_zero _) (map_one _)]
  map_mul' m n := ArchcKProdCrib.matrix_ext_of_semiLocalEval fun v' => by
    by_cases hv : v' = v
    · rw [hv, Matrix.map_mul, semiLocalEval_map_lift1Mat, semiLocalEval_map_lift1Mat, semiLocalEval_map_lift1Mat]
    · rw [Matrix.map_mul, semiLocalEval_map_lift1Mat_of_ne _ hv, semiLocalEval_map_lift1Mat_of_ne _ hv,
        semiLocalEval_map_lift1Mat_of_ne _ hv, one_mul]

def lift1GL : GL (Fin 2) (L ⊗[K] v.adicCompletion K) →* GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) :=
  Units.map (lift1MatHom K L v)

variable {K L v} in
theorem semiLocalComponent_lift1GL (b : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    semiLocalComponent K L v (lift1GL K L v b) = b := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [semiLocalComponent, Matrix.GeneralLinearGroup.map_apply]
  show semiLocalEval K L v (lift1Mat K L v (b : Matrix (Fin 2) (Fin 2) _) i j) = _
  rw [lift1Mat, Matrix.of_apply, semiLocalEval_lift1Entry]

variable {K L v} in
theorem semiLocalComponent_lift1GL_of_ne (b : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    {v' : HeightOneSpectrum (𝓞 K)} (hv : v' ≠ v) : semiLocalComponent K L v' (lift1GL K L v b) = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [semiLocalComponent, Matrix.GeneralLinearGroup.map_apply, Units.val_one]
  show semiLocalEval K L v' (lift1Mat K L v (b : Matrix (Fin 2) (Fin 2) _) i j) = _
  rw [lift1Mat, Matrix.of_apply, semiLocalEval_lift1Entry_of_ne _ _ hv, Matrix.one_apply, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

end Lift1
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar.ArchcKProdCrib"

section Embed

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K))

def embedAt (b : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : AdelicGL2 (𝓞 L) L :=
  AdelicDock.finEmbed (𝓞 L) L (lift1GL K L v b)

variable {K L v} in
theorem glArch_embedAt (b : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    glArch (𝓞 L) L (embedAt K L v b) = 1 :=
  AdelicDock.glArch_finEmbed (𝓞 L) L _

variable {K L v} in
theorem semiLocalComponent_glFin_embedAt (b : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    semiLocalComponent K L v (glFin (𝓞 L) L (embedAt K L v b)) = b := by
  rw [embedAt, AdelicDock.glFin_finEmbed, semiLocalComponent_lift1GL]

variable {K L v} in
theorem semiLocalComponent_glFin_embedAt_of_ne (b : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    {v' : HeightOneSpectrum (𝓞 K)} (hv : v' ≠ v) :
    semiLocalComponent K L v' (glFin (𝓞 L) L (embedAt K L v b)) = 1 := by
  rw [embedAt, AdelicDock.glFin_finEmbed, semiLocalComponent_lift1GL_of_ne b hv]

variable {K L v} in
theorem embedAt_mem (b : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hb : b ∈ semiLocalIntegralSet K L v) :
    embedAt K L v b ∈ adelicMaximalCompact L := by
  refine mem_adelicMaximalCompact_iff.mpr ⟨?_, fun w => ?_⟩
  · refine (ArchcKProdCrib.forall_semiLocalComponent_mem_iff (K := K) _).mp fun v' => ?_
    by_cases hv : v' = v
    · rw [hv, semiLocalComponent_glFin_embedAt]; exact hb
    · rw [semiLocalComponent_glFin_embedAt_of_ne b hv]; exact one_mem_semiLocalIntegralSet K L v'
  · rw [glArch_embedAt, map_one]
    exact AutomorphicForm.WindowedSiegel.isRowIsometry_one

end Embed
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar.ArchcKProdCrib"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar.ArchcKProdCrib"

end ArchcKProd
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar.ArchcKProdCrib P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar.ArchcKProd"

namespace ArchcKProd

noncomputable section

section RightInv

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

theorem isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure (μ : Measure G) [μ.IsHaarMeasure]
    [IsProbabilityMeasure μ] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have hmeas : Measurable fun x : G => x * g := measurable_mul_const g
  haveI : (Measure.map (· * g) μ).IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    rw [Measure.map_map (measurable_const_mul h) hmeas]
    have : ((fun x : G => h * x) ∘ fun x : G => x * g) = (fun x : G => x * g) ∘ fun x : G => h * x := by
      funext x; simp [mul_assoc]
    rw [this, ← Measure.map_map hmeas (measurable_const_mul h), map_mul_left_eq_self]
  haveI : IsProbabilityMeasure (Measure.map (· * g) μ) := Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace (Measure.map (· * g) μ) μ
  have h1 : (Measure.map (· * g) μ) Set.univ = 1 := measure_univ
  rw [h, Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at h1
  have hc : Measure.haarScalarFactor (Measure.map (· * g) μ) μ = 1 := by
    exact_mod_cast h1
  rw [hc, one_smul] at h
  exact h

end RightInv
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar.ArchcKProdCrib P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar.ArchcKProd"

section Main

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

set_option synthInstance.maxHeartbeats 400000 in

theorem setLIntegral_semiLocalHaar_mul_left (v : HeightOneSpectrum (𝓞 K))
    (c : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hc : c ∈ semiLocalIntegralSet K L v)
    (h : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ≥0∞) :
    ∫⁻ b in semiLocalIntegralSet K L v, h (c * b) ∂(semiLocalHaar K L v) =
      ∫⁻ b in semiLocalIntegralSet K L v, h b ∂(semiLocalHaar K L v) := by
  letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
  haveI hTG := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
  haveI hCM : ContinuousMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := hTG.toContinuousMul
  haveI : MeasurableMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := ContinuousMul.measurableMul
  haveI := isHaarMeasure_semiLocalHaar K L v
  have hU : MeasurableSet (semiLocalIntegralSet K L v) := (isOpen_semiLocalIntegralSet K L v).measurableSet
  rw [← lintegral_indicator hU, ← lintegral_indicator hU]
  have hind : (fun b => (semiLocalIntegralSet K L v).indicator (fun b => h (c * b)) b) =
      fun b => (semiLocalIntegralSet K L v).indicator h (c * b) := by
    funext b
    by_cases hb : b ∈ semiLocalIntegralSet K L v
    · rw [Set.indicator_of_mem hb,
        Set.indicator_of_mem (ArchcKProdCrib.mul_mem_semiLocalIntegralSet K L v hc hb)]
    · have hcb : c * b ∉ semiLocalIntegralSet K L v := fun hcb => hb (by
        have := ArchcKProdCrib.mul_mem_semiLocalIntegralSet K L v
          (ArchcKProdCrib.inv_mem_semiLocalIntegralSet K L v hc) hcb
        rwa [inv_mul_cancel_left] at this)
      rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hcb]
  rw [hind]
  exact lintegral_mul_left_eq_self _ c

set_option synthInstance.maxHeartbeats 400000 in

theorem core (S : Finset (HeightOneSpectrum (𝓞 K)))
    (g : adelicMaximalCompact L → ℝ≥0∞) (hg : Measurable g)
    (hginv : ∀ (k : adelicMaximalCompact L) (v : HeightOneSpectrum (𝓞 K))
      (b : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hb : b ∈ semiLocalIntegralSet K L v),
      g (k * ⟨embedAt K L v b, embedAt_mem b hb⟩) = g k)
    (f : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ≥0∞)
    (hf : ∀ v ∈ S, @Measurable _ _ (glBorelOf (L ⊗[K] v.adicCompletion K)) _ (f v)) :
    ∫⁻ k, g k * ∏ v ∈ S, f v (semiLocalComponent K L v (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)))
        ∂(maximalCompactHaar L) =
      (∫⁻ k, g k ∂(maximalCompactHaar L)) *
        ∏ v ∈ S, ∫⁻ y in semiLocalIntegralSet K L v, f v y ∂(semiLocalHaar K L v) := by
  classical
  haveI : (maximalCompactHaar L).IsMulRightInvariant :=
    isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure _
  induction S using Finset.induction_on generalizing g with
  | empty => simp
  | insert v S hvS ih =>

    letI instGL : MeasurableSpace (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := glBorelOf (L ⊗[K] v.adicCompletion K)
    haveI := borelSpace_glBorelOf (L ⊗[K] v.adicCompletion K)
    haveI hTG := isTopologicalGroup_tensorGL K L (v.adicCompletion K)
    haveI hCM : ContinuousMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := hTG.toContinuousMul
    haveI := locallyCompactSpace_tensorGL K L (v.adicCompletion K)
    haveI := t2Space_tensorGL K L (v.adicCompletion K)
    haveI := ArchcKProdCrib.secondCountableTopology_semiLocGL K L v
    haveI : MeasurableMul (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := ContinuousMul.measurableMul
    haveI : MeasurableMul₂ (GL (Fin 2) (L ⊗[K] v.adicCompletion K)) := ContinuousMul.measurableMul₂
    haveI := isHaarMeasure_semiLocalHaar K L v
    have hU : MeasurableSet (semiLocalIntegralSet K L v) := (isOpen_semiLocalIntegralSet K L v).measurableSet
    have hU1 : semiLocalHaar K L v (semiLocalIntegralSet K L v) = 1 := semiLocalHaar_semiLocalIntegralSet K L v

    set μ := maximalCompactHaar L with hμ
    set U := semiLocalIntegralSet K L v with hUdef
    set cpt : adelicMaximalCompact L → GL (Fin 2) (L ⊗[K] v.adicCompletion K) :=
      fun k => semiLocalComponent K L v (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) with hcpt
    have hcpt_meas : Measurable cpt :=
      ((ArchcKProdCrib.continuous_semiLocalComponent K L v).comp
        ((continuous_glFin (𝓞 L) L).comp continuous_subtype_val)).measurable
    have hcpt_mem : ∀ k : adelicMaximalCompact L, cpt k ∈ U := fun k =>
      (ArchcKProdCrib.forall_semiLocalComponent_mem_iff (K := K) _).mpr (glFin_mem_finiteIntegralGL2 k.2) v

    set P : adelicMaximalCompact L → ℝ≥0∞ :=
      fun k => ∏ v' ∈ S, f v' (semiLocalComponent K L v' (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L))) with hP
    have hf' : ∀ v' ∈ S, @Measurable _ _ (glBorelOf (L ⊗[K] v'.adicCompletion K)) _ (f v') :=
      fun v' hv' => hf v' (Finset.mem_insert_of_mem hv')
    have hfv : Measurable (f v) := hf v (Finset.mem_insert_self v S)
    have hP_meas : Measurable P := by
      refine Finset.measurable_prod S fun v' hv' => ?_
      letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] v'.adicCompletion K)) := glBorelOf (L ⊗[K] v'.adicCompletion K)
      haveI := borelSpace_glBorelOf (L ⊗[K] v'.adicCompletion K)
      exact (hf' v' hv').comp ((ArchcKProdCrib.continuous_semiLocalComponent K L v').comp
        ((continuous_glFin (𝓞 L) L).comp continuous_subtype_val)).measurable

    have hP_inv : ∀ (k : adelicMaximalCompact L) (b : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
        (hb : b ∈ U), P (k * ⟨embedAt K L v b, embedAt_mem b hb⟩) = P k := by
      intro k b hb
      simp only [hP]
      refine Finset.prod_congr rfl fun v' hv' => ?_
      have hne : v' ≠ v := fun h => hvS (h ▸ hv')
      simp only [Subgroup.coe_mul, map_mul, semiLocalComponent_glFin_embedAt_of_ne b hne, mul_one]
    have hcpt_mul : ∀ (k : adelicMaximalCompact L) (b : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
        (hb : b ∈ U), cpt (k * ⟨embedAt K L v b, embedAt_mem b hb⟩) = cpt k * b := by
      intro k b hb
      simp only [hcpt, Subgroup.coe_mul, map_mul, semiLocalComponent_glFin_embedAt]

    have hprod : ∀ k : adelicMaximalCompact L,
        ∏ v' ∈ insert v S, f v' (semiLocalComponent K L v' (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L))) =
          f v (cpt k) * P k := fun k => Finset.prod_insert hvS
    simp_rw [hprod]
    rw [Finset.prod_insert hvS]

    have hstep : ∀ b ∈ U, ∫⁻ k, g k * (f v (cpt k) * P k) ∂μ = ∫⁻ k, g k * (f v (cpt k * b) * P k) ∂μ := by
      intro b hb
      rw [← lintegral_mul_right_eq_self (fun k => g k * (f v (cpt k) * P k)) ⟨embedAt K L v b, embedAt_mem b hb⟩]
      refine lintegral_congr fun k => ?_
      rw [hginv k v b hb, hcpt_mul k b hb, hP_inv k b hb]
    have havg : ∫⁻ k, g k * (f v (cpt k) * P k) ∂μ =
        ∫⁻ b in U, ∫⁻ k, g k * (f v (cpt k * b) * P k) ∂μ ∂(semiLocalHaar K L v) := by
      rw [setLIntegral_congr_fun hU (fun b hb => (hstep b hb).symm), setLIntegral_const, hU1, mul_one]
    rw [havg]

    have hF : Measurable fun p : adelicMaximalCompact L × GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        g p.1 * (f v (cpt p.1 * p.2) * P p.1) := by
      refine (hg.comp measurable_fst).mul ((hfv.comp ?_).mul (hP_meas.comp measurable_fst))
      exact ((hcpt_meas.comp measurable_fst).mul measurable_snd)
    rw [lintegral_lintegral_swap (f := fun b k => g k * (f v (cpt k * b) * P k)) ((hF.comp measurable_swap).aemeasurable)]

    have hinner : ∀ k : adelicMaximalCompact L,
        ∫⁻ b in U, g k * (f v (cpt k * b) * P k) ∂(semiLocalHaar K L v) =
          g k * P k * ∫⁻ b in U, f v b ∂(semiLocalHaar K L v) := by
      intro k
      have : (fun b => g k * (f v (cpt k * b) * P k)) = fun b => g k * P k * f v (cpt k * b) := by
        funext b; ring
      have hm : Measurable fun b : GL (Fin 2) (L ⊗[K] v.adicCompletion K) => f v (cpt k * b) :=
        hfv.comp (measurable_const_mul _)
      rw [this, lintegral_const_mul _ hm, setLIntegral_semiLocalHaar_mul_left K L v (cpt k) (hcpt_mem k)]
    simp_rw [hinner]
    rw [lintegral_mul_const _ (hg.fun_mul hP_meas)]

    rw [ih g hg hginv hf']
    ring

end Main
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar.ArchcKProdCrib P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar.ArchcKProd"

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar.ArchcKProdCrib P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar.ArchcKProd"

end ArchcKProd
p2m_reactivate "P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar.ArchcKProdCrib P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar.ArchcKProd"

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    ∃ κ : @Measure (GL (Fin 2) (InfiniteAdeleRing L)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing L)),
      @IsProbabilityMeasure (GL (Fin 2) (InfiniteAdeleRing L)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing L)) κ ∧
      κ = @Measure.map (adelicMaximalCompact L) (GL (Fin 2) (InfiniteAdeleRing L)) _
            (AutomorphicForm.glBorelOf (InfiniteAdeleRing L))
            (fun k : adelicMaximalCompact L => glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) (maximalCompactHaar L) ∧
      ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (g : GL (Fin 2) (InfiniteAdeleRing L) → ℝ≥0∞)
        (f : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ≥0∞),
        @Measurable _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing L)) _ g →
        (∀ v ∈ S, @Measurable _ _ (AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)) _ (f v)) →
        ∫⁻ k, g (glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)) *
            ∏ v ∈ S, f v (AutomorphicForm.semiLocalComponent K L v (glFin (𝓞 L) L (k : AdelicGL2 (𝓞 L) L)))
          ∂(maximalCompactHaar L) =
        (∫⁻ x, g x ∂κ) *
          ∏ v ∈ S, ∫⁻ y in AutomorphicForm.semiLocalIntegralSet K L v, f v y ∂(AutomorphicForm.semiLocalHaar K L v) := by
  letI instA : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing L)) := glBorelOf (InfiniteAdeleRing L)
  haveI := borelSpace_glBorelOf (InfiniteAdeleRing L)
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 L) L
  have harch : Measurable fun k : adelicMaximalCompact L => glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L) :=
    ((continuous_glArch (𝓞 L) L).comp continuous_subtype_val).measurable
  refine ⟨Measure.map (fun k : adelicMaximalCompact L => glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L))
      (maximalCompactHaar L), Measure.isProbabilityMeasure_map harch.aemeasurable, rfl, fun S g f hg hf => ?_⟩
  rw [lintegral_map hg harch]
  exact ArchcKProd.core K L S (fun k => g (glArch (𝓞 L) L (k : AdelicGL2 (𝓞 L) L))) (hg.comp harch)
    (fun k v b hb => by
      simp only [Subgroup.coe_mul, map_mul, ArchcKProd.glArch_embedAt, mul_one]) f hf

end S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_lintegral_maximalCompactHaar_eq_lintegral_mul_prod_setLIntegral_semiLocalHaar (solution)
