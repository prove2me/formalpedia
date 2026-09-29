-- Prove2me | solution 1 for AutomorphicForm.exists_pos_setIntegral_prod_semiLocalComponent_eq_mul_prod_integral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/5e6c8d52-b7af-5f2e-8232-4facb8dc2ba1

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_exists_pos_setIntegral_prod_semiLocalComponent_eq_mul_prod_integral

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

p2m_open "Measure MeasureTheory.Measure Filter Set TopologicalSpace AutomorphicForm"
open scoped Topology NNReal ENNReal

namespace FiniteAdelicHaarSplit

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

end FiniteAdelicHaarSplit
p2m_reactivate "P2MW.S_AutomorphicForm_exists_pos_setIntegral_prod_semiLocalComponent_eq_mul_prod_integral.FiniteAdelicHaarSplit"

open AutomorphicForm FiniteAdelicHaarSplit in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (μf : @Measure (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) (glBorelOf (FiniteAdeleRing (𝓞 L) L)))
    (hμf : @Measure.IsHaarMeasure (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) _ _
      (glBorelOf (FiniteAdeleRing (𝓞 L) L)) μf)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ c : ℝ, 0 < c ∧
      ∀ F : (v : HeightOneSpectrum (𝓞 K)) → (GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        (∀ v ∈ S, Continuous (F v) ∧ HasCompactSupport (F v)) →
        ∫ h in {h | ∀ v ∉ S, semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v},
            ∏ v ∈ S, F v (semiLocalComponent K L v h) ∂μf =
          (c : ℂ) * ∏ v ∈ S, ∫ t, F v t ∂(semiLocalHaar K L v) := by
  classical
  letI mG : MeasurableSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) := glBorelOf _
  haveI : BorelSpace (GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) := borelSpace_glBorelOf _
  haveI : Measure.IsHaarMeasure μf := hμf
  letI mv : ∀ v : S, MeasurableSpace (GL (Fin 2) (SemiLoc K L v)) := fun v => glBorelOf _
  haveI : ∀ v : S, BorelSpace (GL (Fin 2) (SemiLoc K L v)) := fun v => borelSpace_glBorelOf _
  haveI : ∀ v : S, IsTopologicalGroup (GL (Fin 2) (SemiLoc K L v)) := fun v =>
    isTopologicalGroup_tensorGL K L _
  haveI : ∀ v : S, T2Space (GL (Fin 2) (SemiLoc K L v)) := fun v => t2Space_tensorGL K L _
  haveI : ∀ v : S, LocallyCompactSpace (GL (Fin 2) (SemiLoc K L v)) := fun v =>
    locallyCompactSpace_tensorGL K L _
  haveI : ∀ v : S, SecondCountableTopology (GL (Fin 2) (SemiLoc K L v)) := fun v =>
    secondCountableTopology_semiLocGL K L v
  haveI : ∀ v : S, Measure.IsHaarMeasure (semiLocalHaar K L (v : HeightOneSpectrum (𝓞 K))) := fun v =>
    isHaarMeasure_semiLocalHaar K L v
  haveI : ∀ v : S, ContinuousMul (GL (Fin 2) (SemiLoc K L v)) := fun v => IsTopologicalGroup.toContinuousMul
  haveI : ∀ v : S, MeasurableMul (GL (Fin 2) (SemiLoc K L v)) := fun v => ContinuousMul.measurableMul
  haveI : ∀ v : S, SigmaCompactSpace (GL (Fin 2) (SemiLoc K L v)) := fun v =>
    sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : ∀ v : S, SigmaFinite (semiLocalHaar K L (v : HeightOneSpectrum (𝓞 K))) := fun v =>
    Measure.IsHaarMeasure.sigmaFinite _
  haveI : IsTopologicalGroup (∀ v : S, GL (Fin 2) (SemiLoc K L v)) := Pi.topologicalGroup
  haveI : T2Space (∀ v : S, GL (Fin 2) (SemiLoc K L v)) := Pi.t2Space
  haveI : LocallyCompactSpace (∀ v : S, GL (Fin 2) (SemiLoc K L v)) := Pi.locallyCompactSpace_of_finite
  haveI : SecondCountableTopology (∀ v : S, GL (Fin 2) (SemiLoc K L v)) := inferInstance
  haveI : BorelSpace (∀ v : S, GL (Fin 2) (SemiLoc K L v)) := Pi.borelSpace
  haveI : Measure.IsHaarMeasure (Measure.pi fun v : S => semiLocalHaar K L (v : HeightOneSpectrum (𝓞 K))) :=
    Measure.pi.isHaarMeasure _
  obtain ⟨c, hc, hid⟩ := exists_pos_setIntegral_comp_eq_mul_integral μf
    (Measure.pi fun v : S => semiLocalHaar K L (v : HeightOneSpectrum (𝓞 K))) (piComponent K L S)
    (continuous_piComponent K L S) (integralOutside K L S) (isOpen_integralOutside K L S)
    {h | ∀ v : HeightOneSpectrum (𝓞 K), semiLocalComponent K L v h ∈ semiLocalIntegralSet K L v}
    (isCompact_setOf_forall_mem K L)
    (Subgroup.pi Set.univ fun v : S => integralSubgroup K L (v : HeightOneSpectrum (𝓞 K)))
    (isOpen_piIntegralSubgroup K L S)
    (fun g hg hgU v => by
      by_cases hv : v ∈ S
      · exact (Subgroup.mem_pi _).1 hgU ⟨v, hv⟩ (Set.mem_univ _)
      · exact hg v hv)
    (fun t => by
      obtain ⟨h, hout, hin⟩ := exists_integralOutside_semiLocalComponent_eq t
      exact ⟨h, hout, funext fun v => hin v⟩)
  refine ⟨c, hc, fun F hF => ?_⟩
  have hcont : Continuous fun p : (∀ v : S, GL (Fin 2) (SemiLoc K L v)) => ∏ v : S, F v (p v) :=
    continuous_finsetProd _ fun v _ => (hF v v.2).1.comp (continuous_apply v)
  have h1 := hid _ hcont
  have h2 : ∫ p, (∏ v : S, F v (p v)) ∂(Measure.pi fun v : S => semiLocalHaar K L (v : HeightOneSpectrum (𝓞 K))) =
      ∏ v : S, ∫ t, F v t ∂(semiLocalHaar K L v) :=
    integral_fintype_prod_eq_prod (fun (v : S) (t : GL (Fin 2) (SemiLoc K L v)) => F v t)
  have h3 : (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) => ∏ v : S, F v (piComponent K L S g v)) =
      fun g => ∏ v ∈ S, F v (semiLocalComponent K L v g) :=
    funext fun g => Finset.prod_coe_sort S fun v => F v (semiLocalComponent K L v g)
  rw [h2, Finset.prod_coe_sort S fun v => ∫ t, F v t ∂(semiLocalHaar K L v)] at h1
  rw [show (fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) =>
      (fun p : (∀ v : S, GL (Fin 2) (SemiLoc K L v)) => ∏ v : S, F v (p v)) (piComponent K L S g)) =
      fun g => ∏ v ∈ S, F v (semiLocalComponent K L v g) from h3] at h1
  exact h1

#print axioms solution

end S_AutomorphicForm_exists_pos_setIntegral_prod_semiLocalComponent_eq_mul_prod_integral
end P2MW
export P2MW.S_AutomorphicForm_exists_pos_setIntegral_prod_semiLocalComponent_eq_mul_prod_integral (solution)
