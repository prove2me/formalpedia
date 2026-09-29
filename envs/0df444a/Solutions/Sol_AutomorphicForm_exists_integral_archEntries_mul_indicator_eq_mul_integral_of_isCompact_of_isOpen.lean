-- Prove2me | solution 1 for AutomorphicForm.exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/acd27b5a-68ef-51bc-a083-17cc6d7d311b

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Ring.Units
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen

set_option autoImplicit false

noncomputable section

open NumberField AutomorphicForm MeasureTheory IsDedekindDomain
open MeasureTheory.Measure
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace ArchHaarComparison

open NumberField.AdelicLevel

variable (K : Type) [Field K] [NumberField K]

private noncomputable abbrev μ : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K)) := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K

private scoped instance instBorelGL : BorelSpace (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
  AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K

private scoped instance instHaarμ : (μ K).IsHaarMeasure := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

private scoped instance instLocallyCompactMatrixArch : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing K))

private scoped instance instLocallyCompactArch : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing K)) := inferInstance

private noncomputable scoped instance instMeasArch : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing K)) := borel _

private scoped instance instBorelArch : BorelSpace (GL (Fin 2) (InfiniteAdeleRing K)) := ⟨rfl⟩

private noncomputable def pairMat (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))
    (h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K) :=
  Matrix.of fun i j => (g i j, h i j)

private theorem pairMat_mul (g g' : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))
    (h h' : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    pairMat K (g * g') (h * h') = pairMat K g h * pairMat K g' h' := by
  ext i j : 2
  refine Prod.ext ?_ ?_ <;> simp only [pairMat, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> rfl

private theorem pairMat_one : pairMat K 1 1 = (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
  ext i j : 2
  by_cases hij : i = j <;> simp only [pairMat, Matrix.of_apply, Matrix.one_apply, hij, if_true, if_false] <;> rfl

private noncomputable def pair (g : GL (Fin 2) (InfiniteAdeleRing K)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    GL (Fin 2) (AdeleRing (𝓞 K) K) where
  val := pairMat K (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))
    (h : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
  inv := pairMat K (↑g⁻¹ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))
    (↑h⁻¹ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
  val_inv := by rw [← pairMat_mul, Units.mul_inv, Units.mul_inv, pairMat_one]
  inv_val := by rw [← pairMat_mul, Units.inv_mul, Units.inv_mul, pairMat_one]

private theorem glArch_pair (g : GL (Fin 2) (InfiniteAdeleRing K)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    glArch (𝓞 K) K (pair K g h) = g :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

private theorem glFin_pair (g : GL (Fin 2) (InfiniteAdeleRing K)) (h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    glFin (𝓞 K) K (pair K g h) = h :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

private theorem pair_glArch_glFin (x : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    pair K (glArch (𝓞 K) K x) (glFin (𝓞 K) K x) = x :=
  Matrix.GeneralLinearGroup.ext fun _ _ => rfl

private theorem continuous_pair :
    Continuous fun p : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => pair K p.1 p.2 := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · show Continuous fun p : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      pairMat K (p.1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))
        (p.2 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    exact continuous_pi fun i => continuous_pi fun j =>
      ((Units.continuous_val.comp continuous_fst).matrix_elem i j).prodMk
        ((Units.continuous_val.comp continuous_snd).matrix_elem i j)
  · show Continuous fun p : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) =>
      pairMat K (↑p.1⁻¹ : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))
        (↑p.2⁻¹ : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K))
    exact continuous_pi fun i => continuous_pi fun j =>
      ((Units.continuous_coe_inv.comp continuous_fst).matrix_elem i j).prodMk
        ((Units.continuous_coe_inv.comp continuous_snd).matrix_elem i j)

variable {K}

private noncomputable def levelSet (U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) :
    Set (GL (Fin 2) (AdeleRing (𝓞 K) K)) :=
  {x | glFin (𝓞 K) K x ∈ U'}

private theorem isOpen_levelSet {U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))}
    (hU'o : IsOpen (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) : IsOpen (levelSet U') :=
  hU'o.preimage (continuous_glFin (𝓞 K) K)

private theorem pair_mul_mem_levelSet_iff (U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
    (g : GL (Fin 2) (InfiniteAdeleRing K)) (x : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    pair K g 1 * x ∈ levelSet U' ↔ x ∈ levelSet U' := by
  simp only [levelSet, Set.mem_setOf_eq, map_mul, glFin_pair, one_mul]

private theorem measurable_glArch : Measurable (glArch (𝓞 K) K) := (continuous_glArch (𝓞 K) K).measurable

private noncomputable def ν (U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) :
    Measure (GL (Fin 2) (InfiniteAdeleRing K)) :=
  Measure.map (glArch (𝓞 K) K) ((μ K).restrict (levelSet U'))

private theorem ν_apply (U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
    {A : Set (GL (Fin 2) (InfiniteAdeleRing K))} (hA : MeasurableSet A) :
    ν U' A = μ K (glArch (𝓞 K) K ⁻¹' A ∩ levelSet U') := by
  rw [ν, map_apply measurable_glArch hA, restrict_apply (measurable_glArch hA)]

private theorem ν_isMulLeftInvariant (U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) :
    (ν U').IsMulLeftInvariant := by
  refine ⟨fun g => Measure.ext fun A hA => ?_⟩
  have hg : Measurable fun y : GL (Fin 2) (InfiniteAdeleRing K) => g * y :=
    (continuous_const.mul continuous_id).measurable
  rw [map_apply hg hA, ν_apply U' (hg hA), ν_apply U' hA]
  have hset : glArch (𝓞 K) K ⁻¹' ((fun y => g * y) ⁻¹' A) ∩ levelSet U' =
      (fun x => pair K g 1 * x) ⁻¹' (glArch (𝓞 K) K ⁻¹' A ∩ levelSet U') := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, map_mul, glArch_pair, pair_mul_mem_levelSet_iff]
  rw [hset, measure_preimage_mul]

private theorem ν_isFiniteMeasureOnCompacts {U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))}
    (hU'c : IsCompact (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) : IsFiniteMeasureOnCompacts (ν U') := by
  refine ⟨fun C hC => ?_⟩
  rw [ν_apply U' hC.measurableSet]
  have himage : glArch (𝓞 K) K ⁻¹' C ∩ levelSet U' ⊆
      (fun p : GL (Fin 2) (InfiniteAdeleRing K) × GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => pair K p.1 p.2) ''
        (C ×ˢ (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) := by
    rintro x ⟨hxC, hxU⟩
    exact ⟨(glArch (𝓞 K) K x, glFin (𝓞 K) K x), ⟨hxC, hxU⟩, pair_glArch_glFin K x⟩
  exact lt_of_le_of_lt (measure_mono himage) ((hC.prod hU'c).image (continuous_pair K)).measure_lt_top

private theorem ν_isOpenPosMeasure {U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))}
    (hU'o : IsOpen (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) : (ν U').IsOpenPosMeasure := by
  refine ⟨fun O hO hne => ?_⟩
  rw [ν_apply U' hO.measurableSet]
  obtain ⟨g, hg⟩ := hne
  refine ((hO.preimage (continuous_glArch (𝓞 K) K)).inter (isOpen_levelSet hU'o)).measure_ne_zero (μ K)
    ⟨pair K g 1, ?_⟩
  refine ⟨?_, ?_⟩
  · show glArch (𝓞 K) K (pair K g 1) ∈ O
    rw [glArch_pair]; exact hg
  · show glFin (𝓞 K) K (pair K g 1) ∈ U'
    rw [glFin_pair]; exact U'.one_mem

private theorem ν_isHaarMeasure {U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))}
    (hU'c : IsCompact (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))))
    (hU'o : IsOpen (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) : (ν U').IsHaarMeasure :=
  haveI := ν_isFiniteMeasureOnCompacts hU'c
  haveI := ν_isMulLeftInvariant U'
  haveI := ν_isOpenPosMeasure hU'o
  {}

private scoped instance countable_numberField : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private scoped instance secondCountable_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ v : InfinitePlace K, SecondCountableTopology v.Completion := by
    intro v
    haveI : Countable (WithAbs v.1) := (WithAbs.equiv v.1).toEquiv.injective.countable
    haveI : SecondCountableTopology v.1.Completion := UniformSpace.secondCountable_of_separable _
    exact (NumberField.InfinitePlace.Completion.isometryEquivCompletion v).toHomeomorph.secondCountableTopology
  exact inferInstanceAs <| SecondCountableTopology <| (v : InfinitePlace K) → v.Completion

private scoped instance secondCountable_glArch : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing K)) := by
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing K))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

variable (K)

section ClassicalPart

open scoped Classical

open _root_.NumberField.mixedEmbedding in

private theorem abs_algebraNorm (x : mixedSpace K) : |Algebra.norm ℝ x| = mixedEmbedding.norm x := by
  classical

  have h₁ : Algebra.norm ℝ x = (∏ v : {w : InfinitePlace K // w.IsReal}, x.1 v) *
      ∏ w : {w : InfinitePlace K // w.IsComplex}, Complex.normSq (x.2 w) := by
    rw [Algebra.norm_apply]
    have e : Algebra.lmul ℝ (mixedSpace K) x =
        (Algebra.lmul ℝ ({w : InfinitePlace K // w.IsReal} → ℝ) x.1).prodMap
          (Algebra.lmul ℝ ({w : InfinitePlace K // w.IsComplex} → ℂ) x.2) := by
      ext <;> rfl
    rw [e, LinearMap.det_prodMap]
    congr 1
    · have e₁ : Algebra.lmul ℝ ({w : InfinitePlace K // w.IsReal} → ℝ) x.1 =
          LinearMap.pi fun v => (Algebra.lmul ℝ ℝ (x.1 v)).comp (LinearMap.proj v) := by
        ext; rfl
      rw [e₁, LinearMap.det_pi]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [← Algebra.norm_apply, Algebra.norm_self]
      rfl
    · have e₂ : Algebra.lmul ℝ ({w : InfinitePlace K // w.IsComplex} → ℂ) x.2 =
          LinearMap.pi fun w => (Algebra.lmul ℝ ℂ (x.2 w)).comp (LinearMap.proj w) := by
        ext; rfl
      rw [e₂, LinearMap.det_pi]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [← Algebra.norm_apply, Algebra.norm_complex_apply]

  have h₂ : mixedEmbedding.norm x = (∏ v : {w : InfinitePlace K // w.IsReal}, |x.1 v|) *
      ∏ w : {w : InfinitePlace K // w.IsComplex}, ‖x.2 w‖ ^ 2 := by
    rw [mixedEmbedding.norm_apply, ← Fintype.prod_subtype_mul_prod_subtype InfinitePlace.IsReal]
    congr 1
    · refine Finset.prod_congr rfl fun v _ => ?_
      rw [normAtPlace_apply_of_isReal v.2, InfinitePlace.mult_isReal, pow_one, Real.norm_eq_abs]
    · refine Fintype.prod_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex) _ _
        fun w => ?_
      have hw : (w : InfinitePlace K).IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 w.2
      rw [normAtPlace_apply_of_isComplex hw]
      have hm := InfinitePlace.mult_isComplex ⟨(w : InfinitePlace K), hw⟩
      simp only at hm
      rw [hm]
      rfl
  rw [h₁, h₂, abs_mul, Finset.abs_prod, Finset.abs_prod]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Complex.normSq_eq_norm_sq, abs_of_nonneg (by positivity)]

private noncomputable abbrev EntrySpace : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K

private scoped instance instBorelRow : BorelSpace (Fin 2 → mixedEmbedding.mixedSpace K) := Pi.borelSpace

private scoped instance instBorelEntry : BorelSpace (EntrySpace K) := Pi.borelSpace

private scoped instance instBorelS : BorelSpace (mixedEmbedding.mixedSpace K) := Prod.borelSpace

private scoped instance instMeasurableAddS : MeasurableAdd (mixedEmbedding.mixedSpace K) := inferInstance

private scoped instance instAddHaarRow : (volume : Measure (Fin 2 → mixedEmbedding.mixedSpace K)).IsAddHaarMeasure :=
  MeasureTheory.Measure.pi.isAddHaarMeasure _

private scoped instance instAddHaarEntry : (volume : Measure (EntrySpace K)).IsAddHaarMeasure :=
  MeasureTheory.Measure.pi.isAddHaarMeasure _

private noncomputable def mulLeftLin (A : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) :
    EntrySpace K →ₗ[mixedEmbedding.mixedSpace K] EntrySpace K where
  toFun E := Matrix.of.symm (A * Matrix.of E)
  map_add' E F := Matrix.mul_add A (Matrix.of E) (Matrix.of F)
  map_smul' c E := Matrix.mul_smul A c (Matrix.of E)

omit [NumberField K] in
private theorem mulLeftLin_apply (A : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) (E : EntrySpace K)
    (i j : Fin 2) : mulLeftLin K A E i j = ∑ k, A i k * E k j := by
  simp [mulLeftLin, Matrix.mul_apply]

private noncomputable def swapIdx : EntrySpace K ≃ₗ[mixedEmbedding.mixedSpace K] EntrySpace K where
  toFun E j i := E i j
  invFun E j i := E i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit [NumberField K] in

private theorem det_mulLeftLin (A : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) :
    LinearMap.det (mulLeftLin K A) = A.det ^ 2 := by
  have e : mulLeftLin K A = ((swapIdx K).symm : EntrySpace K →ₗ[mixedEmbedding.mixedSpace K] EntrySpace K) ∘ₗ
      (LinearMap.pi fun j : Fin 2 => (Matrix.toLin' A).comp (LinearMap.proj j)) ∘ₗ
        ((swapIdx K).symm.symm : EntrySpace K →ₗ[mixedEmbedding.mixedSpace K] EntrySpace K) := by
    refine LinearMap.ext fun E => funext fun i => funext fun j => ?_
    simp [mulLeftLin_apply, swapIdx, Matrix.mulVec, dotProduct]
  rw [e, LinearMap.det_conj, LinearMap.det_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    LinearMap.det_toLin']

private noncomputable def mulLeftReal (A : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) :
    EntrySpace K →ₗ[ℝ] EntrySpace K :=
  (mulLeftLin K A).restrictScalars ℝ

omit [NumberField K] in
private theorem mulLeftReal_apply (A : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) (E : EntrySpace K) :
    mulLeftReal K A E = Matrix.of.symm (A * Matrix.of E) := rfl

private theorem abs_det_mulLeftReal (A : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) :
    |LinearMap.det (mulLeftReal K A)| = mixedEmbedding.norm A.det ^ 2 := by
  rw [mulLeftReal, LinearMap.det_restrictScalars, det_mulLeftLin, map_pow, abs_pow, abs_algebraNorm]

private theorem abs_det_mulLeftReal_diagonal (t : mixedEmbedding.mixedSpace K) :
    |LinearMap.det (mulLeftReal K (Matrix.diagonal ![t, 1]))| = mixedEmbedding.norm t ^ 2 := by
  rw [abs_det_mulLeftReal, Matrix.det_diagonal]
  simp

open scoped Classical in

private noncomputable def mixedInv (y : mixedEmbedding.mixedSpace K) : InfiniteAdeleRing K := fun v =>
  if hv : v.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩)
  else (InfinitePlace.Completion.ringEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.1 hv)).symm
    (y.2 ⟨v, InfinitePlace.not_isReal_iff_isComplex.1 hv⟩)

omit [NumberField K] in
private theorem continuous_mixedInv : Continuous (mixedInv K) := by
  classical
  refine continuous_pi fun v => ?_
  by_cases hv : v.IsReal
  · simp only [mixedInv, hv, dite_true]
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · simp only [mixedInv, hv, dite_false]
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.1 hv)).symm.continuous.comp ((continuous_apply _).comp continuous_snd)

omit [NumberField K] in
private theorem ringEquiv_mixedSpace_mixedInv (y : mixedEmbedding.mixedSpace K) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K (mixedInv K y) = y := by
  classical
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · have hw : (w : InfinitePlace K).IsReal := w.2
    simp only [mixedInv, hw, dite_true]
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal hw).apply_symm_apply (y.1 w)
  · have hw : ¬ (w : InfinitePlace K).IsReal := InfinitePlace.not_isReal_iff_isComplex.2 w.2
    simp only [mixedInv, hw, dite_false]
    exact (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.1 hw)).apply_symm_apply (y.2 w)

omit [NumberField K] in
private theorem continuous_ringEquiv_mixedSpace_symm :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  have h : ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm : mixedEmbedding.mixedSpace K → InfiniteAdeleRing K) =
      mixedInv K := by
    funext y
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm_apply_eq.2 (ringEquiv_mixedSpace_mixedInv K y).symm
  rw [h]
  exact continuous_mixedInv K

private noncomputable def toMixedGL : GL (Fin 2) (InfiniteAdeleRing K) →* GL (Fin 2) (mixedEmbedding.mixedSpace K) :=
  Matrix.GeneralLinearGroup.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom

private noncomputable def ofMixedGL : GL (Fin 2) (mixedEmbedding.mixedSpace K) →* GL (Fin 2) (InfiniteAdeleRing K) :=
  Matrix.GeneralLinearGroup.map (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom

omit [NumberField K] in
private theorem ofMixedGL_toMixedGL (g : GL (Fin 2) (InfiniteAdeleRing K)) : ofMixedGL K (toMixedGL K g) = g :=
  Matrix.GeneralLinearGroup.ext fun _ _ => (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm_apply_apply _

omit [NumberField K] in
private theorem toMixedGL_ofMixedGL (g : GL (Fin 2) (mixedEmbedding.mixedSpace K)) :
    toMixedGL K (ofMixedGL K g) = g :=
  Matrix.GeneralLinearGroup.ext fun _ _ => (InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply _

omit [NumberField K] in
private theorem continuous_toMixedGL : Continuous (toMixedGL K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_map Units.continuous_val (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace K)
  · exact Continuous.matrix_map Units.continuous_coe_inv (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace K)

omit [NumberField K] in
private theorem continuous_ofMixedGL : Continuous (ofMixedGL K) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_map Units.continuous_val (continuous_ringEquiv_mixedSpace_symm K)
  · exact Continuous.matrix_map Units.continuous_coe_inv (continuous_ringEquiv_mixedSpace_symm K)

omit [NumberField K] in
private theorem continuous_archEntries : Continuous (archEntries K) :=
  Units.continuous_val.comp (continuous_toMixedGL K)

private noncomputable def unitLocus : Set (EntrySpace K) := {E | IsUnit (Matrix.det (Matrix.of E))}

private theorem isOpen_unitLocus : IsOpen (unitLocus K) :=
  Units.isOpen.preimage ((continuous_id (X := Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K))).matrix_det)

omit [NumberField K] in
private theorem archEntries_mem_unitLocus (g : GL (Fin 2) (InfiniteAdeleRing K)) : archEntries K g ∈ unitLocus K :=
  (Matrix.isUnit_iff_isUnit_det _).1 (toMixedGL K g).isUnit

private noncomputable def locusUnit (E : unitLocus K) : GL (Fin 2) (mixedEmbedding.mixedSpace K) :=
  ((Matrix.isUnit_iff_isUnit_det (Matrix.of (E : EntrySpace K))).2 E.2).unit

private noncomputable def ofEntries (E : unitLocus K) : GL (Fin 2) (InfiniteAdeleRing K) := ofMixedGL K (locusUnit K E)

private theorem continuous_locusUnit : Continuous (locusUnit K) := by
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  have h : (fun E : unitLocus K => ((locusUnit K E)⁻¹ : GL (Fin 2) (mixedEmbedding.mixedSpace K)).val) =
      fun E : unitLocus K => (Matrix.of (E : EntrySpace K))⁻¹ :=
    funext fun E => ((Matrix.nonsing_inv_eq_ringInverse _).trans (Ring.inverse_unit (locusUnit K E))).symm
  rw [h]
  refine continuous_iff_continuousAt.2 fun E => ?_
  exact ContinuousAt.comp (x := E) (f := fun E : unitLocus K => Matrix.of (E : EntrySpace K))
    (continuousAt_matrix_inv _ (NormedRing.inverse_continuousAt E.2.unit)) continuous_subtype_val.continuousAt

private theorem continuous_ofEntries : Continuous (ofEntries K) :=
  (continuous_ofMixedGL K).comp (continuous_locusUnit K)

private noncomputable def locusHomeomorph : GL (Fin 2) (InfiniteAdeleRing K) ≃ₜ unitLocus K where
  toFun g := ⟨archEntries K g, archEntries_mem_unitLocus K g⟩
  invFun := ofEntries K
  left_inv g := (congrArg (ofMixedGL K) (Units.ext rfl : locusUnit K ⟨archEntries K g, archEntries_mem_unitLocus K g⟩ =
    toMixedGL K g)).trans (ofMixedGL_toMixedGL K g)
  right_inv E := Subtype.ext (by
    show Matrix.of.symm ((toMixedGL K (ofMixedGL K (locusUnit K E)) : GL (Fin 2) (mixedEmbedding.mixedSpace K)) :
      Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) = (E : EntrySpace K)
    rw [toMixedGL_ofMixedGL]
    rfl)
  continuous_toFun := (continuous_archEntries K).subtype_mk _
  continuous_invFun := continuous_ofEntries K

private theorem isOpenEmbedding_archEntries : Topology.IsOpenEmbedding (archEntries K) := by
  have h : archEntries K = Subtype.val ∘ locusHomeomorph K := rfl
  rw [h]
  exact (isOpen_unitLocus K).isOpenEmbedding_subtypeVal.comp (locusHomeomorph K).isOpenEmbedding

private theorem measurableEmbedding_archEntries : MeasurableEmbedding (archEntries K) :=
  (isOpenEmbedding_archEntries K).measurableEmbedding

private theorem range_archEntries : Set.range (archEntries K) = unitLocus K := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 (archEntries_mem_unitLocus K)) fun E hE => ?_
  exact ⟨ofEntries K ⟨E, hE⟩, congrArg Subtype.val ((locusHomeomorph K).apply_symm_apply ⟨E, hE⟩)⟩

omit [NumberField K] in

private theorem archEntries_mul (g h : GL (Fin 2) (InfiniteAdeleRing K)) :
    archEntries K (g * h) = mulLeftReal K (toMixedGL K g : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K))
      (archEntries K h) := by
  show Matrix.of.symm ((toMixedGL K (g * h) : GL (Fin 2) (mixedEmbedding.mixedSpace K)) :
      Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) = _
  rw [map_mul, mulLeftReal_apply, Units.val_mul]
  rfl

private noncomputable def wtN (E : EntrySpace K) : NNReal :=
  ⟨(mixedEmbedding.norm (Matrix.det (Matrix.of E)))⁻¹ ^ 2, by positivity⟩

private theorem coe_wtN (E : EntrySpace K) :
    (wtN K E : ℝ) = (mixedEmbedding.norm (Matrix.det (Matrix.of E)))⁻¹ ^ 2 := rfl

private theorem continuous_normDet :
    Continuous fun E : EntrySpace K => mixedEmbedding.norm (Matrix.det (Matrix.of E)) :=
  (mixedEmbedding.continuous_norm (K := K)).comp
    ((continuous_id (X := Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K))).matrix_det)

private theorem measurable_wtN : Measurable fun E : EntrySpace K => (wtN K E : ℝ≥0∞) :=
  measurable_coe_nnreal_ennreal.comp
    (Measurable.subtype_mk (((continuous_normDet K).measurable.inv).pow_const 2))

private theorem normDet_pos {E : EntrySpace K} (hE : E ∈ unitLocus K) :
    0 < mixedEmbedding.norm (Matrix.det (Matrix.of E)) :=
  lt_of_le_of_ne (mixedEmbedding.norm_nonneg _) (IsUnit.ne_zero (hE.map mixedEmbedding.norm)).symm

private theorem continuousOn_wtN : ContinuousOn (fun E : EntrySpace K => (wtN K E : ℝ)) (unitLocus K) := by
  simp only [coe_wtN]
  exact (((continuous_normDet K).continuousOn.inv₀ fun E hE => (normDet_pos K hE).ne').pow 2)

private theorem wtN_ne_zero {E : EntrySpace K} (hE : E ∈ unitLocus K) : (wtN K E : ℝ≥0∞) ≠ 0 := by
  rw [Ne, ENNReal.coe_eq_zero, ← NNReal.coe_eq_zero, coe_wtN]
  exact (pow_pos (inv_pos.2 (normDet_pos K hE)) 2).ne'

private theorem coe_wtN_mulLeftReal (A : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) (E : EntrySpace K) :
    (wtN K (mulLeftReal K A E) : ℝ) = (mixedEmbedding.norm A.det)⁻¹ ^ 2 * wtN K E := by
  simp only [coe_wtN, mulLeftReal_apply, Equiv.apply_symm_apply, Matrix.det_mul, map_mul, mul_inv, mul_pow]

private noncomputable def lebN : Measure (EntrySpace K) := volume.withDensity fun E => (wtN K E : ℝ≥0∞)

private theorem lebN_image_mulLeftReal (g : GL (Fin 2) (InfiniteAdeleRing K)) {B : Set (EntrySpace K)}
    (hB : MeasurableSet B) :
    lebN K (mulLeftReal K (toMixedGL K g : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) '' B) = lebN K B := by
  set A := (toMixedGL K g : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K))
  have hA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det _).1 (toMixedGL K g).isUnit
  have hN : mixedEmbedding.norm A.det ≠ 0 := (hA.map mixedEmbedding.norm).ne_zero
  have hinj : Function.Injective (mulLeftReal K A) := by
    refine Function.LeftInverse.injective
      (g := mulLeftReal K A⁻¹) fun E => ?_
    simp only [mulLeftReal_apply, Equiv.apply_symm_apply, ← Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul A hA, Matrix.one_mul]
    exact Equiv.symm_apply_apply _ _
  have hderiv : ∀ E ∈ B, HasFDerivWithinAt (mulLeftReal K A)
      (LinearMap.toContinuousLinearMap (mulLeftReal K A)) B E :=
    fun E _ => (LinearMap.toContinuousLinearMap (mulLeftReal K A)).hasFDerivAt.hasFDerivWithinAt
  unfold lebN
  rw [withDensity_apply' _ _, withDensity_apply' _ _,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hB hderiv hinj.injOn]
  refine lintegral_congr fun E => ?_
  simp only [ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, abs_det_mulLeftReal,
    ← ENNReal.ofReal_coe_nnreal, coe_wtN_mulLeftReal]
  rw [← ENNReal.ofReal_mul (by positivity), ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hN, one_pow, one_mul]

private noncomputable def lam : Measure (GL (Fin 2) (InfiniteAdeleRing K)) := Measure.comap (archEntries K) (lebN K)

private theorem lam_apply {A : Set (GL (Fin 2) (InfiniteAdeleRing K))} (hA : MeasurableSet A) :
    lam K A = lebN K (archEntries K '' A) :=
  Measure.comap_apply _ (measurableEmbedding_archEntries K).injective
    (fun _ hs => (measurableEmbedding_archEntries K).measurableSet_image.2 hs) _ hA

private theorem lam_isMulLeftInvariant : (lam K).IsMulLeftInvariant := by
  refine ⟨fun g => Measure.ext fun A hA => ?_⟩
  have hg : Measurable fun y : GL (Fin 2) (InfiniteAdeleRing K) => g * y :=
    (continuous_const.mul continuous_id).measurable
  rw [map_apply hg hA, lam_apply K (hg hA), lam_apply K hA]
  have hset : archEntries K '' ((fun y => g * y) ⁻¹' A) =
      mulLeftReal K (toMixedGL K g⁻¹ : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)) ''
        (archEntries K '' A) := by
    ext E
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨archEntries K (g * x), ⟨g * x, hx, rfl⟩, by rw [← archEntries_mul, inv_mul_cancel_left]⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨g⁻¹ * y, ?_, archEntries_mul K g⁻¹ y⟩
      show g * (g⁻¹ * y) ∈ A
      rwa [mul_inv_cancel_left]
  rw [hset, lebN_image_mulLeftReal K g⁻¹ ((measurableEmbedding_archEntries K).measurableSet_image.2 hA)]

private theorem lam_isFiniteMeasureOnCompacts : IsFiniteMeasureOnCompacts (lam K) := by
  refine ⟨fun C hC => ?_⟩
  rw [lam_apply K hC.measurableSet]
  have himg : IsCompact (archEntries K '' C) := hC.image (continuous_archEntries K)
  have hsub : archEntries K '' C ⊆ unitLocus K := by
    rw [← range_archEntries]
    exact Set.image_subset_range _ _
  obtain ⟨M, hM⟩ := himg.exists_bound_of_continuousOn ((continuousOn_wtN K).mono hsub)
  unfold lebN
  rw [withDensity_apply _ himg.measurableSet]
  calc ∫⁻ E in archEntries K '' C, (wtN K E : ℝ≥0∞) ≤ ∫⁻ _ in archEntries K '' C, ENNReal.ofReal M :=
        setLIntegral_mono measurable_const fun E hE => by
          rw [← ENNReal.ofReal_coe_nnreal]
          exact ENNReal.ofReal_le_ofReal ((Real.norm_eq_abs _ ▸ le_abs_self _).trans (hM E hE))
    _ = ENNReal.ofReal M * volume (archEntries K '' C) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top himg.measure_lt_top

omit [NumberField K] in

private theorem unitLocus_nonempty : (unitLocus K).Nonempty :=
  ⟨Matrix.of.symm 1, by
    show IsUnit (Matrix.det (Matrix.of (Matrix.of.symm (1 : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace K)))))
    rw [Equiv.apply_symm_apply, Matrix.det_one]
    exact isUnit_one⟩

private theorem lam_ne_zero : lam K ≠ 0 := by
  intro h
  have h1 : lam K Set.univ = 0 := by rw [h]; rfl
  rw [lam_apply K MeasurableSet.univ, Set.image_univ, range_archEntries] at h1
  unfold lebN at h1
  rw [withDensity_apply_eq_zero (measurable_wtN K)] at h1
  have hset : {E : EntrySpace K | (wtN K E : ℝ≥0∞) ≠ 0} ∩ unitLocus K = unitLocus K :=
    Set.inter_eq_right.2 fun E hE => wtN_ne_zero K hE
  rw [hset] at h1
  exact (isOpen_unitLocus K).measure_ne_zero volume (unitLocus_nonempty K) h1

private theorem measurable_wtN_nnreal : Measurable (wtN K) :=
  Measurable.subtype_mk (((continuous_normDet K).measurable.inv).pow_const 2)

private theorem integral_lam (Φ : EntrySpace K → ℂ) (hΦ : Continuous Φ) (hsupp : tsupport Φ ⊆ unitLocus K) :
    ∫ g, Φ (archEntries K g) ∂(lam K) = ∫ E, Φ E * ((wtN K E : ℝ) : ℂ) := by
  rw [← integral_map (measurableEmbedding_archEntries K).measurable.aemeasurable hΦ.aestronglyMeasurable, lam,
    (measurableEmbedding_archEntries K).map_comap, range_archEntries,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun E hE =>
      image_eq_zero_of_notMem_tsupport fun hE' => hE (hsupp hE')]
  unfold lebN
  rw [integral_withDensity_eq_integral_smul (measurable_wtN_nnreal K) Φ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun E => ?_)
  simp only [NNReal.smul_def, Complex.real_smul, mul_comm]

end ClassicalPart

end ArchHaarComparison
p2m_reactivate "P2MW.S_AutomorphicForm_exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen.ArchHaarComparison"

open ArchHaarComparison in
open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K]
    (U' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))
    (hU'c : IsCompact (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))))
    (hU'o : IsOpen (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)))) :
    ∃ c : ℝ, 0 < c ∧
      ∀ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace K) → ℂ, Continuous Φ → HasCompactSupport Φ →
        tsupport Φ ⊆ {E | IsUnit (Matrix.det (Matrix.of E))} →
          ∫ x, Φ (archEntries K (AdelicLevel.glArch (𝓞 K) K x)) *
              (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ))
                (AdelicLevel.glFin (𝓞 K) K x) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) =
            c * ∫ E, Φ E * (((mixedEmbedding.norm (Matrix.det (Matrix.of E)))⁻¹ ^ 2 : ℝ) : ℂ) := by
  haveI := ν_isHaarMeasure hU'c hU'o
  haveI := lam_isMulLeftInvariant K
  haveI := lam_isFiniteMeasureOnCompacts K

  set c : NNReal := (lam K).haarScalarFactor (ν U') with hc_def
  have hlam : lam K = c • ν U' := Measure.isMulLeftInvariant_eq_smul (lam K) (ν U')
  have hc : c ≠ 0 := fun h => lam_ne_zero K (by rw [hlam, h, zero_smul])
  have hν : ν U' = ((c⁻¹ : NNReal) : ENNReal) • lam K := by
    rw [hlam, ENNReal.smul_def, smul_smul, ← ENNReal.coe_mul, inv_mul_cancel₀ hc, ENNReal.coe_one, one_smul]
  refine ⟨(c : ℝ)⁻¹, inv_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)), fun Φ hΦ _ hsupp => ?_⟩

  have step1 : ∫ x, Φ (archEntries K (AdelicLevel.glArch (𝓞 K) K x)) *
      (U' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))).indicator (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 K) K x)
        ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) = ∫ g, Φ (archEntries K g) ∂(ν U') := by
    have hfm : AEStronglyMeasurable (fun g : GL (Fin 2) (InfiniteAdeleRing K) => Φ (archEntries K g))
        (Measure.map (AdelicLevel.glArch (𝓞 K) K) ((μ K).restrict (levelSet U'))) :=
      (hΦ.comp (continuous_archEntries K)).aestronglyMeasurable
    rw [ν, integral_map measurable_glArch.aemeasurable hfm, ← integral_indicator (isOpen_levelSet hU'o).measurableSet]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : AdelicLevel.glFin (𝓞 K) K x ∈ U'
    · simp [Set.indicator, levelSet, hx]
    · simp [Set.indicator, levelSet, hx]
  rw [step1, hν, integral_smul_measure, integral_lam K Φ hΦ hsupp]
  simp only [ENNReal.coe_toReal, NNReal.coe_inv, Complex.real_smul, coe_wtN]

end
p2m_reactivate "P2MW.S_AutomorphicForm_exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen.ArchHaarComparison"

end S_AutomorphicForm_exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen
end P2MW
export P2MW.S_AutomorphicForm_exists_integral_archEntries_mul_indicator_eq_mul_integral_of_isCompact_of_isOpen (solution)
