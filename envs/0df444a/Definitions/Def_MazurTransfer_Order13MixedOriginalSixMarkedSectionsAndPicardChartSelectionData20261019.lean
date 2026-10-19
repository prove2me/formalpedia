-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedOriginalSixMarkedSectionsAndPicardChartSelectionData20261019
-- name    : MazurTransfer_Order13MixedOriginalSixMarkedSectionsAndPicardChartSelectionData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T07:30:27.223544+00:00
-- url     : https://prove2.me/theorems/c17e0812-5089-4a5a-bad1-9b492ac7aaa3
-- title:
--   Original six marked sections and conditional Picard chart selection
-- statement:
--   The original six integral marked sections, their pairwise separation on field fibres and the original 216 triple family. The selection criterion retains its explicit genus-two model hypothesis. Named downstream consumer: the actual dyadic Picard chart sections.
-- source:
--   MazurTheorem original mixed single-section parameter algebras and reciprocal recovery, by Vas and contributors; exact official Anthropic FLT quotient/base-change bridge at pin 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Original per-file attribution retained.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: six literal original mixed integral sections, their exact
point separation over every field, and the original 216-triple Picard chart
selection criterion with its geometric genus-two model hypothesis explicit.
Named downstream consumer: actual dyadic mixed HasChartSections.
Original per-file headers and attribution are retained below.
-/
import Mathlib
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Theorems.Thm_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalInfinitySectionsData20261019
import Definitions.Def_MazurTransfer_Order13MixedOriginalRecoveredReciprocalAndSingleSectionPolynomialBasesData20261019
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalWholeCurveBaseChangeData20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: consume the retained exact chart-overlap proof as a set
range identity. Named downstream consumer: the actual positive infinity
complement in the whole two-chart curve. No affine identification is assumed.
Adapts the existing range wrapper to the actual mixed-curve overlap theorem.
-/

noncomputable section
universe u
namespace MazurTransfer.MixedOriginalSixMarkedSectionsChartRangeOverlap20261019
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve
variable (R : Type u) [CommRing R]

theorem reciprocalChartMap_preimage_ordinary_range :
    reciprocalChartMap R ⁻¹' Set.range (ordinaryChartMap R) =
      (PrimeSpectrum.basicOpen (zCoordinate R) : Set (PrimeSpectrum (reciprocalCoordinateRing R))) := by
  exact congrArg (fun U : (reciprocalScheme R).Opens => (U : Set (reciprocalScheme R)))
    (Order13MixedQuadraticHyperellipticMap.reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen R)

end MazurTransfer.MixedOriginalSixMarkedSectionsChartRangeOverlap20261019
#print axioms MazurTransfer.MixedOriginalSixMarkedSectionsChartRangeOverlap20261019.reciprocalChartMap_preimage_ordinary_range

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted the complete section-selection argument from official Anthropic FLT
exists_finite_etale_hasChartSections_of_field at exact pin
6e837e75355538c7f80bab5b956861e86c4eacc2. Original attribution retained.
Design boundary: six fibrewise distinct sections and genus-two geometric
Riemann-Roch models give original HasChartSections, with all triples indexed.
Named downstream consumer: the six actual marked order-13 integral sections.
Their distinctness and geometric model inputs remain explicit obligations.
-/

noncomputable section
universe u
namespace MazurTransfer.MixedOriginalDyadicSixSectionPicardChartCriterion20261019
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra
variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
variable (σ : Fin 6 → SchemeHomOver (𝟙 (Spec (.of R))) c)

def tripleFamily : Fin (Fintype.card (Fin 3 → Fin 6)) → Fin (5-2) →
    SchemeHomOver (𝟙 (Spec (.of R))) c :=
  fun i j => σ ((Fintype.equivFin (Fin 3 → Fin 6)).symm i j)

theorem hasChartSections_of_six_sections
    (hσ : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (.of k) ⟶ Spec (.of R)),
      Function.Injective (fun i => s ≫ (σ i).1))
    (hmodel : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s : Spec (.of k) ⟶ Spec (.of R)),
      ∃ (L : Type u) (_ : Field L) (_ : Algebra k L) (_ : IsCurveOver k L)
        (M : CurveModel k L) (e : M.C ≅ pullback c s)
        (he : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L),
        ∀ D : Divisor k L, (ell D : ℤ) - ell (Kc-D) = Divisor.degree D + 1 - 2) :
    HasChartSections c (g := 2) (r := 5) (tripleFamily c σ) := by
  classical
  intro k _ _ s
  obtain ⟨L, _, _, _, M, e, he, Kc, hRR⟩ := hmodel k s
  refine ⟨L, inferInstance, inferInstance, M, e, he, ⟨Kc,hRR⟩, ?_⟩
  intro D _ hdegD
  let P : {p : Spec (.of k) ⟶ pullback c s // p ≫ pullback.snd c s = 𝟙 _} → Place k L :=
    fun q => M.pointEquivPlace ⟨q.1 ≫ e.inv, by
      rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact q.2⟩
  have hPinj : Function.Injective P := by
    intro q q' h
    have h1 := congrArg Subtype.val (M.pointEquivPlace.injective h)
    exact Subtype.ext ((cancel_mono e.inv).mp h1)
  let pl : Fin 6 → Place k L := fun i => P (sectionFibrePoint (σ i) s)
  have key : ∀ i, (sectionFibrePoint (σ i) s).1 ≫ pullback.fst c s = s ≫ (σ i).1 :=
    fun _ => pullback.lift_fst _ _ _
  have hplinj : Function.Injective pl := by
    intro i j h
    have h1 := congrArg (fun q => q.1 ≫ pullback.fst c s) (hPinj h)
    rw [key,key] at h1
    exact hσ k s h1
  let S : Finset (Place k L) := Finset.univ.image pl
  have hScard : 5+1 ≤ S.card := by
    rw [Finset.card_image_of_injective _ hplinj, Finset.card_univ, Fintype.card_fin]
  have hS1 : ∀ v ∈ S, v.deg = 1 := fun v _ => IsCurveOver.deg_eq_one_of_isAlgClosed v
  obtain ⟨f, _, hfS, hf⟩ :=
    AlgebraicCurve.RROpens.exists_injective_ell_sub_sum_single_eq_one_of_le_card
      (g := 2) (r := 5) hRR (by omega) S hS1 hScard D hdegD
  have hch : ∀ j, ∃ i, pl i = f j := fun j => by
    simpa [S, Finset.mem_image] using hfS j
  choose μ hμ using hch
  refine ⟨(Fintype.equivFin (Fin 3 → Fin 6)) μ, ?_⟩
  change ell (D - ∑ j, Finsupp.single
    (P (sectionFibrePoint (σ ((Fintype.equivFin (Fin 3 → Fin 6)).symm
      ((Fintype.equivFin (Fin 3 → Fin 6)) μ) j)) s)) 1) = 1
  simp only [Equiv.symm_apply_apply]
  have hsum : ∑ j, Finsupp.single (P (sectionFibrePoint (σ (μ j)) s)) (1 : ℤ) =
      ∑ j, Finsupp.single (f j) 1 :=
    Finset.sum_congr rfl fun j _ => by rw [← hμ j]
  rw [hsum]
  exact hf

end MazurTransfer.MixedOriginalDyadicSixSectionPicardChartCriterion20261019
#print axioms MazurTransfer.MixedOriginalDyadicSixSectionPicardChartCriterion20261019.hasChartSections_of_six_sections

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts the retained integral-section construction to the mixed quadratic
model. Positive labels follow the retained rational square-model marking;
the mixed ordinates are 0 and -1.
Design boundary: six literal sections over every commutative base ring.
Named downstream consumer: geometric distinctness and the actual dyadic
Picard chart-section input. No genus or chart-coverage assertion is assumed.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedIntegralSections
open Polynomial CategoryTheory AlgebraicGeometry
open MixedQuadraticCoordinateJacobian Order13MixedQuadraticJacobianCertificates
open Order13MixedQuadraticPolynomialEvaluations Order13DyadicMixedQuadraticCharts
open Order13MixedQuadraticOverlapCoordinates Order13MixedQuadraticGluedCurve
variable (R : Type u) [CommRing R]

def ordinaryEvaluationAlgHom (t a : R)
    (ha : a ^ 2 + (t ^ 3 + t ^ 2 + 1) * a - t * (t + 1) = 0) :
    ordinaryCoordinateRing R →ₐ[R] R :=
  Order13MixedQuadraticOrdinarySolutions.solutionToAlgHom R R t a ha

def ordinaryEvaluation (t a : R)
    (ha : a ^ 2 + (t ^ 3 + t ^ 2 + 1) * a - t * (t + 1) = 0) :
    ordinaryCoordinateRing R →+* R := (ordinaryEvaluationAlgHom R t a ha).toRingHom

theorem ordinaryEvaluation_x (t a : R)
    (ha : a ^ 2 + (t ^ 3 + t ^ 2 + 1) * a - t * (t + 1) = 0) :
    ordinaryEvaluation R t a ha (xCoordinate R) = t :=
  Order13MixedQuadraticOrdinarySolutions.solutionToAlgHom_x R R t a ha

theorem ordinaryEvaluation_y (t a : R)
    (ha : a ^ 2 + (t ^ 3 + t ^ 2 + 1) * a - t * (t + 1) = 0) :
    ordinaryEvaluation R t a ha (yCoordinate R) = a :=
  Order13MixedQuadraticOrdinarySolutions.solutionToAlgHom_y R R t a ha

def reciprocalInfinityEvaluationAlgHom (a : R) (ha : a ^ 2 + a = 0) :
    reciprocalCoordinateRing R →ₐ[R] R :=
  AdjoinRoot.liftAlgHom (equation R (reciprocalH R) (reciprocalF R)) (aeval (0 : R)) a (by
    change eval₂ (aeval (0 : R)).toRingHom a
      (X ^ 2 + C (reciprocalH R) * X - C (reciprocalF R)) = 0
    simp only [eval₂_sub,eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C]
    rw [map_reciprocalH R _,map_reciprocalF R _]
    simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,aeval_X]
    simpa using ha)

def reciprocalInfinityEvaluation (a : R) (ha : a ^ 2 + a = 0) :
    reciprocalCoordinateRing R →+* R := (reciprocalInfinityEvaluationAlgHom R a ha).toRingHom

theorem reciprocalInfinityEvaluation_z (a : R) (ha : a ^ 2 + a = 0) :
    reciprocalInfinityEvaluation R a ha (zCoordinate R) = 0 := by
  simp only [reciprocalInfinityEvaluation,reciprocalInfinityEvaluationAlgHom,zCoordinate,
    AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,AdjoinRoot.liftAlgHom_of,aeval_X]

theorem reciprocalInfinityEvaluation_w (a : R) (ha : a ^ 2 + a = 0) :
    reciprocalInfinityEvaluation R a ha (wCoordinate R) = a :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

private theorem spec_algHom_section (A : Type u) [CommRing A] [Algebra R A] (φ : A →ₐ[R] R) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A)) = 𝟙 (Spec (.of R)) := by
  have hh : CommRingCat.ofHom (algebraMap R A) ≫ CommRingCat.ofHom φ.toRingHom =
      𝟙 (CommRingCat.of R) := by
    apply CommRingCat.hom_ext
    ext r
    exact φ.commutes r
  rw [← Spec.map_comp,hh,Spec.map_id]

def ordinaryMorphism (t a : R)
    (ha : a ^ 2 + (t ^ 3 + t ^ 2 + 1) * a - t * (t + 1) = 0) : Spec (.of R) ⟶ curveScheme R :=
  Spec.map (CommRingCat.ofHom (ordinaryEvaluation R t a ha)) ≫ ordinaryChartMap R

theorem ordinaryMorphism_curveToBase (t a : R)
    (ha : a ^ 2 + (t ^ 3 + t ^ 2 + 1) * a - t * (t + 1) = 0) :
    ordinaryMorphism R t a ha ≫ curveToBase R = 𝟙 (Spec (.of R)) := by
  let q : Spec (.of R) ⟶ ordinaryScheme R := Spec.map (CommRingCat.ofHom (ordinaryEvaluation R t a ha))
  have hq : q ≫ ordinaryToBase R = 𝟙 (Spec (.of R)) :=
    spec_algHom_section R (ordinaryCoordinateRing R) (ordinaryEvaluationAlgHom R t a ha)
  have he := congrArg (fun f : ordinaryScheme R ⟶ Spec (.of R) => q ≫ f)
    (ordinaryChartMap_curveToBase R)
  exact (Category.assoc q (ordinaryChartMap R) (curveToBase R)).trans (he.trans hq)

def infinityMorphism (a : R) (ha : a ^ 2 + a = 0) : Spec (.of R) ⟶ curveScheme R :=
  Spec.map (CommRingCat.ofHom (reciprocalInfinityEvaluation R a ha)) ≫ reciprocalChartMap R

theorem infinityMorphism_curveToBase (a : R) (ha : a ^ 2 + a = 0) :
    infinityMorphism R a ha ≫ curveToBase R = 𝟙 (Spec (.of R)) := by
  let q : Spec (.of R) ⟶ reciprocalScheme R := Spec.map (CommRingCat.ofHom (reciprocalInfinityEvaluation R a ha))
  have hq : q ≫ reciprocalToBase R = 𝟙 (Spec (.of R)) :=
    spec_algHom_section R (reciprocalCoordinateRing R) (reciprocalInfinityEvaluationAlgHom R a ha)
  have he := congrArg (fun f : reciprocalScheme R ⟶ Spec (.of R) => q ≫ f)
    (reciprocalChartMap_curveToBase R)
  exact (Category.assoc q (reciprocalChartMap R) (curveToBase R)).trans (he.trans hq)

def ordinarySection (t a : R)
    (ha : a ^ 2 + (t ^ 3 + t ^ 2 + 1) * a - t * (t + 1) = 0) :
    NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of R))) (curveToBase R) :=
  ⟨ordinaryMorphism R t a ha,ordinaryMorphism_curveToBase R t a ha⟩

def infinitySection (a : R) (ha : a ^ 2 + a = 0) :
    NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of R))) (curveToBase R) :=
  ⟨infinityMorphism R a ha,infinityMorphism_curveToBase R a ha⟩

def positiveInfinitySection := infinitySection R 0 (by simp)
def negativeInfinitySection := infinitySection R (-1) (by ring)
def zeroPositiveSection := ordinarySection R 0 0 (by ring)
def zeroNegativeSection := ordinarySection R 0 (-1) (by ring)
def negOnePositiveSection := ordinarySection R (-1) 0 (by ring)
def negOneNegativeSection := ordinarySection R (-1) (-1) (by ring)

def sixMarkedSections : Fin 6 →
    NeronModelInfra.SchemeHomOver (𝟙 (Spec (.of R))) (curveToBase R) :=
  ![positiveInfinitySection R,negativeInfinitySection R,zeroPositiveSection R,
    zeroNegativeSection R,negOnePositiveSection R,negOneNegativeSection R]

theorem positiveInfinitySection_val : (positiveInfinitySection R).val =
    Order13MixedQuadraticInfinitySections.infinitySectionZero R := rfl

theorem negativeInfinitySection_val : (negativeInfinitySection R).val =
    Order13MixedQuadraticInfinitySections.infinitySectionNegOne R := rfl

end MazurTransfer.Order13MixedIntegralSections
#print axioms MazurTransfer.Order13MixedIntegralSections.sixMarkedSections
#print axioms MazurTransfer.Order13MixedIntegralSections.positiveInfinitySection_val

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: literal evaluation coordinates distinguish section images
above every prime of the coefficient ring; infinity images avoid the ordinary
chart. Named downstream consumer: fibrewise distinctness of the six marked
integral sections in the original Picard chart-section criterion.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedMarkedSectionPointSeparation
open CategoryTheory AlgebraicGeometry Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve
open Order13MixedIntegralSections
variable (R : Type u) [CommRing R]

theorem ordinaryEvaluation_coefficient (t a : R)
    (ha : a^2 + (t^3+t^2+1)*a-t*(t+1)=0) (r : R) :
    ordinaryEvaluation R t a ha (algebraMap R (ordinaryCoordinateRing R) r) = r :=
  (ordinaryEvaluationAlgHom R t a ha).commutes r

theorem infinityEvaluation_coefficient (a : R) (ha : a^2+a=0) (r : R) :
    reciprocalInfinityEvaluation R a ha (algebraMap R (reciprocalCoordinateRing R) r) = r :=
  (reciprocalInfinityEvaluationAlgHom R a ha).commutes r

theorem ordinary_point_equality_constants (p : PrimeSpectrum R) (t a u b : R)
    (ha : a^2 + (t^3+t^2+1)*a-t*(t+1)=0)
    (hb : b^2 + (u^3+u^2+1)*b-u*(u+1)=0)
    (h : ordinaryMorphism R t a ha p = ordinaryMorphism R u b hb p) :
    u-t ∈ p.asIdeal ∧ b-a ∈ p.asIdeal := by
  have hp := (ordinaryChartMap R).isOpenEmbedding.injective h
  change PrimeSpectrum.comap (ordinaryEvaluation R t a ha) p =
    PrimeSpectrum.comap (ordinaryEvaluation R u b hb) p at hp
  have hx : xCoordinate R - algebraMap R (ordinaryCoordinateRing R) t ∈
      (PrimeSpectrum.comap (ordinaryEvaluation R t a ha) p).asIdeal := by
    change ordinaryEvaluation R t a ha _ ∈ p.asIdeal
    simp only [map_sub, ordinaryEvaluation_x, ordinaryEvaluation_coefficient, sub_self, Ideal.zero_mem]
  have hy : yCoordinate R - algebraMap R (ordinaryCoordinateRing R) a ∈
      (PrimeSpectrum.comap (ordinaryEvaluation R t a ha) p).asIdeal := by
    change ordinaryEvaluation R t a ha _ ∈ p.asIdeal
    simp only [map_sub, ordinaryEvaluation_y, ordinaryEvaluation_coefficient, sub_self, Ideal.zero_mem]
  rw [hp] at hx hy
  change ordinaryEvaluation R u b hb _ ∈ p.asIdeal at hx hy
  simp only [map_sub, ordinaryEvaluation_x, ordinaryEvaluation_y, ordinaryEvaluation_coefficient] at hx hy
  exact ⟨hx,hy⟩

theorem infinity_point_equality_constants (p : PrimeSpectrum R) (a b : R)
    (ha : a^2+a=0) (hb : b^2+b=0)
    (h : infinityMorphism R a ha p = infinityMorphism R b hb p) : b-a ∈ p.asIdeal := by
  have hp := (reciprocalChartMap R).isOpenEmbedding.injective h
  change PrimeSpectrum.comap (reciprocalInfinityEvaluation R a ha) p =
    PrimeSpectrum.comap (reciprocalInfinityEvaluation R b hb) p at hp
  have hw : wCoordinate R - algebraMap R (reciprocalCoordinateRing R) a ∈
      (PrimeSpectrum.comap (reciprocalInfinityEvaluation R a ha) p).asIdeal := by
    change reciprocalInfinityEvaluation R a ha _ ∈ p.asIdeal
    simp only [map_sub, reciprocalInfinityEvaluation_w, infinityEvaluation_coefficient,
      sub_self, Ideal.zero_mem]
  rw [hp] at hw
  change reciprocalInfinityEvaluation R b hb _ ∈ p.asIdeal at hw
  simpa only [map_sub, reciprocalInfinityEvaluation_w, infinityEvaluation_coefficient] using hw

theorem infinity_point_not_ordinary (p : PrimeSpectrum R) (a : R) (ha : a^2+a=0) :
    infinityMorphism R a ha p ∉ Set.range (ordinaryChartMap R) := by
  intro h
  have hz := Set.ext_iff.mp
    (MixedOriginalSixMarkedSectionsChartRangeOverlap20261019.reciprocalChartMap_preimage_ordinary_range R)
    ((Spec.map (CommRingCat.ofHom (reciprocalInfinityEvaluation R a ha))) p)
  have hn := hz.mp h
  change reciprocalInfinityEvaluation R a ha (zCoordinate R) ∉ p.asIdeal at hn
  rw [reciprocalInfinityEvaluation_z] at hn
  exact hn p.asIdeal.zero_mem

theorem infinity_ordinary_point_ne (p : PrimeSpectrum R) (a t b : R)
    (ha : a^2+a=0) (hb : b^2+(t^3+t^2+1)*b-t*(t+1)=0) :
    infinityMorphism R a ha p ≠ ordinaryMorphism R t b hb p := by
  intro h
  apply infinity_point_not_ordinary R p a ha
  rw [h]
  exact ⟨(Spec.map (CommRingCat.ofHom (ordinaryEvaluation R t b hb))) p,rfl⟩

end MazurTransfer.Order13MixedMarkedSectionPointSeparation
#print axioms MazurTransfer.Order13MixedMarkedSectionPointSeparation.ordinary_point_equality_constants
#print axioms MazurTransfer.Order13MixedMarkedSectionPointSeparation.infinity_point_equality_constants
#print axioms MazurTransfer.Order13MixedMarkedSectionPointSeparation.infinity_ordinary_point_ne

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: point images of the six actual mixed marked sections are distinct
above every prime over any commutative coefficient ring; precomposition with a field point
therefore preserves distinctness as scheme morphisms.
Named downstream consumer: MixedOriginalDyadicSixSectionPicardChartCriterion20261019 for the integral
order-13 curve family.
-/

noncomputable section
universe u
namespace MazurTransfer.Order13MixedSixMarkedSectionsDistinct
open CategoryTheory AlgebraicGeometry Polynomial
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticGluedCurve
open Order13MixedIntegralSections Order13MixedMarkedSectionPointSeparation
variable (R : Type u) [CommRing R]

private theorem point_ne_0_1  (p : PrimeSpectrum R) :
    (sixMarkedSections R 0).val p ≠ (sixMarkedSections R 1).val p := by
  intro h
  have he := infinity_point_equality_constants R p 0 (-1) (by simp) (by simp) h
  have hn : (-1 : R) ∉ p.asIdeal := Ideal.notMem_of_isUnit _ (isUnit_one : IsUnit (1 : R)).neg
  apply hn
  convert he using 1; ring

private theorem point_ne_0_2  (p : PrimeSpectrum R) :
    (sixMarkedSections R 0).val p ≠ (sixMarkedSections R 2).val p := by
  exact infinity_ordinary_point_ne R p _ _ _ _ _

private theorem point_ne_0_3  (p : PrimeSpectrum R) :
    (sixMarkedSections R 0).val p ≠ (sixMarkedSections R 3).val p := by
  exact infinity_ordinary_point_ne R p _ _ _ _ _

private theorem point_ne_0_4  (p : PrimeSpectrum R) :
    (sixMarkedSections R 0).val p ≠ (sixMarkedSections R 4).val p := by
  exact infinity_ordinary_point_ne R p _ _ _ _ _

private theorem point_ne_0_5  (p : PrimeSpectrum R) :
    (sixMarkedSections R 0).val p ≠ (sixMarkedSections R 5).val p := by
  exact infinity_ordinary_point_ne R p _ _ _ _ _

private theorem point_ne_1_2  (p : PrimeSpectrum R) :
    (sixMarkedSections R 1).val p ≠ (sixMarkedSections R 2).val p := by
  exact infinity_ordinary_point_ne R p _ _ _ _ _

private theorem point_ne_1_3  (p : PrimeSpectrum R) :
    (sixMarkedSections R 1).val p ≠ (sixMarkedSections R 3).val p := by
  exact infinity_ordinary_point_ne R p _ _ _ _ _

private theorem point_ne_1_4  (p : PrimeSpectrum R) :
    (sixMarkedSections R 1).val p ≠ (sixMarkedSections R 4).val p := by
  exact infinity_ordinary_point_ne R p _ _ _ _ _

private theorem point_ne_1_5  (p : PrimeSpectrum R) :
    (sixMarkedSections R 1).val p ≠ (sixMarkedSections R 5).val p := by
  exact infinity_ordinary_point_ne R p _ _ _ _ _

private theorem point_ne_2_3  (p : PrimeSpectrum R) :
    (sixMarkedSections R 2).val p ≠ (sixMarkedSections R 3).val p := by
  intro h
  have he := ordinary_point_equality_constants R p (0) (0) (0) (-1) _ _ h
  have hn : (-1 : R) ∉ p.asIdeal := Ideal.notMem_of_isUnit _ (isUnit_one : IsUnit (1 : R)).neg
  apply hn
  convert he.2 using 1; ring

private theorem point_ne_2_4  (p : PrimeSpectrum R) :
    (sixMarkedSections R 2).val p ≠ (sixMarkedSections R 4).val p := by
  intro h
  have he := ordinary_point_equality_constants R p (0) (0) (-1) (0) _ _ h
  have hn : (-1 : R) ∉ p.asIdeal := Ideal.notMem_of_isUnit _ isUnit_one.neg
  apply hn
  convert he.1 using 1; ring

private theorem point_ne_2_5  (p : PrimeSpectrum R) :
    (sixMarkedSections R 2).val p ≠ (sixMarkedSections R 5).val p := by
  intro h
  have he := ordinary_point_equality_constants R p (0) (0) (-1) (-1) _ _ h
  have hn : (-1 : R) ∉ p.asIdeal := Ideal.notMem_of_isUnit _ isUnit_one.neg
  apply hn
  convert he.1 using 1; ring

private theorem point_ne_3_4  (p : PrimeSpectrum R) :
    (sixMarkedSections R 3).val p ≠ (sixMarkedSections R 4).val p := by
  intro h
  have he := ordinary_point_equality_constants R p (0) (-1) (-1) (0) _ _ h
  have hn : (-1 : R) ∉ p.asIdeal := Ideal.notMem_of_isUnit _ isUnit_one.neg
  apply hn
  convert he.1 using 1; ring

private theorem point_ne_3_5  (p : PrimeSpectrum R) :
    (sixMarkedSections R 3).val p ≠ (sixMarkedSections R 5).val p := by
  intro h
  have he := ordinary_point_equality_constants R p (0) (-1) (-1) (-1) _ _ h
  have hn : (-1 : R) ∉ p.asIdeal := Ideal.notMem_of_isUnit _ isUnit_one.neg
  apply hn
  convert he.1 using 1; ring

private theorem point_ne_4_5  (p : PrimeSpectrum R) :
    (sixMarkedSections R 4).val p ≠ (sixMarkedSections R 5).val p := by
  intro h
  have he := ordinary_point_equality_constants R p (-1) (0) (-1) (-1) _ _ h
  have hn : (-1 : R) ∉ p.asIdeal := Ideal.notMem_of_isUnit _ (isUnit_one : IsUnit (1 : R)).neg
  apply hn
  convert he.2 using 1; ring

theorem six_point_images_injective  (p : PrimeSpectrum R) :
    Function.Injective (fun i : Fin 6 => (sixMarkedSections R i).val p) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (point_ne_0_1 R p hij)
  · exact False.elim (point_ne_0_2 R p hij)
  · exact False.elim (point_ne_0_3 R p hij)
  · exact False.elim (point_ne_0_4 R p hij)
  · exact False.elim (point_ne_0_5 R p hij)
  · exact False.elim (point_ne_0_1 R p hij.symm)
  · rfl
  · exact False.elim (point_ne_1_2 R p hij)
  · exact False.elim (point_ne_1_3 R p hij)
  · exact False.elim (point_ne_1_4 R p hij)
  · exact False.elim (point_ne_1_5 R p hij)
  · exact False.elim (point_ne_0_2 R p hij.symm)
  · exact False.elim (point_ne_1_2 R p hij.symm)
  · rfl
  · exact False.elim (point_ne_2_3 R p hij)
  · exact False.elim (point_ne_2_4 R p hij)
  · exact False.elim (point_ne_2_5 R p hij)
  · exact False.elim (point_ne_0_3 R p hij.symm)
  · exact False.elim (point_ne_1_3 R p hij.symm)
  · exact False.elim (point_ne_2_3 R p hij.symm)
  · rfl
  · exact False.elim (point_ne_3_4 R p hij)
  · exact False.elim (point_ne_3_5 R p hij)
  · exact False.elim (point_ne_0_4 R p hij.symm)
  · exact False.elim (point_ne_1_4 R p hij.symm)
  · exact False.elim (point_ne_2_4 R p hij.symm)
  · exact False.elim (point_ne_3_4 R p hij.symm)
  · rfl
  · exact False.elim (point_ne_4_5 R p hij)
  · exact False.elim (point_ne_0_5 R p hij.symm)
  · exact False.elim (point_ne_1_5 R p hij.symm)
  · exact False.elim (point_ne_2_5 R p hij.symm)
  · exact False.elim (point_ne_3_5 R p hij.symm)
  · exact False.elim (point_ne_4_5 R p hij.symm)
  · rfl

theorem six_sections_field_precomposition_injective 
    (k : Type u) [Field k] (s : Spec (.of k) ⟶ Spec (.of R)) :
    Function.Injective (fun i : Fin 6 => s ≫ (sixMarkedSections R i).val) := by
  intro i j hij
  have hp := congrArg
    (fun f : Spec (.of k) ⟶ curveScheme R => f (IsLocalRing.closedPoint k)) hij
  exact six_point_images_injective R (s (IsLocalRing.closedPoint k)) hp

end MazurTransfer.Order13MixedSixMarkedSectionsDistinct
#print axioms MazurTransfer.Order13MixedSixMarkedSectionsDistinct.six_point_images_injective

#print axioms MazurTransfer.Order13MixedSixMarkedSectionsDistinct.six_sections_field_precomposition_injective

end


