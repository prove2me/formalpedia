-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalGluedCurveData20261019
-- name    : MazurTransfer_Order13MixedQuadraticOriginalGluedCurveData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T04:18:13.104872+00:00
-- url     : https://prove2.me/theorems/a548b432-29c6-470c-b483-95db2e7b3fbf
-- title:
--   Original glued mixed quadratic curve and structure morphism
-- statement:
--   The original two-chart mixed quadratic curve scheme, its open chart inclusions, categorical gluing data and glued structure morphism. Ninety-one public declaration types and twenty-eight whole values, eight private proof-helper types, both original chart constructors and all recursor reduction rules are checked. Named downstream consumer: smoothness and properness of the original dyadic curve and its integral Picard family.
-- source:
--   MazurTheorem original mixed quadratic integral charts, overlap and gluing, by Vasily Ilin and contributors; Apache-2.0. Original attribution retained.

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Copyright (c) 2026 Vas and contributors.
Released under Apache-2.0. Authors: Vasily Ilin.
Complete two-chart categorical gluing and structure-map proofs adapted
from the existing XOneThirteenProjectiveCurve construction at the pinned
MazurTheorem source. The affine charts and overlap maps use the actual
mixed quadratic equations, with no invertibility of two assumed.
Design boundary: an actual integral two-chart curve scheme and structure
morphism. Named downstream consumer: dyadic smoothness and properness,
and its whole-curve rational-fibre comparison.
-/
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalOverlapAlgebraData20261019

noncomputable section
namespace MazurTransfer.Order13MixedQuadraticGluedCurve
open CategoryTheory AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts Order13MixedQuadraticOverlapCoordinates
open Order13MixedQuadraticTransitionHomomorphisms Order13MixedQuadraticOverlapEquivalence
universe u
variable (R : Type u) [CommRing R]

/-- The corresponding isomorphism of punctured affine schemes. -/
noncomputable def overlapSchemeIso :
    Spec (.of (OrdinaryOverlapRing R)) ≅
      Spec (.of (ReciprocalOverlapRing R)) :=
  Scheme.Spec.mapIso
    (overlapAlgEquiv R).toRingEquiv.toCommRingCatIso.symm.op

@[simp]
theorem overlapSchemeIso_hom :
    (overlapSchemeIso R).hom =
      Spec.map (CommRingCat.ofHom (reciprocalToOrdinary R).toRingHom) := by
  rfl

@[simp]
theorem overlapSchemeIso_inv :
    (overlapSchemeIso R).inv =
      Spec.map (CommRingCat.ofHom (ordinaryToReciprocal R).toRingHom) := by
  rfl

/-- The two affine charts used in the compactification. -/
inductive Chart : Type u
  | ordinary
  | reciprocal
  deriving DecidableEq

/-- The affine scheme belonging to a chart. -/
noncomputable abbrev chartScheme : Chart → Scheme
  | .ordinary => Order13DyadicMixedQuadraticCharts.ordinaryScheme R
  | .reciprocal => Order13DyadicMixedQuadraticCharts.reciprocalScheme R

/-- For distinct charts, the principal-open overlap as viewed from the
first chart. -/
noncomputable abbrev overlapScheme :
    ∀ i j : Chart, i ≠ j → Scheme
  | .ordinary, .reciprocal, _ => Spec (.of (OrdinaryOverlapRing R))
  | .reciprocal, .ordinary, _ => Spec (.of (ReciprocalOverlapRing R))
  | .ordinary, .ordinary, h => (h rfl).elim
  | .reciprocal, .reciprocal, h => (h rfl).elim

/-- Each overlap is included as the principal open where the corresponding
abscissa is invertible. -/
noncomputable def overlapInclusion :
    ∀ i j : Chart, (h : i ≠ j) →
      overlapScheme R i j h ⟶ chartScheme R i
  | .ordinary, .reciprocal, _ =>
      Spec.map (CommRingCat.ofHom
        (algebraMap (ordinaryCoordinateRing R)
          (OrdinaryOverlapRing R)))
  | .reciprocal, .ordinary, _ =>
      Spec.map (CommRingCat.ofHom
        (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R)))
  | .ordinary, .ordinary, h => (h rfl).elim
  | .reciprocal, .reciprocal, h => (h rfl).elim

/-- The transition isomorphism, oriented from the first chart's overlap to
the second chart's overlap. -/
noncomputable def overlapTransition :
    ∀ i j : Chart, (h : i ≠ j) →
      overlapScheme R i j h ⟶ overlapScheme R j i h.symm
  | .ordinary, .reciprocal, _ => (overlapSchemeIso R).hom
  | .reciprocal, .ordinary, _ => (overlapSchemeIso R).inv
  | .ordinary, .ordinary, h => (h rfl).elim
  | .reciprocal, .reciprocal, h => (h rfl).elim

private theorem overlapInclusion_open
    (i j : Chart) (h : i ≠ j) :
    IsOpenImmersion (overlapInclusion R i j h) := by
  rcases i with (_ | _) <;> rcases j with (_ | _)
  · exact (h rfl).elim
  · exact IsOpenImmersion.of_isLocalization
      (xCoordinate R)
  · exact IsOpenImmersion.of_isLocalization (zCoordinate R)
  · exact (h rfl).elim

private theorem overlapInclusion_mono
    (i j : Chart) (h : i ≠ j) :
    CategoryTheory.Mono (overlapInclusion R i j h) := by
  haveI : IsOpenImmersion (overlapInclusion R i j h) :=
    overlapInclusion_open R i j h
  infer_instance

/-- Two-chart categorical gluing datum.  Triple-overlap coherence is
vacuous because three pairwise distinct charts do not exist. -/
noncomputable abbrev categoricalGlueData :
    CategoryTheory.GlueData' Scheme.{u} where
  J := Chart
  U := chartScheme R
  V := overlapScheme R
  f := overlapInclusion R
  f_mono := overlapInclusion_mono R
  f_hasPullback := by
    intro i j k hij hik
    infer_instance
  t := overlapTransition R
  t' := by
    intro i j k hij hik hjk
    rcases i with (_ | _) <;> rcases j with (_ | _) <;>
      rcases k with (_ | _) <;> contradiction
  t_fac := by
    intro i j k hij hik hjk
    rcases i with (_ | _) <;> rcases j with (_ | _) <;>
      rcases k with (_ | _) <;> contradiction
  t_inv := by
    intro i j hij
    rcases i with (_ | _) <;> rcases j with (_ | _)
    · exact (hij rfl).elim
    · exact (overlapSchemeIso R).hom_inv_id
    · exact (overlapSchemeIso R).inv_hom_id
    · exact (hij rfl).elim
  cocycle := by
    intro i j k hij hik hjk
    rcases i with (_ | _) <;> rcases j with (_ | _) <;>
      rcases k with (_ | _) <;> contradiction

private theorem categoricalGlueData_f'_open (i j : Chart) :
    IsOpenImmersion ((categoricalGlueData R).f' i j) := by
  classical
  delta CategoryTheory.GlueData'.f'
  by_cases h : i = j
  · simp only [dif_pos h]
    exact IsOpenImmersion.of_isIso _
  · simp only [dif_neg h]
    haveI : IsOpenImmersion (overlapInclusion R i j h) :=
      overlapInclusion_open R i j h
    exact IsOpenImmersion.comp _ _

/-- Scheme-theoretic gluing data obtained from the checked two-chart
transition. -/
noncomputable abbrev glueData : Scheme.GlueData.{u} where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (categoricalGlueData R)
  f_open := categoricalGlueData_f'_open R

/-- The actual two-chart scheme attached to the order-thirteen sextic. -/
noncomputable def curveScheme : Scheme := (glueData R).glued

/-- The ordinary affine chart as an open subscheme of the glued curve. -/
noncomputable def ordinaryChartMap :
    Order13DyadicMixedQuadraticCharts.ordinaryScheme R ⟶ curveScheme R :=
  (glueData R).ι Chart.ordinary

/-- The reciprocal affine chart as an open subscheme of the glued curve. -/
noncomputable def reciprocalChartMap :
    Order13DyadicMixedQuadraticCharts.reciprocalScheme R ⟶ curveScheme R :=
  (glueData R).ι Chart.reciprocal

instance ordinaryChartMap_isOpenImmersion :
    IsOpenImmersion (ordinaryChartMap R) := by
  dsimp [ordinaryChartMap]
  exact Scheme.GlueData.ι_isOpenImmersion (glueData R) Chart.ordinary

instance reciprocalChartMap_isOpenImmersion :
    IsOpenImmersion (reciprocalChartMap R) := by
  dsimp [reciprocalChartMap]
  exact Scheme.GlueData.ι_isOpenImmersion (glueData R) Chart.reciprocal

/-! ## The curve over its coefficient ring -/

/-- The chartwise structure maps. -/
noncomputable def chartToBase :
    ∀ i : Chart, chartScheme R i ⟶ Spec (.of R)
  | .ordinary => ordinaryToBase R
  | .reciprocal => reciprocalToBase R

private theorem ordinary_ne_reciprocal :
    (Chart.ordinary : Chart.{u}) ≠ Chart.reciprocal := by
  intro h
  cases h

private theorem reciprocal_ne_ordinary :
    (Chart.reciprocal : Chart.{u}) ≠ Chart.ordinary := by
  intro h
  cases h

private theorem ordinary_reciprocal_base_compatible :
    Spec.map (CommRingCat.ofHom
        (algebraMap (ordinaryCoordinateRing R)
          (OrdinaryOverlapRing R))) ≫
        ordinaryToBase R =
      Spec.map (CommRingCat.ofHom
          (reciprocalToOrdinary R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R))) ≫
        reciprocalToBase R := by
  simp only [ordinaryToBase, reciprocalToBase]
  rw [← Spec.map_comp, ← Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  ext k
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← IsScalarTower.algebraMap_apply R
    (ordinaryCoordinateRing R) (OrdinaryOverlapRing R)]
  simp

private theorem reciprocal_ordinary_base_compatible :
    Spec.map (CommRingCat.ofHom
        (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R))) ≫
        reciprocalToBase R =
      Spec.map (CommRingCat.ofHom
          (ordinaryToReciprocal R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (ordinaryCoordinateRing R)
            (OrdinaryOverlapRing R))) ≫
        ordinaryToBase R := by
  simp only [ordinaryToBase, reciprocalToBase]
  rw [← Spec.map_comp, ← Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  ext k
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← IsScalarTower.algebraMap_apply R
    (reciprocalCoordinateRing R) (ReciprocalOverlapRing R)]
  simp

private theorem chartToBase_transition_compatible
    (i j : Chart) (h : i ≠ j) :
    overlapInclusion R i j h ≫ chartToBase R i =
      overlapTransition R i j h ≫
        overlapInclusion R j i h.symm ≫ chartToBase R j := by
  rcases i with (_ | _) <;> rcases j with (_ | _)
  · exact (h rfl).elim
  · exact ordinary_reciprocal_base_compatible R
  · exact reciprocal_ordinary_base_compatible R
  · exact (h rfl).elim

/-- The structure morphism obtained by gluing the two affine algebra
structures. -/
noncomputable def curveToBase : curveScheme R ⟶ Spec (.of R) :=
  by
    letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData R)
    exact Limits.Multicoequalizer.desc (glueData R).toGlueData.diagram
      (Spec (.of R)) (chartToBase R) (by
      rintro ⟨i, j⟩
      simp only [CategoryTheory.GlueData.diagram_fst,
        CategoryTheory.GlueData.diagram_snd]
      rcases i with (_ | _) <;> rcases j with (_ | _)
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToBase,
          Limits.MultispanShape.prod]
        simp
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToBase,
          ordinary_ne_reciprocal, reciprocal_ne_ordinary,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal,
          dif_neg reciprocal_ne_ordinary, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact chartToBase_transition_compatible R _ _
          ordinary_ne_reciprocal
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToBase,
          ordinary_ne_reciprocal, reciprocal_ne_ordinary,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal,
          dif_neg reciprocal_ne_ordinary, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact chartToBase_transition_compatible R _ _
          reciprocal_ne_ordinary
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', chartToBase,
          Limits.MultispanShape.prod]
        simp)

@[simp, reassoc]
theorem ordinaryChartMap_curveToBase :
    ordinaryChartMap R ≫ curveToBase R = ordinaryToBase R := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData R)
  unfold ordinaryChartMap curveToBase
  apply Limits.Multicoequalizer.π_desc

@[simp, reassoc]
theorem reciprocalChartMap_curveToBase :
    reciprocalChartMap R ≫ curveToBase R = reciprocalToBase R := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData R)
  unfold reciprocalChartMap curveToBase
  apply Limits.Multicoequalizer.π_desc

end MazurTransfer.Order13MixedQuadraticGluedCurve
#print axioms MazurTransfer.Order13MixedQuadraticGluedCurve.ordinaryChartMap_curveToBase
#print axioms MazurTransfer.Order13MixedQuadraticGluedCurve.reciprocalChartMap_curveToBase


