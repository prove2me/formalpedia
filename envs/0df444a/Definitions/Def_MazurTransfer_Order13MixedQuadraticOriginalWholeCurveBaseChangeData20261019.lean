-- Prove2me | Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalWholeCurveBaseChangeData20261019
-- name    : MazurTransfer_Order13MixedQuadraticOriginalWholeCurveBaseChangeData20261019
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-19T04:59:03.182226+00:00
-- url     : https://prove2.me/theorems/3b388572-58a1-4fe6-ac36-451cc008ec26
-- title:
--   Original whole mixed quadratic curve base change and cartesian square
-- statement:
--   The original gluing descent morphism, transition compatibility, chart pullback squares, whole cartesian base square and actual whole-curve base-change isomorphism. Fifty-two public types and six whole values, sixteen private helper types, sixty-one required context types and eleven context values, and the original distinct-chart gluing helper type are checked in independent default-heartbeat processes. Named downstream consumer: geometric integrality and the whole dyadic rational-fibre and Picard comparisons.
-- source:
--   MazurTheorem complete original mixed quadratic coefficient maps, transition naturality, gluing and whole base-change square; Vas and contributors; Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalCoefficientAndOverlapBaseChangeMapsData20261019
import Definitions.Def_MazurTransfer_Order13MixedQuadraticOriginalGluedCurveData20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual gluing relation on distinct charts of GlueData'.
Named downstream consumer: the mixed quadratic whole-curve comparison.
-/
noncomputable section
namespace MazurTransfer.MixedQuadraticGlueDataOriginalDistinctCompatibility20261019
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] (D : GlueData' C)
variable [HasMulticoequalizer (GlueData.ofGlueData' D).diagram]

theorem relation (i j : D.J) (h : i ≠ j) :
    D.f i j h ≫ (GlueData.ofGlueData' D).ι i =
      D.t i j h ≫ D.f j i h.symm ≫ (GlueData.ofGlueData' D).ι j := by
  have hh := (GlueData.ofGlueData' D).glue_condition i j
  dsimp only [GlueData.ofGlueData', GlueData'.f'] at hh
  simp only [dif_neg h, dif_neg h.symm, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at hh
  rw [cancel_epi] at hh
  exact hh.symm

end MazurTransfer.MixedQuadraticGlueDataOriginalDistinctCompatibility20261019
#print axioms MazurTransfer.MixedQuadraticGlueDataOriginalDistinctCompatibility20261019.relation

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts the complete checked two-chart descent proof of MazurTheorem at
54d43d8dda8a6fcf069cc02a815f850d762c5c0c to an arbitrary target scheme.
Design boundary: the actual universal gluing morphism for compatible chart
maps. Named downstream consumer: the genuine change-of-base morphism of the
mixed quadratic integral order-thirteen curve, with compatibility proved separately.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticGluedCurveMaps
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Order13MixedQuadraticGluedCurve
universe u
variable (K : Type u) [CommRing K]

private theorem ordinary_ne_reciprocal : (Chart.ordinary : Chart.{u}) ≠ Chart.reciprocal := by
  intro h
  cases h

private theorem reciprocal_ne_ordinary : (Chart.reciprocal : Chart.{u}) ≠ Chart.ordinary := by
  intro h
  cases h

def desc {Y : Scheme.{u}} (δ : ∀ i : Chart.{u}, chartScheme K i ⟶ Y)
    (hδ : ∀ (i j : Chart.{u}) (h : i ≠ j),
      overlapInclusion K i j h ≫ δ i =
        overlapTransition K i j h ≫ overlapInclusion K j i h.symm ≫ δ j) :
    curveScheme K ⟶ Y := by
    letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
    exact Limits.Multicoequalizer.desc (glueData K).toGlueData.diagram
      Y δ (by
      rintro ⟨i, j⟩
      simp only [CategoryTheory.GlueData.diagram_fst,
        CategoryTheory.GlueData.diagram_snd]
      rcases i with (_ | _) <;> rcases j with (_ | _)
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f',
          Limits.MultispanShape.prod]
        simp
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f',
          ordinary_ne_reciprocal, reciprocal_ne_ordinary,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal,
          dif_neg reciprocal_ne_ordinary, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact hδ _ _
          ordinary_ne_reciprocal
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f',
          ordinary_ne_reciprocal, reciprocal_ne_ordinary,
          Limits.MultispanShape.prod]
        simp only [dif_neg ordinary_ne_reciprocal,
          dif_neg reciprocal_ne_ordinary, Category.assoc]
        simp only [CategoryTheory.eqToHom_trans_assoc,
          CategoryTheory.eqToHom_refl, Category.id_comp]
        rw [CategoryTheory.cancel_epi]
        exact hδ _ _
          reciprocal_ne_ordinary
      · dsimp [glueData, categoricalGlueData,
          CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f',
          Limits.MultispanShape.prod]
        simp)

theorem chartMap_desc {Y : Scheme.{u}} (δ : ∀ i : Chart.{u}, chartScheme K i ⟶ Y)
    (hδ : ∀ (i j : Chart.{u}) (h : i ≠ j),
      overlapInclusion K i j h ≫ δ i =
        overlapTransition K i j h ≫ overlapInclusion K j i h.symm ≫ δ j)
    (i : Chart.{u}) :
    (glueData K).ι i ≫ desc K δ hδ = δ i := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  unfold desc
  apply Multicoequalizer.π_desc

end MazurTransfer.Order13MixedQuadraticGluedCurveMaps

#print axioms MazurTransfer.Order13MixedQuadraticGluedCurveMaps.desc
#print axioms MazurTransfer.Order13MixedQuadraticGluedCurveMaps.chartMap_desc

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted from the complete checked Order13ReciprocalTransitionBaseChange proof,
with the actual mixed quadratic rings and gluing object throughout.
Design boundary: the literal reciprocal transition commutes with the actual
chart and localization change-of-base ring maps on the entire overlap rings.
Named downstream consumer: identification of the glued integral curve's
base-changed scheme with the literal order-thirteen curve over the new base.
This does not yet construct a glued scheme isomorphism or a Picard family.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticCoefficientBaseChange
open Polynomial Algebra TensorProduct
universe u
variable (R : Type u) [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
open Order13DyadicMixedQuadraticCharts
open Order13MixedQuadraticOverlapCoordinates Order13MixedQuadraticTransitionHomomorphisms
open Order13MixedQuadraticOverlapEquivalence Order13MixedQuadraticGluedCurve

theorem ordinaryOverlapRingMap_scalar (r : R) :
    ordinaryOverlapRingMap R S (algebraMap R (OrdinaryOverlapRing R) r) =
      algebraMap S (OrdinaryOverlapRing S) (algebraMap R S r) := by
  rw [IsScalarTower.algebraMap_apply R (ordinaryCoordinateRing R) (OrdinaryOverlapRing R),
    ordinaryOverlapRingMap_algebraMap, ordinaryRingMap_algebraMap,
    ← IsScalarTower.algebraMap_apply S (ordinaryCoordinateRing S) (OrdinaryOverlapRing S)]

theorem reciprocalOverlapRingMap_scalar (r : R) :
    reciprocalOverlapRingMap R S (algebraMap R (ReciprocalOverlapRing R) r) =
      algebraMap S (ReciprocalOverlapRing S) (algebraMap R S r) := by
  rw [IsScalarTower.algebraMap_apply R (reciprocalCoordinateRing R) (ReciprocalOverlapRing R),
    reciprocalOverlapRingMap_algebraMap, reciprocalRingMap_algebraMap,
    ← IsScalarTower.algebraMap_apply S (reciprocalCoordinateRing S) (ReciprocalOverlapRing S)]

theorem ordinaryTransition_x :
    ordinaryToReciprocal R
      (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) (xCoordinate R)) =
      IsLocalization.Away.invSelf (zCoordinate R) := by
  rw [ordinaryToReciprocal_algebraMap]
  exact ordinaryToReciprocalBase_x R

theorem ordinaryTransition_y :
    ordinaryToReciprocal R
      (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) (yCoordinate R)) =
      algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R) (wCoordinate R) *
        IsLocalization.Away.invSelf (zCoordinate R) ^ 3 := by
  rw [ordinaryToReciprocal_algebraMap]
  exact ordinaryToReciprocalBase_y R

theorem ordinaryTransition_natural :
    (reciprocalOverlapRingMap R S).comp (ordinaryToReciprocal R).toRingHom =
      (ordinaryToReciprocal S).toRingHom.comp (ordinaryOverlapRingMap R S) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (xCoordinate R))
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      change reciprocalOverlapRingMap R S
          (ordinaryToReciprocal R (algebraMap R (OrdinaryOverlapRing R) r)) =
        ordinaryToReciprocal S
          (ordinaryOverlapRingMap R S (algebraMap R (OrdinaryOverlapRing R) r))
      rw [(ordinaryToReciprocal R).commutes, reciprocalOverlapRingMap_scalar,
        ordinaryOverlapRingMap_scalar, (ordinaryToReciprocal S).commutes]
    · change reciprocalOverlapRingMap R S
          (ordinaryToReciprocal R
            (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) (xCoordinate R))) =
        ordinaryToReciprocal S
          (ordinaryOverlapRingMap R S
            (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) (xCoordinate R)))
      rw [ordinaryTransition_x, reciprocalOverlapRingMap_invSelf,
        ordinaryOverlapRingMap_algebraMap, ordinaryRingMap_x, ordinaryTransition_x]
  · change reciprocalOverlapRingMap R S
        (ordinaryToReciprocal R
          (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) (yCoordinate R))) =
      ordinaryToReciprocal S
        (ordinaryOverlapRingMap R S
          (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R) (yCoordinate R)))
    rw [ordinaryTransition_y, map_mul, map_pow,
      reciprocalOverlapRingMap_algebraMap, reciprocalRingMap_w,
      reciprocalOverlapRingMap_invSelf, ordinaryOverlapRingMap_algebraMap,
      ordinaryRingMap_y, ordinaryTransition_y]

theorem ordinaryTransition_left_inverse (a : OrdinaryOverlapRing R) :
    reciprocalToOrdinary R (ordinaryToReciprocal R a) = a := by
  simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
    DFunLike.congr_fun (reciprocalToOrdinary_comp_ordinaryToReciprocal R) a

theorem ordinaryTransition_right_inverse (a : ReciprocalOverlapRing R) :
    ordinaryToReciprocal R (reciprocalToOrdinary R a) = a := by
  simpa only [AlgHom.comp_apply, AlgHom.id_apply] using
    DFunLike.congr_fun (ordinaryToReciprocal_comp_reciprocalToOrdinary R) a

theorem reciprocalTransition_natural :
    (ordinaryOverlapRingMap R S).comp (reciprocalToOrdinary R).toRingHom =
      (reciprocalToOrdinary S).toRingHom.comp (reciprocalOverlapRingMap R S) := by
  ext a
  have h := DFunLike.congr_fun (ordinaryTransition_natural R S) (reciprocalToOrdinary R a)
  change reciprocalOverlapRingMap R S
      (ordinaryToReciprocal R (reciprocalToOrdinary R a)) =
    ordinaryToReciprocal S (ordinaryOverlapRingMap R S (reciprocalToOrdinary R a)) at h
  rw [ordinaryTransition_right_inverse] at h
  change ordinaryOverlapRingMap R S (reciprocalToOrdinary R a) =
    reciprocalToOrdinary S (reciprocalOverlapRingMap R S a)
  rw [h, ordinaryTransition_left_inverse]

end MazurTransfer.Order13MixedQuadraticCoefficientBaseChange

#print axioms MazurTransfer.Order13MixedQuadraticCoefficientBaseChange.ordinaryTransition_natural
#print axioms MazurTransfer.Order13MixedQuadraticCoefficientBaseChange.reciprocalTransition_natural

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts both second-projection proofs from Order13AffineChartBaseChangeSchemeIsomorphisms.
Design boundary: the previously checked mixed affine pullback isomorphisms
have exactly the canonical coordinate ring map as second projection.
Named downstream consumer: the cartesian whole mixed curve base square.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticAffineBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts
open Order13MixedQuadraticCoefficientBaseChange
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem ordinaryChartIso_inv_snd :
    (ordinaryChartIso R S).inv ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (ordinaryToBase R) =
      Spec.map (CommRingCat.ofHom (Order13MixedQuadraticCoefficientBaseChange.ordinaryRingMap R S)) := by
  change (Spec.map (CommRingCat.ofHom
      (ordinaryAlgebraEquiv R S).toRingHom) ≫
      (pullbackSpecIso R S (ordinaryCoordinateRing R)).inv) ≫ pullback.snd _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  rfl

theorem reciprocalChartIso_inv_snd :
    (reciprocalChartIso R S).inv ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reciprocalToBase R) =
      Spec.map (CommRingCat.ofHom (Order13MixedQuadraticCoefficientBaseChange.reciprocalRingMap R S)) := by
  change (Spec.map (CommRingCat.ofHom
      (reciprocalAlgebraEquiv R S).toRingHom) ≫
      (pullbackSpecIso R S (reciprocalCoordinateRing R)).inv) ≫ pullback.snd _ _ = _
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  rfl

end MazurTransfer.Order13MixedQuadraticAffineBaseChange
#print axioms MazurTransfer.Order13MixedQuadraticAffineBaseChange.ordinaryChartIso_inv_snd
#print axioms MazurTransfer.Order13MixedQuadraticAffineBaseChange.reciprocalChartIso_inv_snd

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted from the complete checked Order13ActualCurveChangeOfBaseMorphism proof,
with the actual mixed quadratic rings and gluing object throughout.
Design boundary: the actual change-of-base morphism of the literal glued
order-thirteen curve, built from the checked coordinate and overlap maps.
Named downstream consumer: constructing the isomorphism from its base change
to the literal curve over the new ring. No such isomorphism is assumed.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticActualCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts
open Order13MixedQuadraticOverlapCoordinates Order13MixedQuadraticTransitionHomomorphisms
open Order13MixedQuadraticOverlapEquivalence Order13MixedQuadraticGluedCurve
open MazurTransfer.Order13MixedQuadraticCoefficientBaseChange
universe u
variable (K : Type u) [CommRing K]

theorem ordinary_reciprocal_glue :
    Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K))) ≫
      ordinaryChartMap K =
    Spec.map (CommRingCat.ofHom (reciprocalToOrdinary K).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing K) (ReciprocalOverlapRing K))) ≫
        reciprocalChartMap K := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  exact MazurTransfer.MixedQuadraticGlueDataOriginalDistinctCompatibility20261019.relation (categoricalGlueData K)
    Chart.ordinary Chart.reciprocal (by intro h; cases h)

theorem reciprocal_ordinary_glue :
    Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing K) (ReciprocalOverlapRing K))) ≫
      reciprocalChartMap K =
    Spec.map (CommRingCat.ofHom (ordinaryToReciprocal K).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K))) ≫
        ordinaryChartMap K := by
  have H := congrArg (fun f => (overlapSchemeIso K).inv ≫ f) (ordinary_reciprocal_glue K)
  rw [← overlapSchemeIso_hom K] at H
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at H
  exact H.symm

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

@[reassoc]
theorem ordinary_inclusion_natural :
    Spec.map (CommRingCat.ofHom (ordinaryOverlapRingMap R S)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R))) =
    Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing S) (OrdinaryOverlapRing S))) ≫
      Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact ordinaryOverlapRingMap_algebraMap R S a

@[reassoc]
theorem reciprocal_inclusion_natural :
    Spec.map (CommRingCat.ofHom (reciprocalOverlapRingMap R S)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R))) =
    Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing S) (ReciprocalOverlapRing S))) ≫
      Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact reciprocalOverlapRingMap_algebraMap R S a

theorem ordinary_transition_natural :
    Spec.map (CommRingCat.ofHom (ordinaryOverlapRingMap R S)) ≫
      Spec.map (CommRingCat.ofHom (reciprocalToOrdinary R).toRingHom) =
    Spec.map (CommRingCat.ofHom (reciprocalToOrdinary S).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (reciprocalOverlapRingMap R S)) := by
  have H := congrArg (fun f : ReciprocalOverlapRing R →+* OrdinaryOverlapRing S =>
    Spec.map (CommRingCat.ofHom f)) (reciprocalTransition_natural R S)
  exact (Spec.map_comp (CommRingCat.ofHom (reciprocalToOrdinary R).toRingHom)
    (CommRingCat.ofHom (ordinaryOverlapRingMap R S))).symm.trans
    (H.trans (Spec.map_comp (CommRingCat.ofHom (reciprocalOverlapRingMap R S))
      (CommRingCat.ofHom (reciprocalToOrdinary S).toRingHom)))

theorem reciprocal_transition_natural :
    Spec.map (CommRingCat.ofHom (reciprocalOverlapRingMap R S)) ≫
      Spec.map (CommRingCat.ofHom (ordinaryToReciprocal R).toRingHom) =
    Spec.map (CommRingCat.ofHom (ordinaryToReciprocal S).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (ordinaryOverlapRingMap R S)) := by
  have H := congrArg (fun f : OrdinaryOverlapRing R →+* ReciprocalOverlapRing S =>
    Spec.map (CommRingCat.ofHom f)) (ordinaryTransition_natural R S)
  exact (Spec.map_comp (CommRingCat.ofHom (ordinaryToReciprocal R).toRingHom)
    (CommRingCat.ofHom (reciprocalOverlapRingMap R S))).symm.trans
    (H.trans (Spec.map_comp (CommRingCat.ofHom (ordinaryOverlapRingMap R S))
      (CommRingCat.ofHom (ordinaryToReciprocal S).toRingHom)))

def chartMapToOriginal : ∀ i : Chart.{u}, chartScheme S i ⟶ curveScheme R
  | .ordinary => Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)) ≫ ordinaryChartMap R
  | .reciprocal => Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)) ≫ reciprocalChartMap R

private theorem paste_compatible {A B C D E F G H X : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ X)
    (d : A ⟶ D) (e : D ⟶ E) (f : E ⟶ F) (g : F ⟶ X)
    (m : A ⟶ G) (n : G ⟶ C) (t : G ⟶ H) (v : D ⟶ H) (w : H ⟶ F)
    (ha : m ≫ n = a ≫ b) (hb : v ≫ w = e ≫ f)
    (ht : m ≫ t = d ≫ v) (hg : n ≫ c = t ≫ w ≫ g) :
    a ≫ b ≫ c = d ≫ e ≫ f ≫ g := by
  rw [← Category.assoc, ← ha, Category.assoc, hg, ← Category.assoc, ht]
  simp only [Category.assoc]
  rw [← Category.assoc v w g, hb]
  simp only [Category.assoc]

theorem chartMapToOriginal_compatible (i j : Chart.{u}) (h : i ≠ j) :
    overlapInclusion S i j h ≫ chartMapToOriginal R S i =
      overlapTransition S i j h ≫ overlapInclusion S j i h.symm ≫ chartMapToOriginal R S j := by
  cases i <;> cases j
  · exact (h rfl).elim
  · exact paste_compatible
      (Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing S) (OrdinaryOverlapRing S))))
      (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S))) (ordinaryChartMap R)
      (Spec.map (CommRingCat.ofHom (reciprocalToOrdinary S).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing S) (ReciprocalOverlapRing S))))
      (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S))) (reciprocalChartMap R)
      (Spec.map (CommRingCat.ofHom (ordinaryOverlapRingMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R))))
      (Spec.map (CommRingCat.ofHom (reciprocalToOrdinary R).toRingHom))
      (Spec.map (CommRingCat.ofHom (reciprocalOverlapRingMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R))))
      (ordinary_inclusion_natural R S) (reciprocal_inclusion_natural R S)
      (ordinary_transition_natural R S) (ordinary_reciprocal_glue R)
  · exact paste_compatible
      (Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing S) (ReciprocalOverlapRing S))))
      (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S))) (reciprocalChartMap R)
      (Spec.map (CommRingCat.ofHom (ordinaryToReciprocal S).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing S) (OrdinaryOverlapRing S))))
      (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S))) (ordinaryChartMap R)
      (Spec.map (CommRingCat.ofHom (reciprocalOverlapRingMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R))))
      (Spec.map (CommRingCat.ofHom (ordinaryToReciprocal R).toRingHom))
      (Spec.map (CommRingCat.ofHom (ordinaryOverlapRingMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R))))
      (reciprocal_inclusion_natural R S) (ordinary_inclusion_natural R S)
      (reciprocal_transition_natural R S) (reciprocal_ordinary_glue R)
  · exact (h rfl).elim

def curveMap : curveScheme S ⟶ curveScheme R :=
  Order13MixedQuadraticGluedCurveMaps.desc S (chartMapToOriginal R S) (chartMapToOriginal_compatible R S)

@[reassoc]
theorem ordinaryChartMap_curveMap :
    ordinaryChartMap S ≫ curveMap R S =
      Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)) ≫ ordinaryChartMap R :=
  Order13MixedQuadraticGluedCurveMaps.chartMap_desc S (chartMapToOriginal R S)
    (chartMapToOriginal_compatible R S) Chart.ordinary

@[reassoc]
theorem reciprocalChartMap_curveMap :
    reciprocalChartMap S ≫ curveMap R S =
      Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)) ≫ reciprocalChartMap R :=
  Order13MixedQuadraticGluedCurveMaps.chartMap_desc S (chartMapToOriginal R S)
    (chartMapToOriginal_compatible R S) Chart.reciprocal

end MazurTransfer.Order13MixedQuadraticActualCurveBaseChange

#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.ordinary_reciprocal_glue
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.curveMap
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.ordinaryChartMap_curveMap
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.reciprocalChartMap_curveMap

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted from the complete checked Order13ActualCurveChangeOfBaseSquare proof,
with the actual mixed quadratic rings and gluing object throughout.
Design boundary: base compatibility and the actual canonical morphism from
our literal order-thirteen curve to the fibre product of the original curve.
Named downstream consumer: the whole glued-curve base-change isomorphism.
No isomorphism, properness, or compatibility hypothesis is supplied.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticActualCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts
open Order13MixedQuadraticOverlapCoordinates Order13MixedQuadraticTransitionHomomorphisms
open Order13MixedQuadraticOverlapEquivalence Order13MixedQuadraticGluedCurve
open MazurTransfer.Order13MixedQuadraticCoefficientBaseChange
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem ordinary_base_natural :
    Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)) ≫ ordinaryToBase R =
      ordinaryToBase S ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  change Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (ordinaryCoordinateRing R))) =
    Spec.map (CommRingCat.ofHom (algebraMap S (ordinaryCoordinateRing S))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S))
  have h : (ordinaryRingMap R S).comp (algebraMap R (ordinaryCoordinateRing R)) =
      (algebraMap S (ordinaryCoordinateRing S)).comp (algebraMap R S) :=
    RingHom.ext (ordinaryRingMap_algebraMap R S)
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext h)

theorem reciprocal_base_natural :
    Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)) ≫ reciprocalToBase R =
      reciprocalToBase S ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  change Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (reciprocalCoordinateRing R))) =
    Spec.map (CommRingCat.ofHom (algebraMap S (reciprocalCoordinateRing S))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S))
  have h : (reciprocalRingMap R S).comp (algebraMap R (reciprocalCoordinateRing R)) =
      (algebraMap S (reciprocalCoordinateRing S)).comp (algebraMap R S) :=
    RingHom.ext (reciprocalRingMap_algebraMap R S)
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext h)

private theorem base_triangle {A B C D E F : Scheme.{u}}
    (i : A ⟶ C) (j : B ⟶ D) (m : A ⟶ B) (f : C ⟶ D)
    (p : C ⟶ E) (q : D ⟶ F) (a : A ⟶ E) (b : B ⟶ F) (g : E ⟶ F)
    (hi : i ≫ f = m ≫ j) (hj : j ≫ q = b) (hp : i ≫ p = a)
    (hm : m ≫ b = a ≫ g) : i ≫ (f ≫ q) = i ≫ (p ≫ g) := by
  rw [← Category.assoc, hi, Category.assoc, hj, ← Category.assoc, hp]
  exact hm

theorem curveMap_base :
    curveMap R S ≫ curveToBase R =
      curveToBase S ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
  apply (glueData S).openCover.hom_ext
  intro i
  cases i
  · exact base_triangle (ordinaryChartMap S) (ordinaryChartMap R)
      (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S))) (curveMap R S)
      (curveToBase S) (curveToBase R) (ordinaryToBase S) (ordinaryToBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (ordinaryChartMap_curveMap R S) (ordinaryChartMap_curveToBase R)
      (ordinaryChartMap_curveToBase S) (ordinary_base_natural R S)
  · exact base_triangle (reciprocalChartMap S) (reciprocalChartMap R)
      (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S))) (curveMap R S)
      (curveToBase S) (curveToBase R) (reciprocalToBase S) (reciprocalToBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (reciprocalChartMap_curveMap R S) (reciprocalChartMap_curveToBase R)
      (reciprocalChartMap_curveToBase S) (reciprocal_base_natural R S)

def curveBaseChangeLift : curveScheme S ⟶
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) (curveToBase R) :=
  pullback.lift (curveToBase S) (curveMap R S) (curveMap_base R S).symm

@[reassoc]
theorem curveBaseChangeLift_fst :
    curveBaseChangeLift R S ≫ pullback.fst _ _ = curveToBase S :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem curveBaseChangeLift_snd :
    curveBaseChangeLift R S ≫ pullback.snd _ _ = curveMap R S :=
  pullback.lift_snd _ _ _

end MazurTransfer.Order13MixedQuadraticActualCurveBaseChange

#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.curveMap_base
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.curveBaseChangeLift
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.curveBaseChangeLift_fst
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.curveBaseChangeLift_snd

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted from the complete checked Order13OverlapBaseChangePullbackSquares proof,
with the actual mixed quadratic rings and gluing object throughout.
Design boundary: both actual localized-chart change-of-base squares are
scheme-theoretic pullbacks. Named downstream consumer: cartesianity of the
chart inclusions in the actual whole glued curve change-of-base map.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticActualCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts
open Order13MixedQuadraticOverlapCoordinates Order13MixedQuadraticTransitionHomomorphisms
open Order13MixedQuadraticOverlapEquivalence Order13MixedQuadraticGluedCurve
open MazurTransfer.Order13MixedQuadraticCoefficientBaseChange
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem ordinaryOverlap_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (ordinaryOverlapRingMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing S) (OrdinaryOverlapRing S))))
      (Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R))))
      (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S))) := by
  letI : IsLocalization ((Submonoid.powers (xCoordinate R)).map (ordinaryRingMap R S))
      (OrdinaryOverlapRing S) := by
    rw [Submonoid.map_powers, ordinaryRingMap_x]
    infer_instance
  have h : (ordinaryOverlapRingMap R S).comp
      (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R)) =
      (algebraMap (ordinaryCoordinateRing S) (OrdinaryOverlapRing S)).comp (ordinaryRingMap R S) :=
    RingHom.ext (ordinaryOverlapRingMap_algebraMap R S)
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (ordinaryRingMap R S)
      (ordinaryOverlapRingMap R S) h (Submonoid.powers (xCoordinate R)))).flip

theorem reciprocalOverlap_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (reciprocalOverlapRingMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing S) (ReciprocalOverlapRing S))))
      (Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R))))
      (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S))) := by
  letI : IsLocalization ((Submonoid.powers (zCoordinate R)).map (reciprocalRingMap R S))
      (ReciprocalOverlapRing S) := by
    rw [Submonoid.map_powers, reciprocalRingMap_z]
    infer_instance
  have h : (reciprocalOverlapRingMap R S).comp
      (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R)) =
      (algebraMap (reciprocalCoordinateRing S) (ReciprocalOverlapRing S)).comp (reciprocalRingMap R S) :=
    RingHom.ext (reciprocalOverlapRingMap_algebraMap R S)
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (reciprocalRingMap R S)
      (reciprocalOverlapRingMap R S) h (Submonoid.powers (zCoordinate R)))).flip

end MazurTransfer.Order13MixedQuadraticActualCurveBaseChange

#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.ordinaryOverlap_isPullback
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.reciprocalOverlap_isPullback

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted from the complete checked Order13ReciprocalOverlapBaseChangePullbackSquares proof,
with the actual mixed quadratic rings and gluing object throughout.
Design boundary: the actual overlap pullbacks also viewed in the opposite
chart coordinates. Named downstream consumer: the full glued curve chart
preimage identification, before whole-curve base-change.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticActualCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts
open Order13MixedQuadraticOverlapCoordinates Order13MixedQuadraticTransitionHomomorphisms
open Order13MixedQuadraticOverlapEquivalence Order13MixedQuadraticGluedCurve
open MazurTransfer.Order13MixedQuadraticCoefficientBaseChange
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem ordinaryOverlapOverReciprocal_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (ordinaryOverlapRingMap R S)))
      (Spec.map (CommRingCat.ofHom (reciprocalToOrdinary S).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing S) (ReciprocalOverlapRing S))))
      (Spec.map (CommRingCat.ofHom (reciprocalToOrdinary R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing R) (ReciprocalOverlapRing R))))
      (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S))) := by
  apply (reciprocalOverlap_isPullback R S).of_iso'
    (overlapSchemeIso S) (overlapSchemeIso R)
    (Iso.refl (reciprocalScheme S)) (Iso.refl (reciprocalScheme R))
  · rw [overlapSchemeIso_hom, overlapSchemeIso_hom, ordinary_transition_natural]
  · simp only [overlapSchemeIso_hom, Iso.refl_hom]
    exact (Category.comp_id _).symm
  · simp only [overlapSchemeIso_hom, Iso.refl_hom]
    exact (Category.comp_id _).symm
  · simp only [Iso.refl_hom]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem reciprocalOverlapOverOrdinary_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (reciprocalOverlapRingMap R S)))
      (Spec.map (CommRingCat.ofHom (ordinaryToReciprocal S).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing S) (OrdinaryOverlapRing S))))
      (Spec.map (CommRingCat.ofHom (ordinaryToReciprocal R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing R) (OrdinaryOverlapRing R))))
      (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S))) := by
  apply (ordinaryOverlap_isPullback R S).of_iso'
    (overlapSchemeIso S).symm (overlapSchemeIso R).symm
    (Iso.refl (Order13DyadicMixedQuadraticCharts.ordinaryScheme S))
    (Iso.refl (Order13DyadicMixedQuadraticCharts.ordinaryScheme R))
  · simp only [Iso.symm_hom, overlapSchemeIso_inv]
    exact (reciprocal_transition_natural R S).symm
  · simp only [Iso.symm_hom, overlapSchemeIso_inv, Iso.refl_hom]
    exact (Category.comp_id _).symm
  · simp only [Iso.symm_hom, overlapSchemeIso_inv, Iso.refl_hom]
    exact (Category.comp_id _).symm
  · simp only [Iso.refl_hom]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

end MazurTransfer.Order13MixedQuadraticActualCurveBaseChange
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.ordinaryOverlapOverReciprocal_isPullback
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.reciprocalOverlapOverOrdinary_isPullback

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted from the complete checked Order13ActualChartIntersectionPullback proof,
with the actual mixed quadratic rings and gluing object throughout.
Design boundary: identify the literal localized overlap as the actual
intersection of the two affine charts in our glued curve.
Named downstream consumer: cartesianity and whole-curve base-change.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticActualCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts
open Order13MixedQuadraticOverlapCoordinates Order13MixedQuadraticTransitionHomomorphisms
open Order13MixedQuadraticOverlapEquivalence Order13MixedQuadraticGluedCurve
universe u
variable (K : Type u) [CommRing K]

theorem ordinary_reciprocal_intersection :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K))))
      (Spec.map (CommRingCat.ofHom (reciprocalToOrdinary K).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing K) (ReciprocalOverlapRing K))))
      (ordinaryChartMap K) (reciprocalChartMap K) := by
  classical
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData K)
  have hor : (Chart.ordinary : Chart.{u}) ≠ Chart.reciprocal := by intro h; cases h
  have hro : (Chart.reciprocal : Chart.{u}) ≠ Chart.ordinary := hor.symm
  have comm : CommSq
      (Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K))))
      (Spec.map (CommRingCat.ofHom (reciprocalToOrdinary K).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing K) (ReciprocalOverlapRing K))))
      (ordinaryChartMap K) (reciprocalChartMap K) :=
    ⟨(ordinary_reciprocal_glue K).trans (Category.assoc
      (Spec.map (CommRingCat.ofHom (reciprocalToOrdinary K).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing K) (ReciprocalOverlapRing K))))
      (reciprocalChartMap K)).symm⟩
  have hpt : (glueData K).V ⟨Chart.ordinary, Chart.reciprocal⟩ =
      Spec (CommRingCat.of (OrdinaryOverlapRing K)) := by
    dsimp only [glueData, categoricalGlueData, CategoryTheory.GlueData.ofGlueData']
    exact dif_neg hor
  apply IsPullback.of_isLimit' comm
  refine IsLimit.ofIsoLimit
    ((glueData K).vPullbackConeIsLimit Chart.ordinary Chart.reciprocal) ?_
  refine PullbackCone.ext (eqToIso hpt) ?_ ?_
  · change (glueData K).f Chart.ordinary Chart.reciprocal =
        (eqToIso hpt).hom ≫
          Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K)))
    dsimp only [glueData, categoricalGlueData,
      CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
    simp only [dif_neg hor]
    rfl
  · change (glueData K).t Chart.ordinary Chart.reciprocal ≫
        (glueData K).f Chart.reciprocal Chart.ordinary =
      (eqToIso hpt).hom ≫
        (Spec.map (CommRingCat.ofHom (reciprocalToOrdinary K).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing K) (ReciprocalOverlapRing K))))
    dsimp only [glueData, categoricalGlueData,
      CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
    simp only [dif_neg hor, dif_neg hro, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rfl

theorem reciprocal_ordinary_intersection :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing K) (ReciprocalOverlapRing K))))
      (Spec.map (CommRingCat.ofHom (ordinaryToReciprocal K).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing K) (OrdinaryOverlapRing K))))
      (reciprocalChartMap K) (ordinaryChartMap K) := by
  apply (ordinary_reciprocal_intersection K).flip.of_iso'
    (overlapSchemeIso K).symm (Iso.refl (reciprocalScheme K))
    (Iso.refl (Order13DyadicMixedQuadraticCharts.ordinaryScheme K)) (Iso.refl (curveScheme K))
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
    rw [← overlapSchemeIso_hom, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    exact (Category.comp_id _).symm
  · simp only [Iso.symm_hom, overlapSchemeIso_inv, Iso.refl_hom]
    exact (Category.comp_id _).symm
  · simp only [Iso.refl_hom, Category.comp_id]
    exact Category.id_comp _
  · simp only [Iso.refl_hom, Category.comp_id]
    exact Category.id_comp _

end MazurTransfer.Order13MixedQuadraticActualCurveBaseChange
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.ordinary_reciprocal_intersection

#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.reciprocal_ordinary_intersection

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted from the complete checked Order13ActualChartBaseChangeCartesian proof,
with the actual mixed quadratic rings and gluing object throughout.
Design boundary: the two actual affine charts are their whole-curve
change-of-base preimages. Named downstream consumer: proving the canonical
whole-curve fibre-product morphism is an isomorphism, without assuming a
chart dictionary or preimage compatibility.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticActualCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts
open Order13MixedQuadraticOverlapCoordinates Order13MixedQuadraticTransitionHomomorphisms
open Order13MixedQuadraticOverlapEquivalence Order13MixedQuadraticGluedCurve
open MazurTransfer.Order13MixedQuadraticCoefficientBaseChange
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

private theorem selfChartPullback {A B X Y : Scheme.{u}}
    (i : A ⟶ X) (j : B ⟶ Y) (m : A ⟶ B) (f : X ⟶ Y)
    (hi : Mono i) (hj : Mono j) (h : i ≫ f = m ≫ j) :
    IsPullback (pullback.snd i i) (pullback.fst i i ≫ m) (i ≫ f) j := by
  letI := hi
  letI := hj
  letI := (IsPullback.of_hasPullback i i).isIso_snd_iso_of_mono
  apply IsPullback.of_horiz_isIso_mono
  constructor
  rw [← Category.assoc, ← pullback.condition, Category.assoc, h, ← Category.assoc]

private theorem offChartPullback {O A B C X Y : Scheme.{u}}
    (a : O ⟶ A) (b : O ⟶ B) (i : A ⟶ X) (j : B ⟶ X)
    (m : A ⟶ C) (f : X ⟶ Y) (k : C ⟶ Y)
    (h : IsPullback a b i j) (hoff : IsPullback b (a ≫ m) (j ≫ f) k) :
    IsPullback (pullback.snd i j) (pullback.fst i j ≫ m) (j ≫ f) k := by
  apply hoff.of_iso h.isoPullback (Iso.refl B) (Iso.refl C) (Iso.refl Y)
  · simp only [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_snd]
  · simp only [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_fst_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem ordinaryChartPreimage_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)))
      (ordinaryChartMap S) (ordinaryChartMap R) (curveMap R S) := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData S)
  have localOff : IsPullback
      (Spec.map (CommRingCat.ofHom (reciprocalToOrdinary S).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing S) (ReciprocalOverlapRing S))))
      (Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing S) (OrdinaryOverlapRing S))) ≫
        Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)))
      (reciprocalChartMap S ≫ curveMap R S) (ordinaryChartMap R) := by
    have H := (ordinaryOverlapOverReciprocal_isPullback R S).flip.paste_vert
      (ordinary_reciprocal_intersection R).flip
    rw [ordinary_inclusion_natural, ← reciprocalChartMap_curveMap] at H
    exact H
  have global : IsPullback (ordinaryChartMap S)
      (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)))
      (curveMap R S) (ordinaryChartMap R) := by
    apply Scheme.isPullback_of_openCover _ _ _ _ (glueData S).openCover
    intro i
    cases i
    · change IsPullback (pullback.snd (ordinaryChartMap S) (ordinaryChartMap S))
        (pullback.fst (ordinaryChartMap S) (ordinaryChartMap S) ≫
          Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)))
        (ordinaryChartMap S ≫ curveMap R S) (ordinaryChartMap R)
      exact selfChartPullback (ordinaryChartMap S) (ordinaryChartMap R)
        (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S))) (curveMap R S)
        (IsOpenImmersion.mono _) (IsOpenImmersion.mono _) (ordinaryChartMap_curveMap R S)
    · change IsPullback (pullback.snd (ordinaryChartMap S) (reciprocalChartMap S))
        (pullback.fst (ordinaryChartMap S) (reciprocalChartMap S) ≫
          Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)))
        (reciprocalChartMap S ≫ curveMap R S) (ordinaryChartMap R)
      exact offChartPullback _ _ (ordinaryChartMap S) (reciprocalChartMap S)
        (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S))) (curveMap R S) (ordinaryChartMap R)
        (ordinary_reciprocal_intersection S) localOff

  exact global.flip

theorem reciprocalChartPreimage_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)))
      (reciprocalChartMap S) (reciprocalChartMap R) (curveMap R S) := by
  letI := Scheme.GlueData.instHasMulticoequalizerDiagram (glueData S)
  have localOff : IsPullback
      (Spec.map (CommRingCat.ofHom (ordinaryToReciprocal S).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (ordinaryCoordinateRing S) (OrdinaryOverlapRing S))))
      (Spec.map (CommRingCat.ofHom (algebraMap (reciprocalCoordinateRing S) (ReciprocalOverlapRing S))) ≫
        Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)))
      (ordinaryChartMap S ≫ curveMap R S) (reciprocalChartMap R) := by
    have H := (reciprocalOverlapOverOrdinary_isPullback R S).flip.paste_vert
      (reciprocal_ordinary_intersection R).flip
    rw [reciprocal_inclusion_natural, ← ordinaryChartMap_curveMap] at H
    exact H
  have global : IsPullback (reciprocalChartMap S)
      (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)))
      (curveMap R S) (reciprocalChartMap R) := by
    apply Scheme.isPullback_of_openCover _ _ _ _ (glueData S).openCover
    intro i
    cases i
    · change IsPullback (pullback.snd (reciprocalChartMap S) (ordinaryChartMap S))
        (pullback.fst (reciprocalChartMap S) (ordinaryChartMap S) ≫
          Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)))
        (ordinaryChartMap S ≫ curveMap R S) (reciprocalChartMap R)
      exact offChartPullback _ _ (reciprocalChartMap S) (ordinaryChartMap S)
        (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S))) (curveMap R S) (reciprocalChartMap R)
        (reciprocal_ordinary_intersection S) localOff

    · change IsPullback (pullback.snd (reciprocalChartMap S) (reciprocalChartMap S))
        (pullback.fst (reciprocalChartMap S) (reciprocalChartMap S) ≫
          Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)))
        (reciprocalChartMap S ≫ curveMap R S) (reciprocalChartMap R)
      exact selfChartPullback (reciprocalChartMap S) (reciprocalChartMap R)
        (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S))) (curveMap R S)
        (IsOpenImmersion.mono _) (IsOpenImmersion.mono _) (reciprocalChartMap_curveMap R S)
  exact global.flip

end MazurTransfer.Order13MixedQuadraticActualCurveBaseChange
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.ordinaryChartPreimage_isPullback
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.reciprocalChartPreimage_isPullback

end
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted from the complete checked Order13WholeCurveBaseChangeIsomorphism proof,
with the actual mixed quadratic rings and gluing object throughout.
Design boundary: for arbitrary commutative base rings, the whole literal
order-thirteen glued curve over the new ring is the scheme-theoretic base
change of the original curve. Named downstream consumer: the compatible
actual integral curve family and its Picard family used in good reduction.
No chart dictionary, isomorphism, or fibre compatibility is assumed.
-/
noncomputable section
namespace MazurTransfer.Order13MixedQuadraticActualCurveBaseChange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Order13DyadicMixedQuadraticCharts
open Order13MixedQuadraticOverlapCoordinates Order13MixedQuadraticTransitionHomomorphisms
open Order13MixedQuadraticOverlapEquivalence Order13MixedQuadraticGluedCurve
open MazurTransfer.Order13MixedQuadraticCoefficientBaseChange
open MazurTransfer.Order13MixedQuadraticAffineBaseChange
universe u
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

theorem ordinaryChartBase_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)))
      (ordinaryToBase S) (ordinaryToBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have comm : CommSq (ordinaryToBase S)
      (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (ordinaryToBase R) :=
    ⟨(ordinary_base_natural R S).symm⟩
  exact (IsPullback.of_iso_pullback comm (ordinaryChartIso R S).symm
    (ordinaryChartIso_inv_fst R S) (ordinaryChartIso_inv_snd R S)).flip

theorem reciprocalChartBase_isPullback :
    IsPullback (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)))
      (reciprocalToBase S) (reciprocalToBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  have comm : CommSq (reciprocalToBase S)
      (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (reciprocalToBase R) :=
    ⟨(reciprocal_base_natural R S).symm⟩
  exact (IsPullback.of_iso_pullback comm (reciprocalChartIso R S).symm
    (reciprocalChartIso_inv_fst R S) (reciprocalChartIso_inv_snd R S)).flip

private theorem chartBasePullback {A B X Y S T : Scheme.{u}}
    (i : A ⟶ X) (j : B ⟶ Y) (m : A ⟶ B) (f : X ⟶ Y)
    (p : X ⟶ S) (q : Y ⟶ T) (a : A ⟶ S) (b : B ⟶ T) (g : S ⟶ T)
    (hpre : IsPullback m i j f) (hbase : IsPullback m a b g)
    (hi : i ≫ p = a) (hj : j ≫ q = b) :
    IsPullback (pullback.snd f j) (pullback.fst f j ≫ p) (j ≫ q) g := by
  rw [hj]
  apply hbase.of_iso hpre.flip.isoPullback (Iso.refl B) (Iso.refl S) (Iso.refl T)
  · simp only [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_snd]
  · simp only [Iso.refl_hom, Category.comp_id, IsPullback.isoPullback_hom_fst_assoc, hi]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem wholeCurve_isPullback :
    IsPullback (curveMap R S) (curveToBase S) (curveToBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (glueData R).openCover
  intro i
  cases i
  · exact chartBasePullback (ordinaryChartMap S) (ordinaryChartMap R)
      (Spec.map (CommRingCat.ofHom (ordinaryRingMap R S))) (curveMap R S)
      (curveToBase S) (curveToBase R) (ordinaryToBase S) (ordinaryToBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (ordinaryChartPreimage_isPullback R S) (ordinaryChartBase_isPullback R S)
      (ordinaryChartMap_curveToBase S) (ordinaryChartMap_curveToBase R)
  · exact chartBasePullback (reciprocalChartMap S) (reciprocalChartMap R)
      (Spec.map (CommRingCat.ofHom (reciprocalRingMap R S))) (curveMap R S)
      (curveToBase S) (curveToBase R) (reciprocalToBase S) (reciprocalToBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (reciprocalChartPreimage_isPullback R S) (reciprocalChartBase_isPullback R S)
      (reciprocalChartMap_curveToBase S) (reciprocalChartMap_curveToBase R)

def wholeCurveBaseChangeIso :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) (curveToBase R) ≅ curveScheme S :=
  (wholeCurve_isPullback R S).flip.isoPullback.symm

theorem wholeCurveBaseChangeIso_inv_eq :
    (wholeCurveBaseChangeIso R S).inv = curveBaseChangeLift R S := by
  apply pullback.hom_ext
  · exact (wholeCurve_isPullback R S).flip.isoPullback_hom_fst.trans
      (curveBaseChangeLift_fst R S).symm
  · exact (wholeCurve_isPullback R S).flip.isoPullback_hom_snd.trans
      (curveBaseChangeLift_snd R S).symm

theorem curveBaseChangeLift_isIso : IsIso (curveBaseChangeLift R S) := by
  rw [← wholeCurveBaseChangeIso_inv_eq]
  infer_instance

theorem wholeCurveBaseChangeIso_inv_fst :
    (wholeCurveBaseChangeIso R S).inv ≫ pullback.fst _ _ = curveToBase S := by
  rw [wholeCurveBaseChangeIso_inv_eq, curveBaseChangeLift_fst]

theorem wholeCurveBaseChangeIso_inv_snd :
    (wholeCurveBaseChangeIso R S).inv ≫ pullback.snd _ _ = curveMap R S := by
  rw [wholeCurveBaseChangeIso_inv_eq, curveBaseChangeLift_snd]

end MazurTransfer.Order13MixedQuadraticActualCurveBaseChange
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.wholeCurve_isPullback
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.wholeCurveBaseChangeIso
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.curveBaseChangeLift_isIso
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.wholeCurveBaseChangeIso_inv_fst
#print axioms MazurTransfer.Order13MixedQuadraticActualCurveBaseChange.wholeCurveBaseChangeIso_inv_snd

end


