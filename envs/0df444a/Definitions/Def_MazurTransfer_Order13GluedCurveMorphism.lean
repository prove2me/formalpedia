-- Prove2me | Definitions.Def_MazurTransfer_Order13GluedCurveMorphism
-- name    : MazurTransfer_Order13GluedCurveMorphism
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T03:12:07.741377+00:00
-- url     : https://prove2.me/theorems/bc13d29c-9800-4d72-969f-2836a2b5597a
-- title:
--   Gluing compatible chart maps from the actual order-thirteen curve
-- statement:
--   Let $K$ be a commutative ring, $C_K$ the fixed curve glued from its ordinary and reciprocal charts $C_i$, and $Y$ any scheme. Given morphisms $\delta_i:C_i\to Y$ agreeing on the specified overlaps, this interface constructs $d:C_K\to Y$ with
--   $$d\circ\iota_i=\delta_i\qquad\text{for each chart }i,$$
--   where $\iota_i:C_i\to C_K$ are the actual chart inclusions.
--
--   The construction uses the multicoequalizer defining this actual glued curve. It supplies the change-of-base morphism once compatibility of its chart maps has been proved separately.
-- source:
--   Unchanged constructor and chart-restriction proof from the checked MazurTheorem source Order13GluedCurveMorphismUniversalProperty.lean. The Lean syntax-oracle header range replaces an unused broad base-change import with Mathlib and the public explicit-curve definition. Both complete original public types are checked by closed kernel witnesses. Adaptation of the two-chart descent proof of MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Vas and contributors, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapts the complete checked two-chart descent proof of MazurTheorem at
54d43d8dda8a6fcf069cc02a815f850d762c5c0c to an arbitrary target scheme.
Design boundary: the actual universal gluing morphism for compatible chart
maps. Named downstream consumer: the genuine change-of-base morphism of the
literal integral order-thirteen curve, with compatibility proved separately.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve


noncomputable section
namespace MazurTransfer.Order13GluedCurveMaps
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
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

end MazurTransfer.Order13GluedCurveMaps

#print axioms MazurTransfer.Order13GluedCurveMaps.desc
#print axioms MazurTransfer.Order13GluedCurveMaps.chartMap_desc


