-- Prove2me | Definitions.Def_MazurTransfer_AffineOpenChartFunctionField
-- name    : MazurTransfer_AffineOpenChartFunctionField
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T09:36:56.315335+00:00
-- url     : https://prove2.me/theorems/98d7eb29-259f-4fed-a287-9f58a0ca838a
-- title:
--   The actual fraction-ring structure supplied by an integral affine open chart
-- statement:
--   Let $X$ be an integral scheme and let $j:\operatorname{Spec}A\hookrightarrow X$ be an open immersion with $A$ an integral domain. Its stalk map at the generic point defines an isomorphism between the actual scheme function fields and an injective coordinate embedding $$A\hookrightarrow K(X).$$ The specified algebra structure makes $K(X)$ a fraction ring of $A$. These are the actual maps constructed from the generic-point stalk isomorphism. They supply the ordinary and reciprocal coordinate embeddings used for the order-thirteen Pell and diamond constructions.
-- source:
--   Original complete AffineOpenChartFunctionField.lean from MazurTheorem, Apache-2.0, Vas and contributors. The original source and all five declaration bodies are reused byte-for-byte, with their existing native, strict and complete frontend checks retained and no proof rebuild. All five complete original closed types and the three data values (function-field isomorphism, coordinate embedding and algebra structure) are kernel-compared. Named downstream consumer: actual ordinary function-field coordinates and the rational diamond field automorphism.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an integral affine open chart supplies its actual coordinate
algebra as a fraction-ring base for the scheme's existing function field.
Named downstream consumer: the two order-13 chart embeddings and the Pell
principal divisor. This constructs the maps from the open immersion's stalk
isomorphism at the generic point, without a supplied field equivalence.
-/
import Mathlib

noncomputable section
universe u
namespace MazurTransfer.AffineOpenChartFunctionField
open AlgebraicGeometry CategoryTheory
variable (A : CommRingCat.{u}) [IsDomain A] {X : Scheme.{u}} [IsIntegral X]
    (j : Spec A ⟶ X) [IsOpenImmersion j]

def functionFieldIso : X.functionField ≅ (Spec A).functionField :=
  eqToIso (congrArg X.presheaf.stalk (genericPoint_eq_of_isOpenImmersion j).symm) ≪≫
    asIso (j.stalkMap (genericPoint (Spec A)))

def coordinateEmbedding : A →+* X.functionField :=
  (functionFieldIso A j).inv.hom.comp (algebraMap A (Spec A).functionField)

def coordinateAlgebra : Algebra A X.functionField := (coordinateEmbedding A j).toAlgebra

theorem coordinateEmbedding_injective : Function.Injective (coordinateEmbedding A j) :=
  (ConcreteCategory.bijective_of_isIso (functionFieldIso A j).inv).1.comp
    (IsFractionRing.injective A (Spec A).functionField)

theorem coordinate_isFractionRing :
    letI := coordinateAlgebra A j
    IsFractionRing A X.functionField := by
  letI := coordinateAlgebra A j
  apply IsFractionRing.of_algEquiv (R := A) (K := (Spec A).functionField)
  refine AlgEquiv.ofRingEquiv (f := (functionFieldIso A j).symm.commRingCatIsoToRingEquiv) ?_
  intro a
  rfl

end MazurTransfer.AffineOpenChartFunctionField
#print axioms MazurTransfer.AffineOpenChartFunctionField.coordinateEmbedding_injective
#print axioms MazurTransfer.AffineOpenChartFunctionField.coordinate_isFractionRing


