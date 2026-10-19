-- Prove2me | Definitions.Def_MazurTransfer_PicardCurvePullbackGeometricFieldLineBundleData
-- name    : MazurTransfer_PicardCurvePullbackGeometricFieldLineBundleData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:37:46.898695+00:00
-- url     : https://prove2.me/theorems/a11e778c-8bba-451e-beb0-7a0f714d63c6
-- title:
--   Geometric field-point line bundles respect curve pullback through a commuting fibre map
-- statement:
--   A field-valued point of a represented relative Picard scheme gives the original line bundle on any chosen model of the curve fibre, and re-rigidified curve pullback acts on that bundle through a commuting fibre morphism. The original geometric bundle constructor, full pullback contract and original field-rigidification helper are retained: three full original types and one constructor value are compared. Named downstream consumer: the actual rational Picard diamond on geometric field points.
-- source:
--   Complete original MazurTheorem field divisor/relative Picard line-bundle transport contracts, constructors and proofs, including the full original invertible-sheaf field-rigidification helper where used. Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a field-valued point of a represented Picard scheme gives
a line bundle on a chosen model of its curve fibre. Curve pullback acts on
this bundle through a commuting fibre map. Named downstream consumer: the
existing rational order-13 Picard diamond on geometric field points.
-/
import Definitions.Def_MazurTransfer_PicardReRigidifiedCurvePullbackData
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field

noncomputable section
namespace MazurTransfer.GeometricCurvePullbackFieldHelpers20261017
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
theorem rigidify_iso_of_field.{u} (K : Type u) [Field K] {P : Scheme.{u}}
    (σ : Spec (CommRingCat.of K) ⟶ P) (q : P ⟶ Spec (CommRingCat.of K))
    (L : P.Modules) (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify σ q L ≅ L) := by
  have hQ : Scheme.Modules.IsInvertible (Scheme.Modules.dual ((Scheme.Modules.pullback σ).obj L)) :=
    (hL.pullback σ).dual.1
  obtain ⟨e⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field K _ hQ
  exact ⟨(Iso.refl L ⊗ᵢ (Scheme.Modules.pullback q).mapIso e) ≪≫
    (Iso.refl L ⊗ᵢ Scheme.Modules.pullbackTensorUnitObjIso q) ≪≫ ρ_ L⟩

end MazurTransfer.GeometricCurvePullbackFieldHelpers20261017
end
noncomputable section
universe u
namespace MazurTransfer.PicardCurvePullbackGeometricFieldLineBundle
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian PicardReRigidifiedCurvePullback
variable {R : Type u} [CommRing R] {K : Type u} [Field K]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    {X : Scheme.{u}} (j : X ⟶ pullback c t)

def geometricPointLineBundle (a : SchemeHomOver t D.toBase) : X.Modules :=
  (Scheme.Modules.pullback j).obj (h.poincare.pullbackAlong a).L

theorem geometricPointLineBundle_postComp_iso_pullback
    (f : C ⟶ C) (hf : f ≫ c = c) (N : PullbackData h f hf)
    (g : X ⟶ X) (hcomp : j ≫ curveChange f hf t = g ≫ j)
    (a : SchemeHomOver t D.toBase) :
    Nonempty (geometricPointLineBundle c ε D h t j (postComp N.hom a) ≅
      (Scheme.Modules.pullback g).obj (geometricPointLineBundle c ε D h t j a)) := by
  let L := (Scheme.Modules.pullback (curveChange f hf t)).obj (h.poincare.pullbackAlong a).L
  have hL : Scheme.Modules.IsInvertible L := (h.poincare.pullbackAlong a).isInvertible.pullback _
  obtain ⟨e₁⟩ := N.classifies t a
  obtain ⟨e₂⟩ := GeometricCurvePullbackFieldHelpers20261017.rigidify_iso_of_field K
    (rigSection c t ε) (pullback.snd c t) L hL
  exact ⟨(Scheme.Modules.pullback j).mapIso (e₁ ≪≫ e₂) ≪≫
    (Scheme.Modules.pullbackComp j (curveChange f hf t)).app (h.poincare.pullbackAlong a).L ≪≫
    (Scheme.Modules.pullbackCongr hcomp).app (h.poincare.pullbackAlong a).L ≪≫
    ((Scheme.Modules.pullbackComp g j).app (h.poincare.pullbackAlong a).L).symm⟩

end MazurTransfer.PicardCurvePullbackGeometricFieldLineBundle
#print axioms MazurTransfer.PicardCurvePullbackGeometricFieldLineBundle.geometricPointLineBundle_postComp_iso_pullback


