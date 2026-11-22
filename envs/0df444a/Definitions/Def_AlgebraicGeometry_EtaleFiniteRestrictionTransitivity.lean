-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFiniteRestrictionTransitivity
-- name    : AlgebraicGeometry_EtaleFiniteRestrictionTransitivity
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T05:33:12.309242+00:00
-- url     : https://prove2.me/theorems/79d1810e-3b3b-43e8-8b58-a20c66a358a6
-- title:
--   Transitivity of restriction to a finite overlap
-- statement:
--   Restriction on direct images is transitive when the final map to the base is finite.

import Definitions.Def_AlgebraicGeometry_EtaleRestrictionEvaluation

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDescentCofaces (transportedLiftEvaluation)
open PhilipponEtaleGeometricStalks
  (algebraicallyClosedGeometricMap algebraicallyClosedGeometricPoints_conservative)
open PhilipponEtalePullbackComposition (restrictDirectImage)
open PhilipponEtaleSmallSite (pullbackSheaves)


namespace PhilipponEtaleRestrictionTransitivity

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private abbrev geometricStalk {X : Scheme.{u}} (x : X) :=
  (Scheme.pointSmallEtale (algebraicallyClosedGeometricMap x)).sheafFiber (A := AddCommGrpCat.{u})

/-- Evaluations at lifts of each geometric point distinguish direct-image germs. -/
def EvaluationsSeparate {X W : Scheme.{u}} (τ : W ⟶ X) (F : Ab X) : Prop :=
  ∀ (x : X) {a b : (geometricStalk x).obj ((pushforward τ).obj ((pullbackSheaves τ).obj F))},
    (∀ (v) (hv : v ≫ τ = algebraicallyClosedGeometricMap x),
      transportedLiftEvaluation τ v _ hv F a = transportedLiftEvaluation τ v _ hv F b) → a = b

set_option maxRecDepth 4096 in
/-- Restriction on direct images is transitive when evaluation at geometric
lifts detects equality of the target germs. -/
theorem restrictDirectImage_comp {X Y Z W : Scheme.{u}} (p : Y ⟶ X) (d : Z ⟶ Y)
    (ρ : Z ⟶ X) (hd : d ≫ p = ρ) (e : W ⟶ Z) (τ : W ⟶ X)
    (he : e ≫ ρ = τ) (hp : (e ≫ d) ≫ p = τ) (F : Ab X) (hSep : EvaluationsSeparate τ F) :
    restrictDirectImage p d ρ hd F ≫ restrictDirectImage ρ e τ he F =
      restrictDirectImage p (e ≫ d) τ hp F := by
  let Φ (x : X) := Scheme.pointSmallEtale (algebraicallyClosedGeometricMap x)
  let P := ObjectProperty.ofObj Φ
  have hP : P.IsConservativeFamilyOfPoints := algebraicallyClosedGeometricPoints_conservative X
  apply (hP.jointlyFaithful AddCommGrpCat.{u}).map_injective
  intro Ψ
  obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff Φ Ψ.obj).mp Ψ.property
  rw [← hx]
  let s := algebraicallyClosedGeometricMap x
  let S := geometricStalk x
  let D := restrictDirectImage p d ρ hd F
  let E := restrictDirectImage ρ e τ he F
  let C := restrictDirectImage p (e ≫ d) τ hp F
  change S.map (D ≫ E) = S.map C
  apply ConcreteCategory.hom_ext
  intro a
  apply hSep x
  intro v hv
  exact ConcreteCategory.congr_hom
    (PhilipponEtaleRestrictionEvaluation.evaluation_comp s p d ρ hd e τ he hp v hv F) a

end PhilipponEtaleRestrictionTransitivity

end

end


