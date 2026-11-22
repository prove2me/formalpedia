-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleRestrictionEvaluation
-- name    : AlgebraicGeometry_EtaleRestrictionEvaluation
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T04:53:39.838889+00:00
-- url     : https://prove2.me/theorems/6d58a32e-4b1d-4f0c-a7b0-da94fdbb9975
-- title:
--   Evaluation after successive direct-image restrictions
-- statement:
--   Both ways to restrict to the final scheme give the same evaluation at any geometric lift.

import Definitions.Def_AlgebraicGeometry_EtaleDirectImageSectionGerms

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open PhilipponEtaleDescentCofaces
  (transportedLiftEvaluation restrict_evaluation restrict_evaluation_of_eq)
open PhilipponEtalePullbackComposition (restrictDirectImage)


namespace PhilipponEtaleRestrictionEvaluation

universe u

/-- Evaluation at a geometric lift identifies both ways to restrict to the final scheme. -/
theorem evaluation_comp {X Y Z W : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (.of K) ⟶ X) (p : Y ⟶ X) (d : Z ⟶ Y)
    (ρ : Z ⟶ X) (hd : d ≫ p = ρ) (e : W ⟶ Z) (τ : W ⟶ X)
    (he : e ≫ ρ = τ) (hp : (e ≫ d) ≫ p = τ) (v : Spec (.of K) ⟶ W) (hv : v ≫ τ = s)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    let S := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})
    let ev := transportedLiftEvaluation τ v s hv F
    S.map (restrictDirectImage p d ρ hd F ≫ restrictDirectImage ρ e τ he F) ≫ ev =
      S.map (restrictDirectImage p (e ≫ d) τ hp F) ≫ ev := by
  let S := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})
  let D := restrictDirectImage p d ρ hd F
  let E := restrictDirectImage ρ e τ he F
  let C := restrictDirectImage p (e ≫ d) τ hp F
  let ev := transportedLiftEvaluation τ v s hv F
  change S.map (D ≫ E) ≫ ev = S.map C ≫ ev
  have hZ : (v ≫ e) ≫ ρ = s := by rw [Category.assoc, he, hv]
  have hY : ((v ≫ e) ≫ d) ≫ p = s := by rw [Category.assoc, hd, hZ]
  have hE := restrict_evaluation ρ e τ he v s hZ hv F
  have hD := restrict_evaluation p d ρ hd (v ≫ e) s hY hZ F
  have hC : S.map C ≫ ev = transportedLiftEvaluation p ((v ≫ e) ≫ d) s hY F :=
    restrict_evaluation_of_eq p (e ≫ d) τ hp v ((v ≫ e) ≫ d) s
      (Category.assoc _ _ _).symm hY hv F
  rw [S.map_comp, Category.assoc]
  exact (congrArg (S.map D ≫ ·) hE).trans (hD.trans hC.symm)

end PhilipponEtaleRestrictionEvaluation

end

end


