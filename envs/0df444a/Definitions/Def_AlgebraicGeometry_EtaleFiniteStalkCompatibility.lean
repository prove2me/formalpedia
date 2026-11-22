-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFiniteStalkCompatibility
-- name    : AlgebraicGeometry_EtaleFiniteStalkCompatibility
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T01:22:19.803067+00:00
-- url     : https://prove2.me/theorems/a936bb65-a981-4286-838b-91e4896bd772
-- title:
--   Matching geometric lifts in finite descent
-- statement:
--   Agreement on a double overlap forces the same evaluation at any two lifts of the geometric point.

import Definitions.Def_AlgebraicGeometry_EtaleDirectImageSectionGerms

noncomputable section

section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDescentCofaces
open PhilipponEtalePullbackComposition (restrictDirectImage)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStrictHenselization (toBase)


namespace PhilipponFiniteStalkDescent

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {X Y Z : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K]
  (p : Y ⟶ X) (s : Spec (.of K) ⟶ X)

private abbrev stalk := (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})

theorem evaluations_eq_of_agreement
    (d₁ d₂ : Z ⟶ Y) (ρ : Z ⟶ X) (hsq : IsPullback d₁ d₂ p p)
    (h₁ : d₁ ≫ p = ρ) (h₂ : d₂ ≫ p = ρ)
    (r₁ r₂ : Spec (.of K) ⟶ Y) (hr₁ : r₁ ≫ p = s) (hr₂ : r₂ ≫ p = s)
    (F : Ab X) (b : (stalk s).obj ((pushforward p).obj ((pullbackSheaves p).obj F)))
    (hb : (stalk s).map (restrictDirectImage p d₁ ρ h₁ F) b =
      (stalk s).map (restrictDirectImage p d₂ ρ h₂ F) b) :
    transportedLiftEvaluation p r₁ s hr₁ F b = transportedLiftEvaluation p r₂ s hr₂ F b := by
  obtain ⟨v, hv₁, hv₂⟩ := hsq.exists_lift r₁ r₂ (hr₁.trans hr₂.symm)
  have hv : v ≫ ρ = s := by rw [← h₁, ← Category.assoc, hv₁, hr₁]
  have hLeft := ConcreteCategory.congr_hom
    (restrict_evaluation_of_eq p d₁ ρ h₁ v r₁ s hv₁ hr₁ hv F) b
  have hRight := ConcreteCategory.congr_hom
    (restrict_evaluation_of_eq p d₂ ρ h₂ v r₂ s hv₂ hr₂ hv F) b
  exact hLeft.symm.trans ((congrArg (transportedLiftEvaluation ρ v s hv F) hb).trans hRight)

end PhilipponFiniteStalkDescent

end

end


