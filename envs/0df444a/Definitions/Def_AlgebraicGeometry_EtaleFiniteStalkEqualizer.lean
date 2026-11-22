-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFiniteStalkEqualizer
-- name    : AlgebraicGeometry_EtaleFiniteStalkEqualizer
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T01:27:02.652626+00:00
-- url     : https://prove2.me/theorems/fbd39cf1-d524-456e-8b4e-8021ae924431
-- title:
--   The finite-cover equalizer on geometric stalks
-- statement:
--   Descent of matching finite direct-image stalk sections.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteStalkCompatibility
import Definitions.Def_AlgebraicGeometry_EtaleFiniteStalkEvaluation

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

variable [IsFinite p] [Surjective p] {I : Type u} (B : I → Type u) [∀ i, CommRing (B i)]
    [∀ i, HenselianLocalRing (B i)] [∀ i, IsSepClosed (IsLocalRing.ResidueField (B i))]

private abbrev spectrum (i : I) := Spec (.of (B i))

set_option maxRecDepth 4096 in
/-- The unit of finite surjective descent is injective on a geometric stalk
and its image is precisely the germs agreeing under the overlap maps. -/
theorem unit_exact_on_stalk (d₁ d₂ : Z ⟶ Y) (ρ : Z ⟶ X)
    (hsq : IsPullback d₁ d₂ p p) (h₁ : d₁ ≫ p = ρ) (h₂ : d₂ ≫ p = ρ)
    (c : (∐ spectrum B) ≅ pullback (toBase s) p)
    (hClosed : ∀ i, IsClosedImmersion (Sigma.ι (spectrum B) i ≫ c.hom)) (F : Ab X) :
    let η := (stalk s).map ((pullbackAdjunction p).unit.app F)
    let f := (stalk s).map (restrictDirectImage p d₁ ρ h₁ F)
    let g := (stalk s).map (restrictDirectImage p d₂ ρ h₂ F)
    Function.Injective η ∧ ∀ b, f b = g b → ∃ a, η a = b := by
  let η := (stalk s).map ((pullbackAdjunction p).unit.app F)
  obtain ⟨r₀, hr₀⟩ := PhilipponFiniteStalkEvaluation.exists_lift s p B c hClosed
  have hRet (r : Spec (.of K) ⟶ Y) (hr : r ≫ p = s) (a : (stalk s).obj F) :
      transportedLiftEvaluation p r s hr F (η a) = a :=
    ConcreteCategory.congr_hom (unit_evaluation p r s hr F) a
  refine ⟨(show Function.LeftInverse (transportedLiftEvaluation p r₀ s hr₀ F) η from
    hRet r₀ hr₀).injective, ?_⟩
  intro b hb
  let a := transportedLiftEvaluation p r₀ s hr₀ F b
  refine ⟨a, PhilipponFiniteStalkEvaluation.ext_of_evaluations_equal s p B c hClosed
    ((pullbackSheaves p).obj F) ?_⟩
  intro r hr
  apply evalAtLiftOver_eq_of_transported_eq p r s hr F
  exact (hRet r hr a).trans (evaluations_eq_of_agreement p s d₁ d₂ ρ hsq h₁ h₂ r₀ r hr₀ hr F b hb)

end PhilipponFiniteStalkDescent

end

end


