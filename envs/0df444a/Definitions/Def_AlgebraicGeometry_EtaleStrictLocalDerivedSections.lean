-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleStrictLocalDerivedSections
-- name    : AlgebraicGeometry_EtaleStrictLocalDerivedSections
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-21T03:44:11.089969+00:00
-- url     : https://prove2.me/theorems/df3c3f3f-dd78-4e3b-b5e4-eafb27723af2
-- title:
--   Higher étale direct-image stalks via strict-local cohomology
-- statement:
--   Computation of the higher direct-image stalk of a proper morphism from the cohomology of the inverse image over the strict henselization.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalAcyclicity

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleBaseChangeMap (stalkOfHigherImageIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtalePullbackResolution (cohomologyEquivPullbackResolution)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStrictHenselization (toBase)
open PhilipponStrictLocalPresheaf (stalkDirectImageNatIsoStrictLocalSections strictLocalPullback_acyclic_of_injective)


namespace PhilipponStrictLocalDerivedSections

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
  (s : Spec (CommRingCat.of K) ⟶ X) (f : Y ⟶ X) [IsProper f]

private abbrev Local : Scheme.{u} := pullback (toBase s) f
private abbrev π : Local s f ⟶ Y := pullback.snd (toBase s) f
private abbrev Φ := Scheme.pointSmallEtale s

local instance : ((Φ s).sheafFiber (A := AddCommGrpCat.{u})).Additive :=
  Functor.additive_of_preserves_binary_products _

local instance (Z : Scheme.{u}) : (globalSections Z).Additive where
  map_add := rfl

local instance {U V : Scheme.{u}} (g : U ⟶ V) : (pullbackSheaves g).Additive :=
  (pullbackAdjunction g).left_adjoint_additive

/-- The higher stalk is computed by applying strict-local sections to
the inverse image of an injective resolution on the original scheme. -/
def higherStalkIsoHomology (F : Ab Y) (I : InjectiveResolution F) (n : ℕ) :
    (Φ s).sheafFiber.obj (((pushforward f).rightDerived n).obj F) ≅
      (((pullbackSheaves (π s f) ⋙ globalSections (Local s f)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).homology n :=
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) n
  let e := NatIso.mapHomologicalComplex (stalkDirectImageNatIsoStrictLocalSections s f)
    (ComplexShape.up ℕ)
  stalkOfHigherImageIso f (Φ s) F n ≪≫ I.isoRightDerivedObj (pushforward f ⋙ (Φ s).sheafFiber) n ≪≫
    H.mapIso (e.app I.cocomplex)

/-- For an injective resolution whose terms pull back to acyclic sheaves,
the higher direct-image stalk equals the cohomology of the inverse image. -/
def higherStalkIsoLocalCohomologyOfAcyclic (F : Ab Y) (I : InjectiveResolution F)
    (h : ∀ j k : ℕ, Subsingleton (((pullbackSheaves (π s f)).obj (I.cocomplex.X j)).H (k + 1)))
    (n : ℕ) : (Φ s).sheafFiber.obj (((pushforward f).rightDerived (n + 1)).obj F) ≅
      AddCommGrpCat.of (((pullbackSheaves (π s f)).obj F).H (n + 1)) :=
  higherStalkIsoHomology s f F I (n + 1) ≪≫
    (cohomologyEquivPullbackResolution (π s f) F I h n).symm.toAddCommGrpIso

/-- The higher direct-image stalk of a proper morphism is the étale
cohomology of the inverse image over the strict henselization. -/
def higherStalkIsoLocalCohomology (F : Ab Y) (n : ℕ) :
    (Φ s).sheafFiber.obj (((pushforward f).rightDerived (n + 1)).obj F) ≅
      AddCommGrpCat.of (((pullbackSheaves (π s f)).obj F).H (n + 1)) := by
  let I := injectiveResolution F
  apply higherStalkIsoLocalCohomologyOfAcyclic s f F I _ n
  intro j q
  let : Injective (I.cocomplex.X j) := I.injective j
  exact strictLocalPullback_acyclic_of_injective s f (I.cocomplex.X j) q

end PhilipponStrictLocalDerivedSections

end

end


