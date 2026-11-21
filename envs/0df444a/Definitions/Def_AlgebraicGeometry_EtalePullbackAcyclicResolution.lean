-- Prove2me | Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
-- name    : AlgebraicGeometry_EtalePullbackAcyclicResolution
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-21T03:38:31.345767+00:00
-- url     : https://prove2.me/theorems/64c5a966-40d0-4d6e-a1b3-3721a2065965
-- title:
--   Acyclic pullback resolutions on small étale sites
-- statement:
--   Comparison of étale cohomology with the global sections complex of a pulled-back resolution whose terms are acyclic.

import Definitions.Def_AlgebraicGeometry_EtaleDerivedGlobalSections

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
open PhilipponEtaleBaseChangeMap (stalkToFiberSections stalkOfHigherImageIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)


namespace PhilipponEtalePullbackResolution

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

local instance (X : Scheme.{u}) : (globalSections X).Additive where
  map_add := rfl

local instance {X Y : Scheme.{u}} (f : Y ⟶ X) : (pullbackSheaves f).Additive :=
  (pullbackAdjunction f).left_adjoint_additive

private theorem extLarge (X : Scheme.{u}) : HasExt.{u + 1} (Ab X) := by
  have h (P Q : Ab X) (n : ℕ) : Small.{u + 1} (Ext.{u} P Q n) :=
    small_succ (Ext.{u} P Q n)
  exact (hasExt_iff_small_ext.{u + 1, u} (Ab X)).mpr h

private def extLift {X : Scheme.{u}} [HasExt.{u + 1} (Ab X)] (P Q : Ab X) (n : ℕ) :
    Ext.{u} P Q n ≃+ Ext.{u + 1} P Q n :=
  letI := HasDerivedCategory.standard (Ab X)
  Ext.homAddEquiv.trans Ext.homAddEquiv.symm

/-- A pulled-back injective resolution computes the positive cohomology of
the inverse image when all its terms have zero higher cohomology. -/
def cohomologyEquivPullbackResolution {X Y : Scheme.{u}} (f : Y ⟶ X) (F : Ab X)
    (I : InjectiveResolution F)
    (h : ∀ j k : ℕ, Subsingleton (((pullbackSheaves f).obj (I.cocomplex.X j)).H (k + 1)))
    (n : ℕ) : ((pullbackSheaves f).obj F).H (n + 1) ≃+
      (((pullbackSheaves f ⋙ globalSections Y).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex).homology (n + 1) := by
  let L := pullbackSheaves f
  let K := (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  haveI : L.IsLeftAdjoint := (pullbackAdjunction f).isLeftAdjoint
  have hExact (j : ℕ) : K.ExactAt (j + 1) :=
    (show (I.cocomplex.sc (j + 1)).Exact from I.cocomplex_exactAt_succ j).map L
  letI : HasExt.{u + 1} (Ab Y) := extLarge Y
  let P := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  have hExt (j k : ℕ) : Subsingleton (Ext.{u + 1} P (K.X j) (k + 1)) := by
    have : Subsingleton (Ext.{u} P (K.X j) (k + 1)) := h j k
    exact (extLift P (K.X j) (k + 1)).symm.injective.subsingleton
  let e := PhilipponAcyclicResolution.extEquivAcyclicComplex P (L.obj F) K
    (asIso (I.toRightDerivedZero' L)) hExact hExt n
  exact (extLift P (L.obj F) (n + 1)).trans
    (e.trans (PhilipponEtaleDerivedSections.homologyEquivGlobalSections K (n + 1)))

private def deriveIso {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasInjectiveResolutions C] {G H : C ⥤ D} [G.Additive] [H.Additive] (e : G ≅ H) (n : ℕ) :
    G.rightDerived n ≅ H.rightDerived n where
  hom := NatTrans.rightDerived e.hom n
  inv := NatTrans.rightDerived e.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, e.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, e.inv_hom_id, NatTrans.rightDerived_id]

/-- The ordinary geometric comparison and a fiber-acyclic pullback
resolution suffice for geometric base change in positive degrees. -/
def geometricBaseChangeOfAcyclicResolution {X Y : Scheme.{u}} (f : Y ⟶ X)
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (CommRingCat.of K) ⟶ X)
    (F : Ab Y) (I : InjectiveResolution F) (h₀ : IsIso (stalkToFiberSections f s))
    (h : ∀ j k : ℕ, Subsingleton (((pullbackSheaves (pullback.snd s f)).obj (I.cocomplex.X j)).H (k + 1)))
    (n : ℕ) :
    (Scheme.pointSmallEtale s).sheafFiber.obj (((pushforward f).rightDerived (n + 1)).obj F) ≅
      AddCommGrpCat.of (((pullbackSheaves (pullback.snd s f)).obj F).H (n + 1)) := by
  let L := pullbackSheaves (pullback.snd s f)
  let Γ := globalSections (pullback s f)
  exact stalkOfHigherImageIso f (Scheme.pointSmallEtale s) F (n + 1) ≪≫
    (deriveIso (asIso (stalkToFiberSections f s)) (n + 1)).app F ≪≫
    I.isoRightDerivedObj (L ⋙ Γ) (n + 1) ≪≫
    (cohomologyEquivPullbackResolution (pullback.snd s f) F I h n).symm.toAddCommGrpIso

end PhilipponEtalePullbackResolution

end

end


