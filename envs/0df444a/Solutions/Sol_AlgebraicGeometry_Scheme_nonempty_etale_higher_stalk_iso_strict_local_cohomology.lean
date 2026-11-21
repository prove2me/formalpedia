-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_etale_higher_stalk_iso_strict_local_cohomology
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-21T04:23:39.557344+00:00
-- url     : https://prove2.me/submissions/a912b59e-0e82-4192-ba70-cbcc439de544

import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_cohomology_iso_strict_local_resolution
import Theorems.Thm_AlgebraicGeometry_Scheme_nonempty_etale_stalk_sections_iso_over_strict_henselization

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etaleHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

universe u

open CategoryTheory.Abelian

local instance (W : Scheme.{u}) : (PhilipponEtaleAcyclicCohomology.globalSections W).Additive where
  map_add := rfl

local instance {U V : Scheme.{u}} (g : U ⟶ V) : (PhilipponEtaleSmallSite.pullbackSheaves g).Additive :=
  (PhilipponEtaleSmallSite.pullbackAdjunction g).left_adjoint_additive

local instance {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X) :
    ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u})).Additive :=
  Functor.additive_of_preserves_binary_products _

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem solution {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) :
    Nonempty ((Scheme.pointSmallEtale s).sheafFiber.obj
      (((PhilipponEtaleClosedPushforward.pushforward f).rightDerived (q + 1)).obj F) ≅
      AddCommGrpCat.of (((PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd (PhilipponEtaleStrictHenselization.toBase s) f)).obj F).H (q + 1))) := by
  let I := injectiveResolution F
  let Φ := Scheme.pointSmallEtale s
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℕ) (q + 1)
  let e := Classical.choice (AlgebraicGeometry.Scheme.nonempty_etale_stalk_sections_iso_over_strict_henselization f s)
  let c := Classical.choice (AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_strict_local_resolution f s F I q)
  exact ⟨PhilipponEtaleBaseChangeMap.stalkOfHigherImageIso f Φ F (q + 1) ≪≫
    I.isoRightDerivedObj (PhilipponEtaleClosedPushforward.pushforward f ⋙ Φ.sheafFiber) (q + 1) ≪≫
    H.mapIso ((NatIso.mapHomologicalComplex e (ComplexShape.up ℕ)).app I.cocomplex) ≪≫ c.symm⟩


end
