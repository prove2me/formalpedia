-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_etale_cohomology_restrict_eq_zero_at_affine_stage
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-25T08:22:21.650291+00:00
-- url     : https://prove2.me/submissions/af74df72-13af-432d-8d88-ca8553476b58

import Definitions.Def_AlgebraicGeometry_EtaleAffineLimitFixedCohomology
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_refinement_kills_etale_system_class

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleLimitBaseMaps (OverBase coneSystem)
open PhilipponEtaleLimitFixedCoefficient (limitIso)
open PhilipponEtaleFixedCohomologyComparison (transition_restrict stageRestriction_restrict)
open PhilipponEtaleStageCohomology (transition)
open PhilipponEtaleLimitCohomologyTransport (stageRestriction)
open PhilipponEtalePrimeTorsionComparison (restrict)

namespace PhilipponEtaleFiniteStageVanishing

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {I : Type u} [Category.{u} I] [IsCofiltered I]

/-- Vanishing of a class after restriction to an affine inverse limit
is witnessed by restriction to one of its stages. -/
theorem exists_affine_stage (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)]
    (c : Cone D) (hc : IsLimit c) {X : Scheme.{u}}
    (g : D ⟶ (Functor.const I).obj X) (f : c.pt ⟶ X)
    (hf : ∀ i, c.π.app i ≫ g.app i = f) (F : Ab X) (q : ℕ) (x : F.H q)
    (hx : restrict f F q x = 0) :
    ∃ j, restrict (g.app j) F q x = 0 := by
  let B : OverBase c X := ⟨g.app, f, fun a => (g.naturality a).trans (Category.comp_id _), hf⟩
  let S := PhilipponEtaleConeSystem.restrict c (coneSystem B F)
  let i := (IsCofiltered.nonempty (C := I)).some
  let y : (S.obj i).H q := restrict (g.app i) F q x
  let e := ((Sheaf.functorH c.pt.smallEtaleTopology q).mapIso
    (limitIso hc B F)).addCommGroupIsoToAddEquiv
  have hy : stageRestriction c hc S i q y = 0 := by
    apply e.injective
    exact (stageRestriction_restrict B F hc i q x).trans (hx.trans e.map_zero.symm)
  obtain ⟨j, a, ha⟩ := AlgebraicGeometry.Scheme.exists_refinement_kills_etale_system_class c hc q S i y hy
  exact ⟨j, (transition_restrict B F a q x).symm.trans ha⟩

end PhilipponEtaleFiniteStageVanishing

end

section

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] (c : Cone D) (hc : IsLimit c)
    {X : Scheme.{u}} (g : D ⟶ (Functor.const I).obj X) (f : c.pt ⟶ X)
    (hf : ∀ i, c.π.app i ≫ g.app i = f)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) (x : F.H q) :
    PhilipponEtalePrimeTorsionComparison.restrict f F q x = 0 →
      ∃ i, PhilipponEtalePrimeTorsionComparison.restrict (g.app i) F q x = 0 := by
  intro hx
  exact PhilipponEtaleFiniteStageVanishing.exists_affine_stage D c hc g f hf F q x hx

end

end
