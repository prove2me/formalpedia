-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestrictionComposition
-- name    : AlgebraicGeometry_EtaleCohomologyRestrictionComposition
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T06:15:19.671009+00:00
-- url     : https://prove2.me/theorems/d03dfc3d-5895-48c8-bfab-0aa629e27264
-- title:
--   Composition and global sections for restriction in étale cohomology
-- statement:
--   Étale cohomological restriction commutes with composition under the inverse-image comparison. In degree zero it agrees with restriction of global sections.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyConnectingMaps

noncomputable section

section

attribute [local instance] etaleHasSheafify etaleHasExt etaleEnoughInjectives

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso pullbackConstantIso)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtalePullbackComposition
  (pullbackCompIso restrictGlobalSections_app_eq restrictGlobalSections_comp)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtalePrimeTorsionComparison (restrict)


namespace PhilipponEtaleCohomologyRestrictionComp

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev Z₀ := AddCommGrpCat.of (ULift.{u} ℤ)
private abbrev C (X : Scheme.{u}) :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj Z₀

private def constAdj (X : Scheme.{u}) :
    constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⊣ globalSections X :=
  constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u}
    (IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) (Scheme.Etale.mk (𝟙 X)) Over.mkIdTerminal)

private abbrev constMap {X Y : Scheme.{u}} (f : Y ⟶ X) :
    C Y ⟶ (pullbackSheaves f).obj (C X) :=
  (pullbackConstantIso f).inv.app Z₀

private theorem homEquiv_constMap {X Y : Scheme.{u}} (f : Y ⟶ X) (F : Ab X) (a : C X ⟶ F) :
    (constAdj Y).homEquiv Z₀ _ (constMap f ≫ (pullbackSheaves f).map a) =
      (constAdj X).homEquiv Z₀ F a ≫ (restrictGlobalSections f).app F := by
  let L := pullbackSheaves f
  let adj := pullbackAdjunction f
  let d := ((constAdj X).comp adj).ofNatIsoRight (globalSectionsIso f)
  have hl : adj.homEquiv _ _ (L.map a) = a ≫ adj.unit.app F := by
    rw [Adjunction.homEquiv_unit]
    exact (adj.unit.naturality a).symm
  have hc : (constAdj Y).homEquiv Z₀ (L.obj (C X)) (constMap f) = d.unit.app Z₀ :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app (constAdj Y) d Z₀
  calc
    _ = d.homEquiv Z₀ _ (L.map a) := by
      rw [Adjunction.homEquiv_naturality_right, hc, Adjunction.homEquiv_unit]
    _ = _ := by
      dsimp only [d]
      rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
      change (constAdj X).homEquiv Z₀ _ (adj.homEquiv _ _ (L.map a)) ≫
        (globalSectionsIso f).hom.app (L.obj F) = _
      rw [hl, Adjunction.homEquiv_naturality_right, restrictGlobalSections_app_eq, Category.assoc]

private theorem constMap_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y) :
    constMap g ≫ (pullbackSheaves g).map (constMap f) ≫
      (pullbackCompIso f g).hom.app (C X) = constMap (g ≫ f) := by
  let a := (constAdj X).homEquiv Z₀ (C X) (𝟙 (C X))
  let d := (pullbackCompIso f g).hom.app (C X)
  have hc {P Q : Scheme.{u}} (h : Q ⟶ P) :
      (constAdj Q).homEquiv Z₀ _ (constMap h) =
        (constAdj P).homEquiv Z₀ (C P) (𝟙 (C P)) ≫ (restrictGlobalSections h).app (C P) := by
    have hh := homEquiv_constMap h (C P) (𝟙 (C P))
    rw [(pullbackSheaves h).map_id (C P), Category.comp_id] at hh
    exact hh
  apply ((constAdj Z).homEquiv Z₀ _).injective
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right, homEquiv_constMap,
    hc f, hc (g ≫ f)]
  change (a ≫ (restrictGlobalSections f).app (C X) ≫
    (restrictGlobalSections g).app ((pullbackSheaves f).obj (C X))) ≫
      (globalSections Z).map d = a ≫ (restrictGlobalSections (g ≫ f)).app (C X)
  simp only [Category.assoc, d, restrictGlobalSections_comp]

set_option maxHeartbeats 900000 in
/-- Restriction in étale cohomology commutes with composition, after
transporting the inverse-image coefficient sheaf. -/
theorem restrict_comp {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (F : Ab X) (q : ℕ) (x : F.H q) :
    Sheaf.H.map ((pullbackCompIso f g).hom.app F) q
      (restrict g ((pullbackSheaves f).obj F) q (restrict f F q x)) =
      restrict (g ≫ f) F q x := by
  have h := PhilipponExtComparisonComposition.comparison_comp_iso
    (pullbackSheaves f) (pullbackSheaves g) (pullbackSheaves (g ≫ f))
    (pullbackCompIso f g) (constMap f) (constMap g) q F x
  rw [constMap_comp] at h
  exact h

/-- Vanishing after a composite restriction is equivalent to vanishing
after successive restrictions. -/
theorem restrict_comp_eq_zero_iff {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (F : Ab X) (q : ℕ) (x : F.H q) :
    restrict (g ≫ f) F q x = 0 ↔
      restrict g ((pullbackSheaves f).obj F) q (restrict f F q x) = 0 := by
  let e := ((Sheaf.functorH Z.smallEtaleTopology q).mapIso
    ((pullbackCompIso f g).app F)).addCommGroupIsoToAddEquiv
  rw [← restrict_comp f g F q x]
  change e _ = 0 ↔ _
  exact ⟨fun h => e.injective (h.trans e.map_zero.symm),
    fun h => (congrArg e h).trans e.map_zero⟩

private def terminalWitness (X : Scheme.{u}) : IsTerminal (Scheme.Etale.mk (𝟙 X)) :=
  IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal

abbrev sectionsEquiv {X : Scheme.{u}} (F : Ab X) :
    F.H 0 ≃+ F.obj.obj (op (Scheme.Etale.mk (𝟙 X))) :=
  Sheaf.H.equiv₀ F (terminalWitness X)

/-- In degree zero, cohomological restriction agrees with restriction of
sections under the usual identification. -/
theorem sectionsEquiv_restrict {X Y : Scheme.{u}} (f : Y ⟶ X) (F : Ab X) (x : F.H 0) :
    sectionsEquiv ((pullbackSheaves f).obj F) (restrict f F 0 x) =
      (restrictGlobalSections f).app F (sectionsEquiv F x) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective (C X) F).surjective x
  have h := PhilipponExtComparison.comparison_mk₀ (pullbackSheaves f) (constMap f) a
  change restrict f F 0 (Ext.mk₀ a) = _ at h
  rw [h]
  unfold sectionsEquiv Sheaf.H.equiv₀
  simp only [AddEquiv.trans_apply, ← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]
  exact congrArg (fun m : Z₀ ⟶ (globalSections Y).obj ((pullbackSheaves f).obj F) =>
    m (ULift.up (1 : ℤ))) (homEquiv_constMap f F a)

end PhilipponEtaleCohomologyRestrictionComp

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtalePrimeTorsionComparison (restrict)
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleBaseChangeMap (pushforwardCompIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtalePullbackComposition (pullbackCompIso pullbackCompIso_over_hom)
open PhilipponEtaleCohomologyRestrictionComp (restrict_comp)


namespace PhilipponEtaleCohomologyAlong

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- The pullback composition comparison for a given composite arrow. -/
def pullbackComposition {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (ρ : Z ⟶ X) (h : g ≫ f = ρ) :
    pullbackSheaves f ⋙ pullbackSheaves g ≅ pullbackSheaves ρ :=
  pullbackCompIso f g ≪≫ eqToIso (congrArg pullbackSheaves h)

/-- Restriction in cohomology along a given composite agrees with
successive restrictions and the inverse-image composition comparison. -/
theorem restrict_comp_over {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (ρ : Z ⟶ X) (h : g ≫ f = ρ) (F : Ab X) (q : ℕ) (x : F.H q) :
    Sheaf.H.map ((pullbackComposition f g ρ h).hom.app F) q
      (restrict g ((pullbackSheaves f).obj F) q (restrict f F q x)) = restrict ρ F q x := by
  subst ρ
  simpa only [pullbackComposition, congrArg, eqToIso_refl, Iso.trans_refl] using restrict_comp f g F q x

end PhilipponEtaleCohomologyAlong

end

end


