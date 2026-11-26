-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleTwoAffineFilteredCohomology
-- name    : AlgebraicGeometry_EtaleTwoAffineFilteredCohomology
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T08:22:06.915903+00:00
-- url     : https://prove2.me/theorems/4556a506-c648-552e-82ce-29fe6d9a2e95
-- title:
--   Filtered colimits of étale cohomology on two affine opens
-- statement:
--   Affine lifting of sections and acyclicity on the two affine opens imply that abelian étale cohomology preserves filtered colimits.
-- source:
--   Stacks Project, Section 59.83, https://stacks.math.columbia.edu/tag/03SB.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Definitions.Def_AlgebraicGeometry_EtaleOpenCoefficientComparison
import Definitions.Def_AlgebraicGeometry_EtaleOverlapBoundary
import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSectionGerms
import Definitions.Def_AlgebraicGeometry_FilteredColimitExtDetection
import Definitions.Def_AlgebraicGeometry_FreeEtaleChartSheaves
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ColimCoyoneda
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.ObjectProperty.Ind
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.Tactic.FinCases
import Theorems.Thm_AlgebraicGeometry_Scheme_filtered_colimit_of_injectives_etale_H_succ_subsingleton

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etaleTwoAffineFilteredCohomologyHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleTwoAffineFilteredCohomologyHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleTwoAffineFilteredCohomologyEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleExtensionByZero (restrict)
namespace PhilipponEtaleMayerVietoris
universe u
variable {X : Scheme.{u}} (U V : X.Opens)
private abbrev terminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)
theorem subsingleton_H_succ (h : U ⊔ V = ⊤)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ)
    (h₁ : Subsingleton (((restrict (U ⊓ V).ι).obj F).H q))
    (h₂ : Subsingleton (((restrict U.ι).obj F).H (q + 1)))
    (h₃ : Subsingleton (((restrict V.ι).obj F).H (q + 1))) :
    Subsingleton (F.H (q + 1)) := by
  let _ := h₁
  let _ := h₂
  let _ := h₃
  let S := mayerVietoris U V h
  have z₁ : IsZero (F.H' q S.X₁) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr
      ((PhilipponEtaleOpenCohomology.openComparison (U ⊓ V).ι F q).injective.subsingleton)
  have z₂ : IsZero (F.H' (q + 1) S.X₂) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr
      ((PhilipponEtaleOpenCohomology.openComparison U.ι F (q + 1)).injective.subsingleton)
  have z₃ : IsZero (F.H' (q + 1) S.X₃) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr
      ((PhilipponEtaleOpenCohomology.openComparison V.ι F (q + 1)).injective.subsingleton)
  have hTo : S.toBiprod F (q + 1) = 0 := by
    apply biprod.hom_ext
    · exact z₂.eq_of_tgt _ _
    · exact z₃.eq_of_tgt _ _
  have hδ : S.δ F q (q + 1) rfl = 0 := z₁.eq_zero_of_src _
  have exactPair : Function.Exact (S.δ F q (q + 1) rfl) (S.toBiprod F (q + 1)) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp ((S.sequence_exact F q (q + 1) rfl).exact 2)
  have hZero (x : F.H' (q + 1) S.X₄) : x = 0 := by
    obtain ⟨y, hy⟩ := (exactPair x).mp (by rw [hTo]; rfl)
    rw [← hy, hδ]
    rfl
  have hT : IsTerminal (terminal X) := IsTerminal.isTerminalOfObj (Scheme.Etale.forget X)
    _ Over.mkIdTerminal
  exact ⟨fun a b => (PhilipponSheafCohomology.terminalComparison _ hT F (q + 1)).injective
    ((hZero _).trans (hZero _).symm)⟩


end PhilipponEtaleMayerVietoris
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 950000

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleExtensionByZero (restrict)
open PhilipponEtaleMayerVietoris (overlapBoundary overlapBoundary_surjective overlapBoundary_naturality)
open PhilipponEtaleNeighborhoodRestriction (restrictionIso)
open PhilipponEtaleOpenCohomology (openComparison openComparison_map)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleFilteredAcyclicityTwoAffine

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

private theorem preserves_colimits_of_shape {J : Type u} [Category.{u} J]
    {X : Scheme.{u}} (W : X.Opens) : PreservesColimitsOfShape J (restrict W.ι) := by
  let L := pullbackSheaves W.ι
  let : L.IsLeftAdjoint := (pullbackAdjunction W.ι).isLeftAdjoint
  let e : restrict W.ι ≅ L := restrictionIso W.ι
  exact preservesColimitsOfShape_of_natIso e.symm

/-- Filtered colimits of injective étale sheaves are acyclic on a separated
scheme covered by two affine opens. -/
theorem acyclic_of_colimit {J : Type u} [Category.{u} J] [IsFiltered J]
    (X : Scheme.{u}) [X.IsSeparated] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ⊔ V = ⊤)
    (hZero : ∀ (W : Scheme.{u}) [IsAffine W] (D : J ⥤ Ab W) (c : Cocone D),
      IsColimit c → ∀ x : c.pt.H 0,
        ∃ (j : J) (y : (D.obj j).H 0), Sheaf.H.map (c.ι.app j) 0 y = x)
    (F : J ⥤ Ab X) [∀ j, Injective (F.obj j)] (d : Cocone F) (hd : IsColimit d) (n : ℕ) :
    Subsingleton (d.pt.H (n + 1)) := by
  have localVanish (W : X.Opens) (hW : IsAffineOpen W) (m : ℕ) :
      Subsingleton (((restrict W.ι).obj d.pt).H (m + 1)) := by
    let R := restrict W.ι
    let : IsAffine W.toScheme := hW
    let : PreservesColimitsOfShape J R := preserves_colimits_of_shape (J := J) W
    let : ∀ j, Injective ((F ⋙ R).obj j) := fun _ => R.injective_obj_of_injective inferInstance
    exact AlgebraicGeometry.Scheme.filtered_colimit_of_injectives_etale_H_succ_subsingleton W.toScheme (F ⋙ R) (R.mapCocone d)
      (isColimitOfPreserves R hd) m
  cases n with
  | succ n =>
    exact PhilipponEtaleMayerVietoris.subsingleton_H_succ U V h d.pt (n + 1)
      (localVanish (U ⊓ V) (hU.inf hV) n) (localVanish U hU (n + 1)) (localVanish V hV (n + 1))
  | zero =>
    let W := U ⊓ V
    let R := restrict W.ι
    let : IsAffine W.toScheme := hU.inf hV
    let : PreservesColimitsOfShape J R := preserves_colimits_of_shape (J := J) W
    let e (G : Ab X) := openComparison W.ι G 0
    have hzero (x : d.pt.H 1) : x = 0 := by
      obtain ⟨s, hs⟩ := overlapBoundary_surjective U V h d.pt
        (localVanish U hU 0) (localVanish V hV 0) x
      obtain ⟨j, t, ht⟩ := hZero W.toScheme
        (F ⋙ R) (R.mapCocone d) (isColimitOfPreserves R hd) (e d.pt s)
      let w := (e (F.obj j)).symm t
      have hw : w.comp (Ext.mk₀ (d.ι.app j)) rfl = s := by
        apply (e d.pt).injective
        change openComparison W.ι d.pt 0 (w.comp (Ext.mk₀ (d.ι.app j)) rfl) = e d.pt s
        rw [openComparison_map, show openComparison W.ι (F.obj j) 0 w = t from
          (e (F.obj j)).apply_symm_apply t]
        exact ht
      have hstage : overlapBoundary U V h (F.obj j) w = 0 :=
        Ext.eq_zero_of_injective _
      calc
        x = overlapBoundary U V h d.pt (w.comp (Ext.mk₀ (d.ι.app j)) rfl) :=
          (congrArg (overlapBoundary U V h d.pt) hw).trans hs |>.symm
        _ = Sheaf.H.map (d.ι.app j) 1 (overlapBoundary U V h (F.obj j) w) :=
          overlapBoundary_naturality U V h (d.ι.app j) w
        _ = 0 := by rw [hstage, map_zero]
    exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

end PhilipponEtaleFilteredAcyclicityTwoAffine

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleExtensionByZero (restrict)
open PhilipponEtaleNeighborhoodRestriction (restrictionIso)
open PhilipponEtaleOpenCohomology (openComparison openComparison_map)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponFilteredHomDetection
open PhilipponSheafCohomology (freeOn freeTerminalIso)


namespace PhilipponEtaleTwoAffineFilteredSections

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

abbrev AffineLifting : Prop :=
  ∀ {J : Type u} [SmallCategory J] [IsFiltered J] (Y : Scheme.{u}) [IsAffine Y]
    (F : J ⥤ Ab Y) (d : Cocone F), IsColimit d → ∀ x : d.pt.H 0,
      ∃ (j : J) (y : (F.obj j).H 0), Sheaf.H.map (d.ι.app j) 0 y = x

/-- The free abelian sheaf on an affine open is finitely presentable. -/
theorem isFinitelyPresentable_affineOpen (hLift : AffineLifting.{u})
    {X : Scheme.{u}} (W : X.Opens) (hW : IsAffineOpen W) :
    IsFinitelyPresentable.{u} ((freeOn X.smallEtaleTopology).obj (Scheme.Etale.mk W.ι)) := by
  apply isFinitelyPresentable_of_lifting
  intro J _ _ F d hd x
  let R := restrict W.ι
  let L := pullbackSheaves W.ι
  let : IsAffine W.toScheme := hW
  let : L.IsLeftAdjoint := (pullbackAdjunction W.ι).isLeftAdjoint
  let : PreservesColimitsOfShape J R :=
    preservesColimitsOfShape_of_natIso (restrictionIso W.ι).symm
  let e (G : Ab X) := openComparison W.ι G 0
  obtain ⟨j, t, ht⟩ := hLift W.toScheme (F ⋙ R)
    (R.mapCocone d) (isColimitOfPreserves R hd) (e d.pt (Ext.mk₀ x))
  let z : Ext ((freeOn X.smallEtaleTopology).obj (Scheme.Etale.mk W.ι)) (F.obj j) 0 :=
    (e (F.obj j)).symm t
  obtain ⟨y, hy⟩ := (Ext.mk₀_bijective _ _).surjective z
  refine ⟨j, y, (Ext.mk₀_bijective _ _).injective ?_⟩
  rw [← Ext.mk₀_comp_mk₀, hy]
  apply (e d.pt).injective
  rw [openComparison_map, AddEquiv.apply_symm_apply]
  exact ht

/-- On a separated scheme with two affine charts, the constant integer sheaf
is finitely presentable, so global sections commute with filtered colimits. -/
theorem isFinitelyPresentable_constantIntegers (hLift : AffineLifting.{u})
    {X : Scheme.{u}} [X.IsSeparated] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ⊔ V = ⊤) :
    IsFinitelyPresentable.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) := by
  let S := PhilipponEtaleMayerVietoris.mayerVietoris U V h
  let : IsFinitelyPresentable.{u} S.shortComplex.X₁ :=
    isFinitelyPresentable_affineOpen hLift (U ⊓ V) (hU.inf hV)
  let : IsFinitelyPresentable.{u} ((freeOn X.smallEtaleTopology).obj (Scheme.Etale.mk U.ι)) :=
    isFinitelyPresentable_affineOpen hLift U hU
  let : IsFinitelyPresentable.{u} ((freeOn X.smallEtaleTopology).obj (Scheme.Etale.mk V.ι)) :=
    isFinitelyPresentable_affineOpen hLift V hV
  let : IsFinitelyPresentable.{u} S.shortComplex.X₂ := isFinitelyPresentable_biprod
    ((freeOn X.smallEtaleTopology).obj (Scheme.Etale.mk U.ι))
    ((freeOn X.smallEtaleTopology).obj (Scheme.Etale.mk V.ι))
  have h₃ : IsFinitelyPresentable.{u} S.shortComplex.X₃ :=
    isFinitelyPresentable_of_shortExact S.shortComplex S.shortComplex_shortExact
  let : Fact (Cardinal.aleph0.{u}.IsRegular) := Cardinal.fact_isRegular_aleph0
  let : IsCardinalPresentable ((freeOn X.smallEtaleTopology).obj
    (Scheme.Etale.mk (𝟙 X))) Cardinal.aleph0.{u} := h₃
  let hT : IsTerminal (Scheme.Etale.mk (𝟙 X)) :=
    IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal
  exact isCardinalPresentable_of_iso (freeTerminalIso X.smallEtaleTopology hT) _

/-- Étale cohomology on a separated scheme with a two-affine cover commutes
with filtered colimits of coefficient sheaves. -/
def isColimit_cohomology (hLift : AffineLifting.{u}) {J : Type u} [SmallCategory J] [IsFiltered J]
    {X : Scheme.{u}} [X.IsSeparated] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ⊔ V = ⊤)
    (F : J ⥤ Ab X) (n : ℕ) :
    IsColimit ((Sheaf.functorH X.smallEtaleTopology n).mapCocone (colimit.cocone F)) := by
  let P := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  let : IsFinitelyPresentable.{u} P := isFinitelyPresentable_constantIntegers hLift U V hU hV h
  have hA (G : J ⥤ Ab X) (hG : ∀ j, Injective (G.obj j)) (m : ℕ) :
      Subsingleton ((colimit G).H (m + 1)) := by
    let : ∀ j, Injective (G.obj j) := hG
    exact PhilipponEtaleFilteredAcyclicityTwoAffine.acyclic_of_colimit X U V hU hV h
      (fun Y _ G c hc x => hLift Y G c hc x)
      G (colimit.cocone G) (colimit.isColimit G) m
  exact PhilipponFilteredColimitExtLifting.isColimit_ext P hA F n

/-- With a two-affine cover, the cohomology functor preserves all small
filtered colimits. -/
theorem preservesFilteredColimits_functorH (hLift : AffineLifting.{u})
    {X : Scheme.{u}} [X.IsSeparated] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ⊔ V = ⊤) (n : ℕ) :
    PreservesFilteredColimitsOfSize.{u, u} (Sheaf.functorH X.smallEtaleTopology n) where
  preserves_filtered_colimits J _ _ :=
    ⟨fun {F} => preservesColimit_of_preserves_colimit_cocone
      (colimit.isColimit F) (isColimit_cohomology hLift U V hU hV h F n)⟩

end PhilipponEtaleTwoAffineFilteredSections

end


