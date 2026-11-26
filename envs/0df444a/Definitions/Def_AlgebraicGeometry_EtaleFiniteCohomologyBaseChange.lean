-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFiniteCohomologyBaseChange
-- name    : AlgebraicGeometry_EtaleFiniteCohomologyBaseChange
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-26T08:19:45.743781+00:00
-- url     : https://prove2.me/theorems/06f81419-5759-4e6d-87ea-6cf1921d71c6
-- title:
--   Comparison on étale cohomology under finite direct image
-- statement:
--   In a cartesian square along a finite morphism, restriction in étale cohomology is compatible with the cohomology isomorphisms for direct image.
-- source:
--   Stacks Project, Section 59.83, https://stacks.math.columbia.edu/tag/03SB.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Definitions.Def_AlgebraicGeometry_EtaleFilteredCoefficientRestriction
import Definitions.Def_AlgebraicGeometry_EtaleFiniteDirectImageBaseChange
import Definitions.Def_AlgebraicGeometry_EtaleOpenCoefficientComparison
import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSectionGerms
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
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_coproduct_strictlyHenselian_of_finite

noncomputable section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etaleFiniteCohomologyBaseChangeHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleFiniteCohomologyBaseChangeHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleFiniteCohomologyBaseChangeEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 950000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleGeometricStalks (geometricMap)
open PhilipponEtaleLocalRing (stalkRing)
open PhilipponEtaleStrictHenselization (toBase)


namespace PhilipponEtaleFiniteCohomology

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- Direct image along a finite morphism is exact on abelian étale sheaves. -/
theorem preservesFiniteColimits {X Y : Scheme.{u}} (p : Y ⟶ X) [IsFinite p] :
    PreservesFiniteColimits (pushforward p) := by
  apply PhilipponFiniteEtaleStalks.preservesFiniteColimits_of_strictLocalComponents
  intro x
  let s := geometricMap x
  let f := pullback.fst (toBase s) p
  let : IsFinite f := inferInstanceAs (IsFinite (pullback.fst (toBase s) p))
  obtain ⟨I, _, B, hB, hH, hSep, c, _⟩ :=
    Scheme.exists_finite_coproduct_strictlyHenselian_of_finite (stalkRing s) f
  exact ⟨I, B, hB, hH, hSep, ⟨c⟩⟩

end PhilipponEtaleFiniteCohomology

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1250000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleCohomologyRestrictionComp (pullbackConstantIso_inv_comp)
open PhilipponEtaleCohomologyUnits (directImageConstant toDirectImage bijective_toDirectImage)
open PhilipponEtalePrimeTorsionComparison (restrict)
open PhilipponEtalePullbackComposition (pullbackCompIso)
open PhilipponEtalePullbackSquareUnits
  (restrictionBaseChangeOver restrictionBaseChangeOver_naturality pullbackSquareIsoOver
    pullbackSquareIsoOver_comp pulledImageComparison_unit)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponExtComparison (comparison)


namespace PhilipponEtaleFiniteCohomologyBaseChange

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev Z := AddCommGrpCat.of (ULift.{u} ℤ)
private abbrev C (X : Scheme.{u}) := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj Z

variable {X S Y W : Scheme.{u}} (f : S ⟶ X) (p : Y ⟶ X) (j : W ⟶ S) (b : W ⟶ Y)
  (h : IsPullback j b f p)

private abbrev baseChange (F : Ab Y) :=
  restrictionBaseChangeOver f p j b (j ≫ f) rfl h.w.symm F

private abbrev constInv {A B : Scheme.{u}} (g : B ⟶ A) :=
  (pullbackConstantIso g).inv.app Z

private theorem constInv_comp_over {A B D : Scheme.{u}} (g : B ⟶ A) (k : D ⟶ B)
    (ρ : D ⟶ A) (hρ : k ≫ g = ρ) :
    constInv k ≫ (pullbackSheaves k).map (constInv g) ≫
        (pullbackCompIso g k ≪≫ eqToIso (congrArg pullbackSheaves hρ)).hom.app (C A) =
      constInv ρ := by
  subst ρ
  simpa only [eqToIso_refl, Iso.trans_refl] using pullbackConstantIso_inv_comp g k

private theorem constant_square :
    constInv f ≫ (pullbackSheaves f).map (directImageConstant p) ≫
        baseChange f p j b h (C Y) =
      directImageConstant j ≫ (pushforward j).map (constInv b) := by
  let L := pullbackSheaves f
  let V := pullbackSheaves b
  let M := pullbackSheaves j
  let U := pushforward p
  let R := pushforward j
  let α := (pullbackSquareIsoOver f p j b (j ≫ f) rfl h.w.symm).app (C X)
  let d := (pullbackCompIso p b ≪≫ eqToIso (congrArg pullbackSheaves h.w.symm)).app (C X)
  let e := (pullbackConstantIso p).app Z
  let e' := (pullbackConstantIso j).app Z
  let η := (pullbackAdjunction p).unit.app (C X)
  let η' (G : Ab S) := (pullbackAdjunction j).unit.app G
  have hα : α.hom ≫ d.hom = (pullbackCompIso f j).hom.app (C X) := by
    have hh := pullbackSquareIsoOver_comp f p j b (j ≫ f) rfl h.w.symm (C X)
    simp only [eqToIso_refl, Iso.trans_refl] at hh
    exact hh
  have hc : constInv j ≫ M.map (constInv f) ≫ α.hom = constInv b ≫ V.map (constInv p) := by
    apply (cancel_mono d.hom).mp
    simp only [Category.assoc, hα]
    exact (pullbackConstantIso_inv_comp f j).trans
      (constInv_comp_over p b (j ≫ f) h.w.symm).symm
  have hc' : M.map (constInv f) ≫ α.hom ≫ V.map e.hom = e'.hom ≫ constInv b := by
    apply (cancel_epi (constInv j)).mp
    calc
      _ = (constInv j ≫ M.map (constInv f) ≫ α.hom) ≫ V.map e.hom := by
        simp only [Category.assoc]
      _ = (constInv b ≫ V.map e.inv) ≫ V.map e.hom := by rw [hc]; rfl
      _ = constInv b := by
        rw [Category.assoc, ← V.map_comp, e.inv_hom_id]
        exact (congrArg (fun g => constInv b ≫ g) (V.map_id (C Y))).trans (Category.comp_id _)
      _ = _ := (e'.inv_hom_id_assoc _).symm
  have hUnit : L.map η ≫ baseChange f p j b h ((pullbackSheaves p).obj (C X)) =
      η' (L.obj (C X)) ≫ R.map α.hom := by
    apply (cancel_mono (R.map α.inv)).mp
    have hd := pulledImageComparison_unit f p j b (j ≫ f) rfl h.w.symm (C X)
    change L.map η ≫ (baseChange f p j b h ((pullbackSheaves p).obj (C X)) ≫
      R.map α.inv) = η' (L.obj (C X)) at hd
    calc
      _ = η' (L.obj (C X)) := by simpa only [Category.assoc] using hd
      _ = _ := by
        rw [Category.assoc, ← R.map_comp, α.hom_inv_id]
        exact ((congrArg (fun g => η' (L.obj (C X)) ≫ g) (R.map_id (M.obj (L.obj (C X))))).trans
          (Category.comp_id _)).symm
  have hp : directImageConstant p = η ≫ U.map e.hom :=
    Adjunction.homEquiv_unit (pullbackAdjunction p) (C X) (C Y) e.hom
  have hj : directImageConstant j = η' (C S) ≫ R.map e'.hom :=
    Adjunction.homEquiv_unit (pullbackAdjunction j) (C S) (C W) e'.hom
  have hn : L.map (U.map e.hom) ≫ baseChange f p j b h (C Y) =
      baseChange f p j b h ((pullbackSheaves p).obj (C X)) ≫ R.map (V.map e.hom) :=
    restrictionBaseChangeOver_naturality f p j b (j ≫ f) rfl h.w.symm e.hom
  have hη : constInv f ≫ η' (L.obj (C X)) = η' (C S) ≫ R.map (M.map (constInv f)) :=
    (pullbackAdjunction j).unit.naturality (constInv f)
  calc
    _ = constInv f ≫ L.map η ≫ L.map (U.map e.hom) ≫ baseChange f p j b h (C Y) := by
      rw [hp, L.map_comp, Category.assoc]
    _ = constInv f ≫ L.map η ≫ baseChange f p j b h ((pullbackSheaves p).obj (C X)) ≫
        R.map (V.map e.hom) := by
      rw [hn]
    _ = constInv f ≫ η' (L.obj (C X)) ≫ R.map α.hom ≫ R.map (V.map e.hom) := by
      rw [reassoc_of% hUnit]
    _ = η' (C S) ≫ R.map (M.map (constInv f) ≫ α.hom ≫ V.map e.hom) := by
      rw [R.map_comp, R.map_comp, reassoc_of% hη]
    _ = _ := by rw [hc', R.map_comp, hj, Category.assoc]

section ExactDirectImage

variable [PreservesFiniteColimits (pushforward p)] [PreservesFiniteColimits (pushforward j)]

/-- The canonical ordinary base-change morphism intertwines the étale
cohomology restrictions under the exact direct-image identifications. -/
theorem cohomology_square
    (hIso : ∀ F : Ab Y, IsIso (baseChange f p j b h F))
    (F : Ab Y) (q : ℕ) (x : F.H q) :
    Sheaf.H.map (baseChange f p j b h F) q
      (restrict f ((pushforward p).obj F) q (toDirectImage p F q x)) =
    toDirectImage j ((pullbackSheaves b).obj F) q (restrict b F q x) := by
  let U := pushforward p
  let L := pullbackSheaves f
  let V := pullbackSheaves b
  let M := pushforward j
  let D := V ⋙ M
  let e : U ⋙ L ≅ D := NatIso.ofComponents
    (fun G => letI := hIso G; asIso (baseChange f p j b h G))
    (fun g => restrictionBaseChangeOver_naturality f p j b (j ≫ f) rfl h.w.symm g)
  let c_f := (pullbackConstantIso f).inv.app Z
  let c_b := (pullbackConstantIso b).inv.app Z
  let u := c_f ≫ L.map (directImageConstant p) ≫ e.hom.app (C Y)
  let v := directImageConstant j ≫ M.map c_b
  have hLeft (G : Ab Y) (n : ℕ) (z : G.H n) :
      Sheaf.H.map (baseChange f p j b h G) n
        (restrict f (U.obj G) n (toDirectImage p G n z)) =
      comparison D u G n z :=
    PhilipponExtComparisonComposition.comparison_comp_iso U L D e
      (directImageConstant p) c_f n G z
  have hRight (G : Ab Y) (n : ℕ) (z : G.H n) :
      toDirectImage j (V.obj G) n (restrict b G n z) = comparison D v G n z := by
    have he := PhilipponExtComparisonComposition.comparison_comp_iso V M D (Iso.refl D)
      c_b (directImageConstant j) n G z
    let w := toDirectImage j (V.obj G) n (restrict b G n z)
    change w.comp (Ext.mk₀ (𝟙 (D.obj G))) (add_zero n) =
      comparison D (directImageConstant j ≫ M.map c_b ≫ 𝟙 (D.obj (C Y))) G n z at he
    have hArrow : directImageConstant j ≫ M.map c_b ≫ 𝟙 (D.obj (C Y)) = v :=
      congrArg (fun a => directImageConstant j ≫ a) (Category.comp_id (M.map c_b))
    exact (Ext.comp_mk₀_id w).symm.trans (he.trans (congrArg (fun a => comparison D a G n z) hArrow))
  have huv : u = v := constant_square f p j b h
  rw [hLeft, hRight, huv]

end ExactDirectImage

include h in
/-- For a finite morphism, the field-extension comparison for a direct
image is equivalent to comparison on the source. This applies to any
cartesian base change and any abelian coefficient sheaf. -/
theorem bijective_restrict_directImage_iff [IsFinite p] (F : Ab Y) (q : ℕ) :
    Function.Bijective (restrict f ((pushforward p).obj F) q) ↔
      Function.Bijective (restrict b F q) := by
  let : IsFinite j := MorphismProperty.of_isPullback h.flip inferInstance
  let : PreservesFiniteColimits (pushforward p) := PhilipponEtaleFiniteCohomology.preservesFiniteColimits p
  let : PreservesFiniteColimits (pushforward j) := PhilipponEtaleFiniteCohomology.preservesFiniteColimits j
  let δ := baseChange f p j b h F
  let : IsIso δ := PhilipponEtaleFiniteBaseChange.isIso_comparison f p j b h F
  let d := Sheaf.H.map δ q
  let u := toDirectImage p F q
  let v := toDirectImage j ((pullbackSheaves b).obj F) q
  let s := restrict f ((pushforward p).obj F) q
  let t := restrict b F q
  have hd : Function.Bijective d := ConcreteCategory.bijective_of_isIso
    ((Sheaf.functorH S.smallEtaleTopology q).map δ)
  have hu := bijective_toDirectImage p F q
  have hv := bijective_toDirectImage j ((pullbackSheaves b).obj F) q
  have hC : (d ∘ s) ∘ u = v ∘ t := funext fun x =>
    cohomology_square f p j b h (PhilipponEtaleFiniteBaseChange.isIso_comparison f p j b h) F q x
  exact (Function.Bijective.of_comp_iff' hd s).symm.trans
    ((Function.Bijective.of_comp_iff (d ∘ s) hu).symm.trans
      ((congrArg Function.Bijective hC).to_iff.trans (Function.Bijective.of_comp_iff' hv t)))

end PhilipponEtaleFiniteCohomologyBaseChange

end


