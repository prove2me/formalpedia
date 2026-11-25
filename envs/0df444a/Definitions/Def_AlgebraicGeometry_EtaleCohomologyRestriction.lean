-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
-- name    : AlgebraicGeometry_EtaleCohomologyRestriction
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T01:00:29.935832+00:00
-- url     : https://prove2.me/theorems/0172b51a-0a0d-4800-9571-ccc499f4c7e4
-- title:
--   Restriction in small étale cohomology and the inverse-image unit
-- statement:
--   Restriction is defined using exact inverse image on Ext. Its composite with the exact direct-image comparison agrees with the map of the inverse-image unit.
-- source:
--   Stacks Project, Proposition 59.55.2, https://stacks.math.columbia.edu/tag/03QP.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.Data.Nat.Prime.Basic

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

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits


namespace PhilipponExtComparison

universe u v u' v' w w'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
  (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  {Q : C} {P : D} (p : P ⟶ R.obj Q)

/-- Apply an exact functor to Ext, then precompose with the comparison map. -/
def comparison (M : C) (n : ℕ) : Ext Q M n →+ Ext P (R.obj M) n :=
  ((Ext.mk₀ p).precomp (R.obj M) (zero_add n)).comp (R.mapExtAddHom Q M n)

private theorem comparison_comp {M N : C} {n k m : ℕ} (x : Ext Q M n) (a : Ext M N k)
    (h : n + k = m) :
    comparison R p N m (x.comp a h) =
      (comparison R p M n x).comp (a.mapExactFunctor R) h := by
  change (Ext.mk₀ p).comp ((x.comp a h).mapExactFunctor R) (zero_add m) = _
  rw [Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc (Ext.mk₀ p) (x.mapExactFunctor R) (a.mapExactFunctor R)
    (zero_add n) h (by simpa using h)).symm

theorem comparison_mk₀ {M : C} (x : Q ⟶ M) :
    comparison R p M 0 (Ext.mk₀ x) = Ext.mk₀ (p ≫ R.map x) := by
  change (Ext.mk₀ p).comp ((Ext.mk₀ x).mapExactFunctor R) (zero_add 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

private theorem comparison_boundary {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) (x : Ext Q S.X₃ n) :
    comparison R p S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (comparison R p S.X₃ n x).comp (hS.map_of_exact R).extClass rfl := by
  rw [comparison_comp, Ext.mapExactFunctor_extClass]

set_option maxHeartbeats 1200000 in
/-- The two Ext comparisons of an exact adjoint pair compose to the map
induced by its unit on the second argument. -/
theorem comparison_adjoint_unit [EnoughInjectives C]
    (L : C ⥤ D) (U : D ⥤ C) [L.Additive] [U.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (adj : L ⊣ U) (A : C) (B : D) (e : L.obj A ≅ B)
    (q : ℕ) (F : C) (x : Ext A F q) :
    comparison U (adj.homEquiv A B e.hom) (L.obj F) q (comparison L e.inv F q x) =
      x.comp (Ext.mk₀ (adj.unit.app F)) (add_zero q) := by
  induction q generalizing F with
  | zero =>
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective A F).surjective x
      rw [comparison_mk₀, comparison_mk₀, Ext.mk₀_comp_mk₀]
      congr 1
      rw [← adj.homEquiv_naturality_right, e.hom_inv_id_assoc,
        Adjunction.homEquiv_unit]
      exact (adj.unit.naturality f).symm
  | succ q ih =>
      let i := Injective.ι F
      let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
      have hSL := hS.map_of_exact L
      have hSU := hSL.map_of_exact U
      have hKill : x.comp (Ext.mk₀ S.f) (add_zero (q + 1)) = 0 :=
        Ext.eq_zero_of_injective _
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ A hS x hKill (n₀ := q) rfl
      let t : S ⟶ (S.map L).map U :=
        { τ₁ := adj.unit.app S.X₁
          τ₂ := adj.unit.app S.X₂
          τ₃ := adj.unit.app S.X₃
          comm₁₂ := (adj.unit.naturality S.f).symm
          comm₂₃ := (adj.unit.naturality S.g).symm }
      have hNat := hS.extClass_naturality hSU t
      change hS.extClass.comp (Ext.mk₀ (adj.unit.app S.X₁)) (add_zero 1) =
        (Ext.mk₀ (adj.unit.app S.X₃)).comp hSU.extClass (zero_add 1) at hNat
      let a := adj.homEquiv A B e.hom
      let left := comparison L e.inv F (q + 1)
      let right := comparison U a (L.obj F) (q + 1)
      let v := comparison L e.inv S.X₃ q y
      let η₁ := Ext.mk₀ (adj.unit.app S.X₁)
      let η₃ := Ext.mk₀ (adj.unit.app S.X₃)
      calc
        _ = right (left (y.comp hS.extClass rfl)) := congrArg (fun z => right (left z)) hy.symm
        _ = right (v.comp hSL.extClass rfl) :=
          congrArg right (comparison_boundary L e.inv hS q y)
        _ = (comparison U a (L.obj S.X₃) q v).comp hSU.extClass rfl :=
          comparison_boundary U a hSL q v
        _ = (y.comp η₃ (add_zero q)).comp hSU.extClass rfl :=
          congrArg (fun z => z.comp hSU.extClass rfl) (ih S.X₃ y)
        _ = y.comp (η₃.comp hSU.extClass (zero_add 1)) rfl :=
          Ext.comp_assoc_of_second_deg_zero _ _ _ rfl
        _ = y.comp (hS.extClass.comp η₁ (add_zero 1)) rfl :=
          congrArg (fun z => y.comp z rfl) hNat.symm
        _ = (y.comp hS.extClass rfl).comp η₁ (add_zero (q + 1)) :=
          (Ext.comp_assoc_of_third_deg_zero _ _ _ rfl).symm
        _ = _ := congrArg (fun z => z.comp η₁ (add_zero (q + 1))) hy

end PhilipponExtComparison

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtalePullbackSquareUnits (restrictionBaseChangeOver)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleCohomologyUnits

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev H (X : Scheme.{u}) (q : ℕ) := Sheaf.functorH X.smallEtaleTopology q
private abbrev Z := AddCommGrpCat.of (ULift.{u} ℤ)
private abbrev C (X : Scheme.{u}) := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj Z

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- The cohomology map of the inverse-image unit. -/
abbrev unitMap (F : Ab X) (q : ℕ) := (H X q).map ((pullbackAdjunction p).unit.app F)

private def directImageConstant : C X ⟶ (pushforward p).obj (C Y) :=
  (pullbackAdjunction p).homEquiv _ _ ((pullbackConstantIso p).hom.app Z)

variable [PreservesFiniteColimits (pushforward p)]

/-- The exact direct-image comparison, in the direction given by applying
pushforward to extensions. -/
def toDirectImage (F : Ab Y) (q : ℕ) : F.H q →+ ((pushforward p).obj F).H q :=
  PhilipponExtComparison.comparison (pushforward p) (directImageConstant p) F q

end PhilipponEtaleCohomologyUnits

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections globalSectionsIso)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtalePrimeTorsionComparison

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev constants (X : Scheme.{u}) := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev Z := AddCommGrpCat.of (ULift.{u} ℤ)

private def constantAdj (X : Scheme.{u}) : constants X ⊣ globalSections X :=
  constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u}
    (IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) (Scheme.Etale.mk (𝟙 X)) Over.mkIdTerminal)

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

private def composedAdj :=
  ((constantAdj X).comp (pullbackAdjunction f)).ofNatIsoRight (globalSectionsIso f)

private def constantComparison : (constants Y).obj Z ⟶
    (pullbackSheaves f).obj ((constants X).obj Z) :=
  ((constantAdj Y).leftAdjointUniq (composedAdj f)).hom.app Z

private instance : (pullbackSheaves f).Additive := (pullbackAdjunction f).left_adjoint_additive
private instance : (pullbackSheaves f).IsLeftAdjoint := (pullbackAdjunction f).isLeftAdjoint

/-- Restriction on étale cohomology, defined by applying the exact inverse
image to Ext and comparing the two constant integer sheaves. -/
def restrict (F : Ab X) (n : ℕ) : F.H n →+ ((pullbackSheaves f).obj F).H n :=
  PhilipponExtComparison.comparison (pullbackSheaves f) (constantComparison f) F n

end PhilipponEtalePrimeTorsionComparison

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleCohomologyUnits (toDirectImage unitMap)
open PhilipponEtalePrimeTorsionComparison (restrict)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleCohomologyRestrictionUnit

universe u

set_option maxHeartbeats 900000 in
/-- For an exact direct image, restriction in étale cohomology becomes the
map induced by the inverse-image unit under the direct-image comparison. -/
theorem toDirectImage_restrict_eq_unitMap {X Y : Scheme.{u}} (p : Y ⟶ X)
    [PreservesFiniteColimits (pushforward p)]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (q : ℕ) (x : F.H q) :
    toDirectImage p ((pullbackSheaves p).obj F) q (restrict p F q x) = unitMap p F q x := by
  let C (S : Scheme.{u}) :=
    (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  let e := (pullbackConstantIso p).app (AddCommGrpCat.of (ULift.{u} ℤ))
  exact PhilipponExtComparison.comparison_adjoint_unit (pullbackSheaves p) (pushforward p)
    (pullbackAdjunction p) (C X) (C Y) e q F x

end PhilipponEtaleCohomologyRestrictionUnit

end

end


