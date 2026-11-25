-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleCohomologyConnectingMaps
-- name    : AlgebraicGeometry_EtaleCohomologyConnectingMaps
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-25T06:03:34.895984+00:00
-- url     : https://prove2.me/theorems/0e1b6e01-ef90-4d0a-92fe-84cd0c5d4cc5
-- title:
--   Connecting maps and composition for exact-functor comparisons of Ext
-- statement:
--   The cohomology comparison for an exact functor and a coefficient map commutes with connecting homomorphisms. Successive exact-functor comparisons compose via the isomorphism to the composite functor.
-- source:
--   Stacks Project, Theorem 59.51.3, https://stacks.math.columbia.edu/tag/09YQ.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction

noncomputable section

section

attribute [local instance] etaleHasSheafify etaleHasExt etaleEnoughInjectives

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponExtComparison (comparison comparison_mk₀)


namespace PhilipponExtComparisonComposition

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasExt C] [HasExt D]

private theorem comparison_boundary (L : C ⥤ D)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A : C} {B : D} (a : B ⟶ L.obj A) {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) (x : Ext A S.X₃ n) :
    comparison L a S.X₁ (n + 1) (x.comp hS.extClass rfl) =
      (comparison L a S.X₃ n x).comp (hS.map_of_exact L).extClass rfl := by
  change (Ext.mk₀ a).comp ((x.comp hS.extClass rfl).mapExactFunctor L) (zero_add (n + 1)) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc (Ext.mk₀ a) (x.mapExactFunctor L) (hS.map_of_exact L).extClass
    (zero_add n) rfl (zero_add (n + 1))).symm

/-- Ext comparison along an exact functor and a map of short exact
sequences commutes with the connecting maps. -/
theorem comparison_boundary_along (L : C ⥤ D)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {A : C} {B : D} (a : B ⟶ L.obj A) {S : ShortComplex C} {T : ShortComplex D}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S.map L ⟶ T)
    (n : ℕ) (x : Ext A S.X₃ n) :
    (comparison L a S.X₁ (n + 1) (x.comp hS.extClass rfl)).comp
          (Ext.mk₀ φ.τ₁) (add_zero (n + 1)) =
      ((comparison L a S.X₃ n x).comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp hT.extClass rfl := by
  let hL := hS.map_of_exact L
  let y := comparison L a S.X₃ n x
  have h := hL.extClass_naturality hT φ
  rw [comparison_boundary L a hS n x]
  exact (Ext.comp_assoc_of_third_deg_zero y hL.extClass (Ext.mk₀ φ.τ₁) rfl).trans
    ((congrArg (fun cls => y.comp cls rfl) h).trans
      (Ext.comp_assoc_of_second_deg_zero y (Ext.mk₀ φ.τ₃) hT.extClass rfl).symm)

variable {E : Type*} [Category* E] [Abelian E] [HasExt E] [EnoughInjectives C]

set_option maxHeartbeats 800000 in
/-- The Ext comparisons for two exact functors compose, including the
transport along an isomorphism with a third exact functor. -/
theorem comparison_comp_iso (L : C ⥤ D) (M : D ⥤ E) (N : C ⥤ E)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [M.Additive] [PreservesFiniteLimits M] [PreservesFiniteColimits M]
    [N.Additive] [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    (e : L ⋙ M ≅ N) {A : C} {B : D} {T : E}
    (a : B ⟶ L.obj A) (b : T ⟶ M.obj B)
    (q : ℕ) (F : C) (x : Ext A F q) :
    (comparison M b (L.obj F) q (comparison L a F q x)).comp (Ext.mk₀ (e.hom.app F))
      (add_zero q) = comparison N (b ≫ M.map a ≫ e.hom.app A) F q x := by
  induction q generalizing F with
  | zero =>
    obtain ⟨v, rfl⟩ := (Ext.mk₀_bijective A F).surjective x
    rw [comparison_mk₀, comparison_mk₀, Ext.mk₀_comp_mk₀, comparison_mk₀]
    congr 1
    simp only [Functor.map_comp, Category.assoc]
    exact congrArg (fun m => b ≫ M.map a ≫ m) (e.hom.naturality v)
  | succ q ih =>
    let i := Injective.ι F
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel i }
    let hL := hS.map_of_exact L
    let hM := hL.map_of_exact M
    let hN := hS.map_of_exact N
    have hKill : x.comp (Ext.mk₀ S.f) (add_zero (q + 1)) = 0 := Ext.eq_zero_of_injective _
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ A hS x hKill (n₀ := q) rfl
    let t : (S.map L).map M ⟶ S.map N :=
      { τ₁ := e.hom.app S.X₁
        τ₂ := e.hom.app S.X₂
        τ₃ := e.hom.app S.X₃
        comm₁₂ := (e.hom.naturality S.f).symm
        comm₂₃ := (e.hom.naturality S.g).symm }
    have hNat := hM.extClass_naturality hN t
    change hM.extClass.comp (Ext.mk₀ (e.hom.app S.X₁)) (add_zero 1) =
      (Ext.mk₀ (e.hom.app S.X₃)).comp hN.extClass (zero_add 1) at hNat
    let v := comparison M b (L.obj S.X₃) q (comparison L a S.X₃ q y)
    let η₁ := Ext.mk₀ (e.hom.app S.X₁)
    let η₃ := Ext.mk₀ (e.hom.app S.X₃)
    let d := comparison N (b ≫ M.map a ≫ e.hom.app A) S.X₃ q y
    let l := comparison L a S.X₃ q y
    let k := comparison M b (L.obj S.X₁) (q + 1)
    let c := comparison N (b ≫ M.map a ≫ e.hom.app A) S.X₁ (q + 1)
    calc
      _ = (k (comparison L a S.X₁ (q + 1) (y.comp hS.extClass rfl))).comp η₁
          (add_zero (q + 1)) :=
        congrArg (fun z => (k (comparison L a S.X₁ (q + 1) z)).comp η₁ _) hy.symm
      _ = (k (l.comp hL.extClass rfl)).comp η₁ (add_zero (q + 1)) :=
        congrArg (fun z => (k z).comp η₁ _) (comparison_boundary L a hS q y)
      _ = (v.comp hM.extClass rfl).comp η₁ (add_zero (q + 1)) :=
        congrArg (fun z : Ext T (M.obj (L.obj S.X₁)) (q + 1) =>
          z.comp η₁ (add_zero (q + 1))) (comparison_boundary M b hL q l)
      _ = v.comp (hM.extClass.comp η₁ (add_zero 1)) rfl :=
        Ext.comp_assoc_of_third_deg_zero _ _ _ rfl
      _ = v.comp (η₃.comp hN.extClass (zero_add 1)) rfl :=
        congrArg (fun z => v.comp z rfl) hNat
      _ = (v.comp η₃ (add_zero q)).comp hN.extClass rfl :=
        (Ext.comp_assoc_of_second_deg_zero _ _ _ rfl).symm
      _ = d.comp hN.extClass rfl := congrArg (fun z => z.comp hN.extClass rfl) (ih S.X₃ y)
      _ = c (y.comp hS.extClass rfl) := (comparison_boundary N _ hS q y).symm
      _ = _ := congrArg c hy

end PhilipponExtComparisonComposition

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)

namespace PhilipponEtalePrimeTorsionComparison
universe u
private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
variable {X Y : Scheme.{u}} (f : Y ⟶ X)
local instance : (pullbackSheaves f).Additive := (pullbackAdjunction f).left_adjoint_additive
local instance : (pullbackSheaves f).IsLeftAdjoint := (pullbackAdjunction f).isLeftAdjoint

/-- Cohomological restriction with a coefficient map commutes with the
connecting maps of short exact sequences. -/
theorem restrict_boundary_along {S : ShortComplex (Ab X)} {T : ShortComplex (Ab Y)}
    (hS : S.ShortExact) (hT : T.ShortExact) (φ : S.map (pullbackSheaves f) ⟶ T)
    (n : ℕ) (x : S.X₃.H n) :
    (restrict f S.X₁ (n + 1) (x.comp hS.extClass rfl)).comp
        (Ext.mk₀ φ.τ₁) (add_zero (n + 1)) =
      ((restrict f S.X₃ n x).comp (Ext.mk₀ φ.τ₃) (add_zero n)).comp hT.extClass rfl := by
  let α := (pullbackConstantIso f).inv.app (AddCommGrpCat.of (ULift.{u} ℤ))
  have z := PhilipponExtComparisonComposition.comparison_boundary_along (pullbackSheaves f)
    α hS hT φ n x
  exact z

end PhilipponEtalePrimeTorsionComparison

end

end


