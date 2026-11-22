-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:55.030134+00:00
-- url     : https://prove2.me/theorems/a8c91777-d26d-463d-966b-bffa585f8494
-- title:
--   Const Gen
-- statement:
--   Definitions and structural lemmas for Const Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ConstGen.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out
open Semi
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]
def translPt {T : Over S} (x : T ⟶ A) : T ⊗ A ⟶ A := lift (fst T A ≫ x) (snd T A) ≫ μ[A]
def translT {T : Over S} (x : T ⟶ A) : T ⊗ A ⟶ T ⊗ A := lift (fst T A) (translPt A x)
def thetaLB (L : LB A.left) (k : ℤ) {T : Over S} (x : T ⟶ A) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 2) ![(snd T A).left, (translPt A x).left] ![k, -k]
structure ThetaGrp (L : LB A.left) (k : ℤ) (T : Over S) where

  pt : T ⟶ A

  φ : LB.Gen (thetaLB A L k pt)

  isGen : φ.IsGen
def constGen (L : LB A.left) {T : Over S} (c : Γ(T.left, ⊤)ˣ) :
    LB.Gen (LB.LinComb L (Y := (T ⊗ A).left) (K := PEmpty) PEmpty.elim PEmpty.elim) where
  s := fun _ => res le_top (Units.map (fst T A).left.appTop.hom.toMonoidHom c)
def CommIsOf (L : LB A.left) (k : ℤ) {T : Over S} (θx θy : ThetaGrp A L k T)
    (c : Γ(T.left, ⊤)ˣ) : Prop :=
  LB.Gen.Corr L _ _ _ _
    (LB.mulGen L _ _ _ _ θx.φ (LB.pullGen L _ _ θy.φ (translT A θx.pt).left))
    (LB.mulGen L _ _ _ _
      (LB.mulGen L _ _ _ _ θy.φ (LB.pullGen L _ _ θx.φ (translT A θy.pt).left))
      (constGen A L c))
abbrev overRes {T : Over S} (V : T.left.Opens) : Over S := Over.mk (V.ι ≫ T.hom)
def overResι {T : Over S} (V : T.left.Opens) : overRes V ⟶ T := Over.homMk V.ι rfl
def unitRes {T : Over S} (V : T.left.Opens) (c : Γ(T.left, ⊤)ˣ) : Γ((overRes V).left, ⊤)ˣ :=
  Units.map V.ι.appTop.hom.toMonoidHom c
def WeilIs (L : LB A.left) (k : ℤ) {T : Over S} (x y : T ⟶ A) (c : Γ(T.left, ⊤)ˣ) : Prop :=
  ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
    (∃ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x ∧ θy.pt = overResι V ≫ y) ∧
    ∀ θx θy : ThetaGrp A L k (overRes V), θx.pt = overResι V ≫ x → θy.pt = overResι V ≫ y →
      CommIsOf A L k θx θy (unitRes V c)
end ReciprocityTheory.ChartRestriction.G.Out


