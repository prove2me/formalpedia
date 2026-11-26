-- Prove2me | Definitions.Def_KrohnRhodes_FactorTower
-- name    : KrohnRhodes_FactorTower
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:57:26.23203+00:00
-- url     : https://prove2.me/theorems/33cac36a-65b8-4e01-b255-48aa2fa3b7db
-- title:
--   Factor Tower
-- statement:
--   Definitions and structural lemmas for Factor Tower, from Aditya Rao (adii800/krohn-rhodes-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Krohn-Rhodes prime decomposition of finite monoids into aperiodic and simple-group factors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/FactorTower.lean

module
public import Definitions.Def_KrohnRhodes_Defs
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_Cayley
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Theorems.Thm_KrohnRhodes_constEnd_mul
public import Theorems.Thm_KrohnRhodes_krasnerKaloujnine_hom_left
attribute [local simp] KrohnRhodes.constEnd_mul
attribute [local simp] KrohnRhodes.krasnerKaloujnine_hom_left


set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.style.show false
set_option linter.unusedSectionVars false
universe u
open Green
namespace KRFactor
def ofAperiodic (A : Type u) [Monoid A] [Finite A]
    (hA : ∀ a : A, IsAperiodicElem a) : KRFactor.{u} where
  carrier := A
  kind := KRFactorKind.aperiodic
  isKind := Or.inl ⟨rfl, hA⟩
def ofSimpleGroup (G : Type u) [g : Group G] [Finite G] [IsSimpleGroup G] :
    KRFactor.{u} where
  carrier := G
  kind := KRFactorKind.simpleGroup
  isKind := Or.inr ⟨rfl, ⟨g, rfl, inferInstance⟩⟩
@[simp] theorem ofAperiodic_carrier (A : Type u) [Monoid A] [Finite A]
    (hA : ∀ a : A, IsAperiodicElem a) : (ofAperiodic A hA).carrier = A := rfl
@[simp] theorem ofAperiodic_kind (A : Type u) [Monoid A] [Finite A]
    (hA : ∀ a : A, IsAperiodicElem a) :
    (ofAperiodic A hA).kind = KRFactorKind.aperiodic := rfl
@[simp] theorem ofSimpleGroup_carrier (G : Type u) [Group G] [Finite G]
    [IsSimpleGroup G] : (ofSimpleGroup G).carrier = G := rfl
@[simp] theorem ofSimpleGroup_kind (G : Type u) [Group G] [Finite G]
    [IsSimpleGroup G] : (ofSimpleGroup G).kind = KRFactorKind.simpleGroup := rfl
end KRFactor
@[simp] theorem divTowerWreath_nil (M : Type u) [Monoid M] [Finite M] :
    DivTowerWreath M [] = SgDiv M PUnit.{u + 1} := rfl
namespace WreathAssoc
variable (G B' B Y X : Type u) [Monoid G] [Monoid B'] [Monoid B]
  [MulAction B' Y] [MulAction B X]
@[instance_reducible]
def actW : MulAction (WreathProduct B' B X) (Y × X) where
  smul w yx := (w.func yx.2 • yx.1, w.base • yx.2)
  one_smul := by
    rintro ⟨y, x⟩
    show ((1 : WreathProduct B' B X).func x • y, (1 : WreathProduct B' B X).base • x) = (y, x)
    rw [WreathProduct.one_func, WreathProduct.one_base, one_smul, one_smul]
  mul_smul := by
    rintro w1 w2 ⟨y, x⟩
    show ((w1 * w2).func x • y, (w1 * w2).base • x) =
         (w1.func (w2.base • x) • (w2.func x • y), w1.base • (w2.base • x))
    rw [WreathProduct.mul_func, WreathProduct.mul_base, mul_smul, mul_smul]
attribute [local instance] actW
def Phi : WreathProduct (WreathProduct G B' Y) B X →ₙ*
    WreathProduct G (WreathProduct B' B X) (Y × X) where
  toFun F := ⟨fun yx => (F.func yx.2).func yx.1, ⟨fun x => (F.func x).base, F.base⟩⟩
  map_mul' := by
    intro F1 F2
    apply WreathProduct.ext
    · funext yx
      obtain ⟨y, x⟩ := yx
      show ((F1 * F2).func x).func y =
          (F1.func (F2.base • x)).func ((F2.func x).base • y) * (F2.func x).func y
      rw [WreathProduct.mul_func, WreathProduct.mul_func]
    · apply WreathProduct.ext
      · funext x; rfl
      · rfl
end WreathAssoc
namespace KrohnRhodes
open Green
def SubFactorsDivide (M : Type u) [Monoid M] (factors : List KRFactor.{u}) : Prop :=
  ∀ F ∈ factors, KrohnRhodes.MonoidDivides F.carrier M
structure KRFactorTowerSub (M : Type u) [Monoid M] [Finite M] where
  /-- The explicit list of factors, each flagged and witnessed as aperiodic or as a simple
      group. -/
  factors : List KRFactor.{u}
  /-- `M` divides the right-iterated wreath product of `factors`. -/
  divides : DivTowerWreath M factors
  /-- Every factor's carrier divides `M` (the subquotient-faithful condition). -/
  factorsDivide : SubFactorsDivide M factors
end KrohnRhodes


