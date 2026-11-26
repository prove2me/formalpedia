-- Prove2me | Definitions.Def_KrohnRhodes_Defs
-- name    : KrohnRhodes_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:52:22.195697+00:00
-- url     : https://prove2.me/theorems/84467b77-4b0d-47c9-a7b6-9ccd7732a6ed
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Aditya Rao (adii800/krohn-rhodes-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Krohn-Rhodes prime decomposition of finite monoids into aperiodic and simple-group factors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/Defs.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u v w
namespace Green
variable {M : Type*} [Monoid M]
def L (a b : M) : Prop :=
  ∃ s t : M, s * a = b ∧ t * b = a
def R (a b : M) : Prop :=
  ∃ s t : M, a * s = b ∧ b * t = a
def H (a b : M) : Prop :=
  L a b ∧ R a b
def IsAperiodicElem (a : M) : Prop :=
  ∀ b : M, H a b → a = b
end Green
def SgDiv (S T : Type*) [Mul S] [Mul T] : Prop :=
  ∃ (U : Subsemigroup T) (φ : U →ₙ* S), Function.Surjective φ
@[ext]
structure WreathProduct (A : Type u) (B : Type v) (X : Type w)
    [Monoid A] [Monoid B] [MulAction B X] where
  /-- The decoration function mapping each point of `X` to an element of `A`. -/
  func : X → A
  /-- The component in `B`, which acts on `X`. -/
  base : B
namespace WreathProduct
variable {A : Type u} {B : Type v} {X : Type w}
variable [Monoid A] [Monoid B] [MulAction B X]
instance : Mul (WreathProduct A B X) where
  mul p q := ⟨fun x => p.func (q.base • x) * q.func x, p.base * q.base⟩
end WreathProduct
namespace KrohnRhodes
def MonoidDivides (M : Type*) (N : Type*) [Monoid M] [Monoid N] : Prop :=
  ∃ (S : Submonoid N) (φ : S →* M), Function.Surjective φ
end KrohnRhodes
open Green
inductive KRFactorKind where
  /-- The factor is a finite aperiodic monoid. -/
  | aperiodic : KRFactorKind
  /-- The factor is a finite simple group. -/
  | simpleGroup : KRFactorKind
  deriving DecidableEq, Repr
structure KRFactor where
  /-- The carrier monoid of the factor. -/
  carrier : Type u
  /-- The factor's monoid structure. -/
  [mon : Monoid carrier]
  /-- The factor is finite. -/
  [fin : Finite carrier]
  /-- Whether the factor is an aperiodic atom or a simple-group atom. -/
  kind : KRFactorKind
  /-- The flag is *witnessed*: an `aperiodic`-flagged factor is genuinely
      aperiodic; a `simpleGroup`-flagged factor genuinely carries a finite
      simple-group structure on `carrier` **whose underlying monoid is the
      factor's own monoid field** (`g.toMonoid = mon`).  Recording the
      `g.toMonoid = mon` compatibility lets one transport monoid-indexed data
      between `F.mon` and the witnessed group instance `g`. -/
  isKind :
    (kind = KRFactorKind.aperiodic ∧ (∀ a : carrier, IsAperiodicElem a)) ∨
    (kind = KRFactorKind.simpleGroup ∧
      ∃ (g : Group carrier), g.toMonoid = mon ∧ @IsSimpleGroup carrier g)
attribute [instance] KRFactor.mon KRFactor.fin
def DivTowerWreath : (M : Type u) → [Monoid M] → [Finite M] → List KRFactor.{u} → Prop
  | M, _, _, [] => SgDiv M PUnit.{u + 1}
  | M, _, _, (F :: rest) =>
      ∃ (B : Type u) (_ : Monoid B) (_ : Finite B)
        (Y : Type u) (_ : Fintype Y) (_ : MulAction B Y),
        DivTowerWreath B rest ∧
        SgDiv M (WreathProduct F.carrier B Y)
namespace KrohnRhodes
structure KRFactorTowerGrp (M : Type) [Monoid M] [Finite M] where
  /-- The explicit list of factors, each flagged and witnessed as aperiodic or as a simple
      group. -/
  factors : List KRFactor.{0}
  /-- `M` divides the right-iterated wreath product of `factors`. -/
  divides : DivTowerWreath M factors
  /-- Every SIMPLE-GROUP factor divides `M` (the Krohn-Rhodes prime-divisor guarantee;
      aperiodic factors are only required to be aperiodic). -/
  groupFactorsDivide : ∀ F ∈ factors, F.kind = KRFactorKind.simpleGroup →
    KrohnRhodes.MonoidDivides F.carrier M
end KrohnRhodes


