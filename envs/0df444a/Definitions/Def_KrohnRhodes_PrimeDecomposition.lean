-- Prove2me | Definitions.Def_KrohnRhodes_PrimeDecomposition
-- name    : KrohnRhodes_PrimeDecomposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T03:58:29.996733+00:00
-- url     : https://prove2.me/theorems/d6e75598-165e-4b9a-86a0-42f72d1b2c3b
-- title:
--   Prime Decomposition
-- statement:
--   Definitions and structural lemmas for Prime Decomposition, from Aditya Rao (adii800/krohn-rhodes-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Krohn-Rhodes prime decomposition of finite monoids into aperiodic and simple-group factors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/KrohnRhodes/PrimeDecomposition.lean

module
public import Definitions.Def_KrohnRhodes_Defs
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_FactorTower
public import Theorems.Thm_KrohnRhodes_MonoidDivides_trans

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option linter.unusedFintypeInType false
namespace KrohnRhodes
open Green
instance instFiniteFunctionEnd (Q : Type) [Finite Q] : Finite (Function.End Q) :=
  inferInstanceAs (Finite (Q → Q))
def resetSubmonoid (Q : Type) : Submonoid (Function.End Q) :=
  Submonoid.closure (Set.range (constEnd : Q → Function.End Q))
def closureMonoid {M Q : Type} [Monoid M] (act : M →* Function.End Q) :
    Submonoid (Function.End Q) :=
  Submonoid.closure (Set.range (⇑act) ∪ Set.range (constEnd : Q → Function.End Q))
def Covers {A B P X R : Type} [Monoid A] [Monoid B] [MulAction A P] [MulAction B X]
    (φ : P × X → R) (w : WreathProduct A B X) (t : Function.End R) : Prop :=
  ∀ (p : P) (y : X), φ (w.func y • p, w.base • y) = t (φ (p, y))
def cQSet {M Q : Type} [Monoid M] (act : M →* Function.End Q) (c : M) : Type :=
  {q : Q // ∃ x : Q, q = act c x}
noncomputable def localActHom {M Q : Type} [Monoid M] (act : M →* Function.End Q) (c : M) :
    LocalDivisor M c →* Function.End (cQSet act c) where
  toFun u := fun p =>
    ⟨act (Classical.choose u.mem_right) p.1, by
      obtain ⟨x, hx⟩ := p.2
      obtain ⟨a, ha⟩ := u.mem_left
      refine ⟨act a x, ?_⟩
      have hb := Classical.choose_spec u.mem_right
      rw [hx]
      calc act (Classical.choose u.mem_right) (act c x)
          = act (Classical.choose u.mem_right * c) x := by rw [map_mul]; rfl
        _ = act u.val x := by rw [← hb]
        _ = act (c * a) x := by rw [← ha]
        _ = act c (act a x) := by rw [map_mul]; rfl⟩
  map_one' := by
    funext p
    apply Subtype.ext
    obtain ⟨x, hx⟩ := p.2
    have hcb : c = Classical.choose (1 : LocalDivisor M c).mem_right * c :=
      (LocalDivisor.one_val).symm.trans
        (Classical.choose_spec (1 : LocalDivisor M c).mem_right)
    change act (Classical.choose (1 : LocalDivisor M c).mem_right) p.1 = p.1
    rw [hx]
    calc act (Classical.choose (1 : LocalDivisor M c).mem_right) (act c x)
        = act (Classical.choose (1 : LocalDivisor M c).mem_right * c) x := by
          rw [map_mul]; rfl
      _ = act c x := by rw [← hcb]
  map_mul' := by
    intro u v
    funext p
    apply Subtype.ext
    obtain ⟨x, hx⟩ := p.2
    have hbu := Classical.choose_spec u.mem_right
    have hbv := Classical.choose_spec v.mem_right
    have hbuv := Classical.choose_spec (u * v).mem_right
    have hv0 := Classical.choose_spec v.mem_left
    change act (Classical.choose (u * v).mem_right) p.1
        = act (Classical.choose u.mem_right) (act (Classical.choose v.mem_right) p.1)
    rw [hx]
    have lhs : act (Classical.choose (u * v).mem_right) (act c x)
        = act (u.val * Classical.choose v.mem_left) x := by
      calc act (Classical.choose (u * v).mem_right) (act c x)
          = act (Classical.choose (u * v).mem_right * c) x := by rw [map_mul]; rfl
        _ = act ((u * v).val) x := by rw [← hbuv]
        _ = act (u.val * Classical.choose v.mem_left) x := by rw [LocalDivisor.mul_val]
    have rhs : act (Classical.choose u.mem_right)
          (act (Classical.choose v.mem_right) (act c x))
        = act (u.val * Classical.choose v.mem_left) x := by
      calc act (Classical.choose u.mem_right)
            (act (Classical.choose v.mem_right) (act c x))
          = act (Classical.choose u.mem_right)
              (act (Classical.choose v.mem_right * c) x) := by rw [map_mul]; rfl
        _ = act (Classical.choose u.mem_right) (act v.val x) := by rw [← hbv]
        _ = act (Classical.choose u.mem_right)
              (act (c * Classical.choose v.mem_left) x) := by rw [← hv0]
        _ = act (Classical.choose u.mem_right)
              (act c (act (Classical.choose v.mem_left) x)) := by rw [map_mul]; rfl
        _ = act (Classical.choose u.mem_right * c)
              (act (Classical.choose v.mem_left) x) := by rw [map_mul]; rfl
        _ = act u.val (act (Classical.choose v.mem_left) x) := by rw [← hbu]
        _ = act (u.val * Classical.choose v.mem_left) x := by rw [map_mul]; rfl
    rw [lhs, rhs]
def extAct {M Q : Type} [Monoid M] (act : M →* Function.End Q) (N : Submonoid M) :
    ↥N →* Function.End (Q ⊕ ↥N) where
  toFun n := fun s =>
    Sum.elim (fun q => Sum.inl (act n.1 q)) (fun m => Sum.inr (n * m)) s
  map_one' := by
    funext s
    cases s with
    | inl q =>
        change Sum.inl (act ((1 : ↥N) : M) q) = _
        rw [OneMemClass.coe_one, map_one]
        rfl
    | inr m =>
        change Sum.inr ((1 : ↥N) * m) = _
        rw [one_mul]
        rfl
  map_mul' := by
    intro n₁ n₂
    funext s
    cases s with
    | inl q =>
        change Sum.inl (act ((n₁ * n₂ : ↥N) : M) q)
            = Sum.inl (act (n₁ : M) (act (n₂ : M) q))
        rw [MulMemClass.coe_mul, map_mul]
        rfl
    | inr m =>
        change Sum.inr (n₁ * n₂ * m) = Sum.inr (n₁ * (n₂ * m))
        rw [mul_assoc]
def dksProj {M Q : Type} [Monoid M] (act : M →* Function.End Q) (c : M)
    (N : Submonoid M) : cQSet act c × (Q ⊕ ↥N) → Q :=
  fun s => Sum.elim (fun q => q) (fun n : ↥N => act n.1 s.1.1) s.2
def groupProj {G Q : Type} [Group G] (act : G →* Function.End Q) : Q × G → Q :=
  fun s => act s.2 s.1
end KrohnRhodes


