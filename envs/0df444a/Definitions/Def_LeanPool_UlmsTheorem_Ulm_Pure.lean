-- Prove2me | Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
-- name    : LeanPool_UlmsTheorem_Ulm_Pure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:53:48.990591+00:00
-- url     : https://prove2.me/theorems/4a4efe5c-aaf9-448e-963f-5a844799869e
-- title:
--   Pure
-- statement:
--   Definitions and structural lemmas for Pure, from Elan Roth; LeanPool contributors's pinned Ulm’s theorem for abelian p-groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Pure.lean

module
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_Heights
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.NormNum.GCD
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace UlmsTheorem
open Ordinal
universe u
variable (p : ℕ)
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
noncomputable def ulmHeight (x : G) : WithTop Ordinal.{0} :=
  ⨆ (α : Ordinal.{0}) (_ : x ∈ ulmSubgroup p α (G := G)), (α : WithTop Ordinal.{0})
def IsProper (S : AddSubgroup G) (x : G) : Prop :=
  ∀ s : S, ulmHeight p x ≥ ulmHeight p (x + s)
def IsHeightPreserving (φ : G →+ H) : Prop :=
  ∀ (x : G) (α : Ordinal.{0}),
    x ∈ ulmSubgroup p α (G := G) ↔ φ x ∈ ulmSubgroup p α (G := H)
def IsHeightPresOn {A : AddSubgroup G} {B : AddSubgroup H} (φ : A →+ B) : Prop :=
  ∀ (a : A) (α : Ordinal.{0}),
    (a : G) ∈ ulmSubgroup p α (G := G) ↔ (φ a : H) ∈ ulmSubgroup p α (G := H)
noncomputable def pOrder (x : G) : ℕ∞ :=
  ⨅ (n : ℕ) (_ : p ^ n • x = 0), (n : ℕ∞)
def IsPure (A : AddSubgroup G) : Prop :=
  ∀ (n : ℕ) (x : A), (x : G) ∈ pPow p n (G := G) → x ∈ pPow p n (G := A)
def IsIsotype (A : AddSubgroup G) : Prop :=
  ∀ (x : A) (α : Ordinal.{0}),
    (x : G) ∈ ulmSubgroup p α (G := G) ↔ x ∈ ulmSubgroup p α (G := A)
end UlmsTheorem


