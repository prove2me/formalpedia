-- Prove2me | Definitions.Def_HajnalSzemeredi_Structure
-- name    : HajnalSzemeredi_Structure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T22:44:29.158948+00:00
-- url     : https://prove2.me/theorems/7228c73c-37c1-562a-b582-4322d8385e17
-- title:
--   Structure
-- statement:
--   Definitions and structural lemmas for Structure, from Juan Pablo Traverso Gianini (jtraverso/hajnal-szemeredi; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Hajnal-Szemeredi theorem on equitable vertex colourings development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/hajnal-szemeredi/blob/2a71de73134d10cdfecfe52cec652a386f1aa356/HajnalSzemeredi/Structure.lean

module
public import Definitions.Def_HajnalSzemeredi_Count
public import Definitions.Def_HajnalSzemeredi_Reach
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open Classical Finset Relation
namespace HajnalSzemeredi
variable {V : Type*} {G : SimpleGraph V}
structure Ctx (G : SimpleGraph V) (S : Finset V) (P : Finset ℕ) (c : V → ℕ)
    (r s lo hi : ℕ) : Prop where
  near : IsNear G S P c s lo hi
  deg : DegLe G S r
  card_P : P.card = r + 1
  hi_not : hi ∉ acc G S P c lo
def avoid (G : SimpleGraph V) (S : Finset V) (c : V → ℕ) (W : ℕ) (a b : ℕ) : Prop :=
  Mov G S c a b ∧ a ≠ W ∧ b ≠ W
def T (G : SimpleGraph V) (S : Finset V) (P : Finset ℕ) (c : V → ℕ) (lo W : ℕ) : Finset ℕ :=
  ((acc G S P c lo).erase W).filter fun X => ¬ ReflTransGen (avoid G S c W) X lo
namespace Ctx
variable {S : Finset V} {P : Finset ℕ} {c : V → ℕ} {r s lo hi : ℕ}
end Ctx
end HajnalSzemeredi


