-- Prove2me | Definitions.Def_Erdos1219_Defs
-- name    : Erdos1219_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:39:34.297901+00:00
-- url     : https://prove2.me/theorems/54443a49-ed80-4709-8b05-e97ecffd8f23
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Ji Ho Bae (jbaelaw/erdos1219-lean; see pinned Apache-2.0 LICENSE and source headers)'s pinned Erdos Problem 1219 on cardinal partition relations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Defs.lean

import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.Data.Finset.Card
set_option autoImplicit false
open Cardinal
namespace Erdos1219
universe u
variable {V : Type u}
def Homog (f : V → V → Bool) (c : Bool) (H : Set V) : Prop :=
  ∀ x ∈ H, ∀ y ∈ H, x ≠ y → f x y = c
noncomputable def ofFinsetColouring (col : {s : Finset V // s.card = 2} → Bool) (x y : V) :
    Bool := by
  classical
  exact if h : x = y then false else col ⟨{x, y}, Finset.card_pair h⟩
def PartitionArrow (κ α : Cardinal.{u}) : Prop :=
  ∀ (A : Type u), #A = κ →
    ∀ col : {s : Finset A // s.card = 2} → Bool,
      ∃ (c : Bool) (H : Set A), #H = α ∧
        ∀ (s : Finset A) (hs : s.card = 2), (↑s : Set A) ⊆ H → col ⟨s, hs⟩ = c
end Erdos1219


