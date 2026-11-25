-- Prove2me | Definitions.Def_HiltonMilnerLib_HMCore
-- name    : HiltonMilnerLib_HMCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:54:01.006601+00:00
-- url     : https://prove2.me/theorems/8749c68a-fe93-4765-b906-bcf2928324d4
-- title:
--   HMCore
-- statement:
--   Definitions and structural lemmas for HMCore, from Juan Pablo Traverso Gianini (jtraverso/hilton-milner; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Hilton-Milner theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/HMCore.lean

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_CrossIntersecting
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace HiltonMilner
def NonTriv (X : Finset ℕ) (𝒜 : Finset (Finset ℕ)) : Prop :=
  ∀ x ∈ X, ∃ A ∈ 𝒜, x ∉ A
def hmNum (n k : ℕ) : ℕ := (n - 1).choose (k - 1) - (n - k - 1).choose (k - 1) + 1
end HiltonMilner


