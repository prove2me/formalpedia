-- Prove2me | Definitions.Def_HiltonMilnerLib_CrossIntersecting
-- name    : HiltonMilnerLib_CrossIntersecting
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T17:49:12.562241+00:00
-- url     : https://prove2.me/theorems/082ad833-b28f-4f05-8419-a205eef1f5da
-- title:
--   Cross Intersecting
-- statement:
--   Definitions and structural lemmas for Cross Intersecting, from Juan Pablo Traverso Gianini (jtraverso/hilton-milner; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Hilton-Milner theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/CrossIntersecting.lean

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace HiltonMilner
abbrev low (z : ℕ) (𝒜 : Finset (Finset ℕ)) : Finset (Finset ℕ) := 𝒜.filter (fun A => z ∉ A)
abbrev high (z : ℕ) (𝒜 : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  (𝒜.filter (fun A => z ∈ A)).image (fun A => A.erase z)
end HiltonMilner


