-- Prove2me | Definitions.Def_KirkmanLib_Solution
-- name    : KirkmanLib_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:46:22.822843+00:00
-- url     : https://prove2.me/theorems/8a8ebb90-320c-4f63-b242-490061915f55
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Juan Pablo Traverso Gianini (jtraverso/kirkman-steiner-triple-systems; see pinned Apache-2.0 LICENSE and source headers)'s pinned Kirkman theorem on existence of Steiner triple systems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/kirkman-steiner-triple-systems/blob/18551414d822f7fa4fb7535dc43733c4b316c3a8/Solution.lean

module
public import Mathlib
public import Definitions.Def_KirkmanLib_Kirkman
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
namespace KirkmanTheorem
def IsSTS {v : ℕ} (𝒯 : Finset (Finset (Fin v))) : Prop :=
  (∀ T ∈ 𝒯, #T = 3) ∧ ∀ x y : Fin v, x ≠ y → ∃! T, T ∈ 𝒯 ∧ x ∈ T ∧ y ∈ T
end KirkmanTheorem


