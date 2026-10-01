-- Prove2me | Definitions.Def_Yukon_f25f93421272fca15844f5d1
-- name    : Yukon_f25f93421272fca15844f5d1
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:38:16.437611+00:00
-- url     : https://prove2.me/theorems/ebf35f47-b8b0-48a8-81c2-3e0755c61186
-- title:
--   YukonModule.VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.SimpAttr.part0
-- statement:
--   Source module VCVio.CryptoFoundations.FiatShamir.Sigma.Stateful.SimpAttr.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/VCVio/CryptoFoundations/FiatShamir/Sigma/Stateful/SimpAttr.lean
--
--   provider-v8:f94c2fd60325836a256a6bc92486e0e3eecde433a85a003967193c37388be036
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODpmOTRjMmZkNjAzMjU4MzZhMjU2YTZiYzkyNDg2ZTBlM2VlY2RlNDMzYTg1YTAwMzk2NzE5M2MzNzM4OGJlMDM2IiwiaGFzaCI6IjI1OWY4MjBjYzhjM2MyZWM0YWFhNjVjN2Y2YjQ0OTAzMWFiNjRmYWQ3OGM5ZTJlMzBiMzRlMWU4NDliNzI3NjIiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uX2YyNWY5MzQyMTI3MmZjYTE1ODQ0ZjVkMSIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import Mathlib.Tactic.Attr.Register


public import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# `fs_simp` simp attribute for the stateful Fiat-Shamir CMA development

This file declares a single named simp set, `fs_simp`, used throughout the
stateful Fiat-Shamir CMA proof stack (everything under
`VCVio/CryptoFoundations/FiatShamir/Sigma/Stateful/`).

Tag handler definitions, frames, lenses, and adversary wrappers with
`@[fs_simp]` and use `simp [fs_simp, ...]` (or `simp only [fs_simp, ...]`) at
call sites instead of re-listing every recurring FS-CMA name on every
`unif/ro/sign/pk` × `none/some` leaf.

This attribute is intentionally **local** to the stateful FS-CMA development;
do not extend it with lemmas from outside `Sigma/Stateful/` or related
adversary helpers. The attribute is registered in its own file because
`register_simp_attr` does not take effect within the same Lean file as its
first use.
-/

@[expose] public section

/-- Simp set for unfolding stateful Fiat-Shamir CMA handlers, frames, lenses,
and adversary wrappers in one shot. Local to `Sigma/Stateful/`. -/
register_simp_attr fs_simp


