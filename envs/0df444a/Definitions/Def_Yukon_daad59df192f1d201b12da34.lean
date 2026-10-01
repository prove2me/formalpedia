-- Prove2me | Definitions.Def_Yukon_daad59df192f1d201b12da34
-- name    : Yukon_daad59df192f1d201b12da34
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:38:23.897281+00:00
-- url     : https://prove2.me/theorems/aa9a79d4-dbc8-4157-8b4c-ae31ed9bafc8
-- title:
--   YukonModule.PolyFun.Logic.HEq.part0
-- statement:
--   Source module PolyFun.Logic.HEq.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/Logic/HEq.lean
--
--   provider-v8:058d5fb88dead52daaf2714965f4d9bc9da8af414ab2520fa7192247141683fa
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODowNThkNWZiODhkZWFkNTJkYWFmMjcxNDk2NWY0ZDliYzlkYThhZjQxNGFiMjUyMGZhNzE5MjI0NzE0MTY4M2ZhIiwiaGFzaCI6IjU5ODI5M2I0ODhmNGI1NTdiOTBkZjQwZGQyNDVlMDBiNGMwMmI1NDUzZDcwNmQ5NDU0ZWQ5Y2I0NjUwNmM1OWIiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uX2RhYWQ1OWRmMTkyZjFkMjAxYjEyZGEzNCIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# Heterogeneous equality helper lemmas

This file contains small `HEq` lemmas that belong in Mathlib rather than in
domain-specific developments.
-/

@[expose] public section

universe u v w

namespace PolyFun
namespace Logic

/-- Apply a dependent binary function to equal indices and heterogeneously
equal arguments. -/
theorem dependent_apply_heq
    {A : Sort u} {B : A → Sort v} {C : A → Sort w}
    (function : (a : A) → B a → C a)
    {a a' : A} (ha : a = a') {b : B a} {b' : B a'} (hb : b ≍ b') :
    function a b ≍ function a' b' := by
  subst a'
  cases hb
  rfl

end Logic
end PolyFun

namespace Prod

/-- Build a heterogeneous equality between pairs with the same first component
from a heterogeneous equality between their second components. -/
theorem mk_heq {α : Type u} {β β' : Type v}
    {a : α} {b : β} {b' : β'} (h : b ≍ b') :
    ((a, b) : α × β) ≍ ((a, b') : α × β') := by
  cases h
  rfl

end Prod


