-- Prove2me | Definitions.Def_Yukon_950ab98b4aafc32b0f064af3
-- name    : Yukon_950ab98b4aafc32b0f064af3
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:38:23.931126+00:00
-- url     : https://prove2.me/theorems/862297e8-c4b6-4f37-ba12-7cb8b72fa247
-- title:
--   YukonModule.ArkLib.ToMathlib.Control.MonadLift.part0
-- statement:
--   Source module ArkLib.ToMathlib.Control.MonadLift.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/ToMathlib/Control/MonadLift.lean
--
--   provider-v8:0847097c31c8d4a3955f406c8053db53cd84706612890041249a00756c8ea5f8
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODowODQ3MDk3YzMxYzhkNGEzOTU1ZjQwNmM4MDUzZGI1M2NkODQ3MDY2MTI4OTAwNDEyNDlhMDA3NTZjOGVhNWY4IiwiaGFzaCI6IjFiZWQyNDYyYzg3MDViYjY2MGI1MzQ0ZjQ2OGVjNTU2ODQ2MjYwNWQ1NmQ0MjQzMDdlNjkxMGE2ZDA0ZDI5MjgiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uXzk1MGFiOThiNGFhZmMzMmIwZjA2NGFmMyIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/


import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# Pushing a projection through a monad lift

`monadLift_bind_map` moves a post-composed function from the continuation of a lifted computation
into the lifted computation itself. It is the `monadLift`-generic form of `bind_map_left`, and is a
two-step composite of the Lean core lemmas `monadLift_map` and `bind_map_left`.

Upstreaming candidate: the statement mentions nothing outside Lean core, so it belongs beside
`Init.Control.Lawful.MonadLift.Lemmas`.

Note on normal forms: core's simp set already rewrites this lemma's right-hand side *into* its
left-hand side (via `liftM_map` and `bind_map_left`, both `@[simp]`), so this is deliberately not
tagged `@[simp]` — use it explicitly, typically right-to-left to expose a lemma about `h <$> x`.
-/

universe u v w

/-- Lifting a computation and post-composing `h` in the continuation is the same as lifting the
`h`-mapped computation. Use it to move a projection inside a `monadLift` so that lemmas about the
projected computation apply. -/
theorem monadLift_bind_map {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] {α α' γ : Type u}
    (h : α → α') (x : m α) (f : α' → n γ) :
    ((monadLift x : n α) >>= fun a => f (h a)) = (monadLift (h <$> x) : n α') >>= f := by
  rw [monadLift_map, bind_map_left]

/-- The `Prod.fst` case of `monadLift_bind_map`: discard the second component of a lifted
pair-valued computation. -/
theorem monadLift_bind_fst {m : Type u → Type v} {n : Type u → Type w}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [MonadLiftT m n] [LawfulMonadLiftT m n] {α β γ : Type u}
    (x : m (α × β)) (f : α → n γ) :
    ((monadLift x : n (α × β)) >>= fun p => f p.1) = (monadLift (Prod.fst <$> x) : n α) >>= f :=
  monadLift_bind_map Prod.fst x f


