-- Prove2me | Definitions.Def_Yukon_91af1749a6c283192774fa4d
-- name    : Yukon_91af1749a6c283192774fa4d
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:37:46.641239+00:00
-- url     : https://prove2.me/theorems/e1ff8928-10fb-4731-93a4-936aa3b8d3c6
-- title:
--   YukonModule.ToMathlib.Data.FinEnum.part0
-- statement:
--   Source module ToMathlib.Data.FinEnum.
-- source:
--   https://github.com/Verified-zkEVM/VCV-io/blob/446baa72bb7d4296d6f6b7015fd6c15ca9c678b7/ToMathlib/Data/FinEnum.lean
--
--   provider-v8:eab67a7ef63d2640c9e0e9ccbc43b9cb8d6400468b787f260456043739446643
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODplYWI2N2E3ZWY2M2QyNjQwYzllMGU5Y2NiYzQzYjljYjhkNjQwMDQ2OGI3ODdmMjYwNDU2MDQzNzM5NDQ2NjQzIiwiaGFzaCI6IjA5ZTdiNjk3ODk0OWEzY2Q1MjU2M2Y1ODdiOWNkNzlkY2I4ZDEwNWI0ZWZlY2U3MDI4ZTIyZjk0NzAzMWMzMGUiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uXzkxYWYxNzQ5YTZjMjgzMTkyNzc0ZmE0ZCIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.List.Sym
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Data.Fintype.Pi


public import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# Computable `FinEnum` constructions for `Bool`, `Sym`, `Equiv.Perm`, and embeddings

`FinEnum α` packages a finite type with a *canonical computable enumeration* (an exhaustive
duplicate-free list, hence `DecidableEq` and `Fintype`). `Mathlib` provides `FinEnum` for the
basic shape-formers (`Fin`, products, sums, `Finset`, subtypes, pi types, …) but not for `Bool`
nor for the combinatorial type-formers `Sym`, `Equiv.Perm`, and function embeddings — even though
each has a `Fintype` instance and an underlying list enumerator. This file fills those gaps.

* `FinEnum Bool` is a small base instance.
* `Sym.finEnum`, `Equiv.Perm.finEnum`, and `Function.Embedding.finEnum` are provided as plain
  `def`s (not instances) on purpose: a global `FinEnum` instance for any of these would, through
  the `priority 100` `FinEnum → Fintype` instance, synthesize a second `Fintype` competing with
  `Mathlib`'s native one and not definitionally equal to it. Callers that want the enumeration
  introduce it locally with `letI` so no competing `Fintype` ever enters global resolution.

Each construction reuses an existing computable enumerator: `List.sym` for `Sym`, `permsOfList`
for `Equiv.Perm`, and the equivalence with the injective-function subtype for embeddings (the
latter is genuinely computable, unlike `Mathlib`'s noncomputable `Function.Embedding.fintype`).
`List.mem_sym` supplies the completeness half that `Mathlib` is missing for `List.sym`.
-/

@[expose] public section

universe u

/-- Completeness of `List.sym`: every `z : Sym α n` whose members all lie in `xs` is enumerated by
`xs.sym n`. This is the converse of `List.mem_of_mem_of_mem_sym`. -/
theorem List.mem_sym {α : Type u} :
    ∀ {n : ℕ} {xs : List α} {z : Sym α n}, (∀ a ∈ z, a ∈ xs) → z ∈ xs.sym n
  | 0, _, z, _ => by rw [Sym.eq_nil_of_card_zero z]; simp [List.sym]
  | n + 1, [], z, h => by
      obtain ⟨a, z', rfl⟩ := z.exists_eq_cons_of_succ
      exact absurd (h a (Sym.mem_cons_self a z')) (by simp)
  | n + 1, x :: xs, z, h => by
      classical
      rw [List.sym, List.mem_append]
      by_cases hx : x ∈ z
      · refine Or.inl (List.mem_map.mpr ⟨z.erase x hx, ?_, Sym.cons_erase hx⟩)
        exact List.mem_sym fun a ha =>
          h a (by rw [← Sym.cons_erase hx]; exact Sym.mem_cons.mpr (Or.inr ha))
      · refine Or.inr (List.mem_sym fun a ha => ?_)
        rcases List.mem_cons.mp (h a ha) with rfl | ha'
        · exact absurd ha hx
        · exact ha'

/-- `Bool` enumerated as `[true, false]`. -/
instance  _root_.instFinEnumBool_toMathlib : FinEnum Bool := .ofList [true, false] (by decide)

/-- Computable enumeration of size-`n` multisets over a `FinEnum` type, drawn from `List.sym` of
the canonical enumeration. Every `z : Sym α n` qualifies since all its members lie in
`FinEnum.toList`. -/
@[reducible] def Sym.finEnum {α : Type u} [FinEnum α] (n : ℕ) : FinEnum (Sym α n) :=
  FinEnum.ofNodupList ((FinEnum.toList α).sym n)
    (fun _ => List.mem_sym fun a _ => FinEnum.mem_toList a)
    (List.Nodup.sym n FinEnum.nodup_toList)

/-- Computable enumeration of permutations of a `FinEnum` type via `permsOfList` applied to the
canonical enumeration. Completeness holds because every element a permutation can move lies in
`FinEnum.toList`. -/
@[reducible] def Equiv.Perm.finEnum {α : Type u} [FinEnum α] : FinEnum (Equiv.Perm α) :=
  FinEnum.ofNodupList (permsOfList (FinEnum.toList α))
    (fun _ => mem_permsOfList_of_mem fun x _ => FinEnum.mem_toList x)
    (nodup_permsOfList FinEnum.nodup_toList)

/-- Computable enumeration of embeddings `β ↪ α` between `FinEnum` types, transported from the
`FinEnum` on the subtype of injective functions `{f : β → α // Function.Injective f}`. Injectivity
is decidable for functions out of a finite domain, so this subtype is itself `FinEnum`. -/
@[reducible] def Function.Embedding.finEnum {β α : Type u} [FinEnum β] [FinEnum α] :
    FinEnum (β ↪ α) :=
  FinEnum.ofEquiv { f : β → α // Function.Injective f }
    (Equiv.subtypeInjectiveEquivEmbedding β α).symm


