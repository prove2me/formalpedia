-- Prove2me | Definitions.Def_Yukon_93a3fe646386238f28bc7a09
-- name    : Yukon_93a3fe646386238f28bc7a09
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T14:37:42.465662+00:00
-- url     : https://prove2.me/theorems/3d00651f-690b-40e1-9368-28b3a63dde72
-- title:
--   YukonModule.ArkLib.ToMathlib.Set.Finite.part0
-- statement:
--   Source module ArkLib.ToMathlib.Set.Finite.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/ToMathlib/Set/Finite.lean
--
--   provider-v8:2d0c30712e9f1b9a0e25e850a42cb296fb8dddee48bb290512aa19d39e7109dd
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJwcm92aWRlci12ODoyZDBjMzA3MTJlOWYxYjlhMGUyNWU4NTBhNDJjYjI5NmZiOGRkZGVlNDhiYjI5MDUxMmFhMTlkMzllNzEwOWRkIiwiaGFzaCI6IjA0MzkwMjU5NDQyODJmMTlkOWI3ZDdkNTJiYWQ3ODUzNmNiYjM2MzVjMzBlNmQ3OTZjOWRiNzNlYjI5MDQwZGUiLCJraW5kIjoiZGVmaW5pdGlvbiIsInRhcmdldCI6Ill1a29uXzkzYTNmZTY0NjM4NjIzOGYyOGJjN2EwOSIsImVudmlyb25tZW50Ijp7Im1hdGhsaWJSZXYiOiIwZGY0NDRhMzYwZWFhNjBhYjhjMTFkY2E1MWE4NmFmNjkyOTU1NDc0IiwidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIn0sInRhZyI6ImJldHRlci1jb2RlcyJ9]

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Alexander Hicks
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.Order.Floor.Semiring


import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
# Finiteness of a set from a uniform bound on its finite subsets

Mathlib has `Set.Infinite.exists_subset_card_eq`, that an infinite set has finite subsets of every
cardinality. This file records the consequence in the direction a counting argument uses it, where
finiteness is the conclusion rather than a hypothesis.
-/

/-- A set whose finite subsets are uniformly bounded is finite.

The bound lives in an arbitrary `FloorSemiring`, so this applies both to a natural bound and to the
real bounds that counting arguments produce. No nonnegativity hypothesis is needed: at a negative
bound the hypothesis at `T = ∅` is already unsatisfiable. -/
theorem Set.finite_of_forall_finset_card_le {α : Type*} {S : Set α} {R : Type*}
    [Semiring R] [LinearOrder R] [FloorSemiring R] {ℓ : R}
    (h : ∀ T : Finset α, (T : Set α) ⊆ S → (T.card : R) ≤ ℓ) : S.Finite := by
  by_contra hinf
  obtain ⟨T, hTS, hTcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊ℓ⌋₊ + 1)
  have hle : ((⌊ℓ⌋₊ + 1 : ℕ) : R) ≤ ℓ := by rw [← hTcard]; exact h T hTS
  have := Nat.le_floor hle
  omega


