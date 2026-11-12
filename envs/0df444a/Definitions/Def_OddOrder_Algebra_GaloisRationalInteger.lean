-- Prove2me | Definitions.Def_OddOrder_Algebra_GaloisRationalInteger
-- name    : OddOrder_Algebra_GaloisRationalInteger
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:04:35.491504+00:00
-- url     : https://prove2.me/theorems/39d9c2d4-ff1b-4ae5-a52d-e1f306c1b5fa
-- title:
--   Algebraic integers fixed by all Galois automorphisms are rational integers
-- statement:
--   The arithmetic core of Isaacs, Lemma 3.14 (and Peterfalvi (13.9.b)): a nonzero algebraic integer whose Galois conjugates are all accounted for has a field norm that is a nonzero rational integer, hence of absolute value at least $1$. The file isolates the reusable number-theoretic facts: an algebraic integer $\alpha\in\mathbb{C}$ fixed by every ring automorphism of $\mathbb{C}$ is a rational integer, and every ring automorphism of $\mathbb{C}$ acts as a power map on roots of unity.
--
--   The one declaration is `apply_inv_eq_star_of_mem_ZIrr` (virtual characters satisfy $\varphi(g^{-1})=\overline{\varphi(g)}$); the rest are lemmas.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Algebra/GaloisRationalInteger.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Algebra/GaloisRationalInteger.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclotomicGaloisAction
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ClassSumAlgebra
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterConjugate
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCompleteness
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

namespace OddOrder.Algebra

open Polynomial IntermediateField

/-- A rational algebraic integer is a rational integer: if `α : ℂ` is integral over `ℤ` and lies in
the image of `ℚ`, then `α` is the image of an integer. -/
theorem exists_int_of_isIntegral_of_mem_range_rat {α : ℂ} (hα : IsIntegral ℤ α)
    (hrat : ∃ q : ℚ, (q : ℂ) = α) : ∃ z : ℤ, (z : ℂ) = α := by
  obtain ⟨q, rfl⟩ := hrat
  -- `q` is integral over `ℤ` (the map `ℚ → ℂ` is injective, so integrality descends).
  have hqℚ : IsIntegral ℤ q := by
    have hinj : Function.Injective (algebraMap ℚ ℂ) := (algebraMap ℚ ℂ).injective
    exact (isIntegral_algebraMap_iff hinj).mp hα
  -- `ℤ` is integrally closed in `ℚ`, so `q ∈ ℤ`.
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff).mp hqℚ
  refine ⟨z, ?_⟩
  rw [← hz]
  simp

open OddOrder.RepresentationTheory in
/-- **Virtual characters satisfy `φ(g⁻¹) = conj (φ(g))`** — the `ℤ[Irr]`-span extension of
`character_inv` (finite-dimensional complex representations have `χ(g⁻¹) = χ̄(g)`). -/
theorem apply_inv_eq_star_of_mem_ZIrr {G : Type*} [Group G] [Finite G]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G) (g : G) :
    φ g⁻¹ = star (φ g) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨V, _, _, _, ρ, hchar⟩ := IsIrreducibleCharacter.isCharacter hx
      rw [show x g = ρ.character g from congrFun hchar g,
        show x g⁻¹ = ρ.character g⁻¹ from congrFun hchar g⁻¹]
      exact character_inv ρ g
  | zero => simp
  | add a b _ _ ha hb =>
      rw [ClassFunction.add_apply, ClassFunction.add_apply, ha, hb, star_add]
  | smul n a _ ha =>
      rw [ClassFunction.zsmul_apply, ClassFunction.zsmul_apply, ha]
      simp

end OddOrder.Algebra


