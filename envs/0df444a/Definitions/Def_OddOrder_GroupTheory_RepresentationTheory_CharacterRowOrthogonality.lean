-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterRowOrthogonality
-- name    : OddOrder_GroupTheory_RepresentationTheory_CharacterRowOrthogonality
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:58:57.298199+00:00
-- url     : https://prove2.me/theorems/a1d16b92-e10c-47d2-a4c9-3cd75486db98
-- title:
--   Row orthogonality of irreducible characters (first orthogonality)
-- statement:
--   Discharges the row-orthogonality hypothesis `CharacterTableRowOrthogonality` used in the second-orthogonality development, turning it into an unconditional theorem for finite groups. The content is Mathlib's orthogonality of characters of irreducible complex representations, bridged to Peterfalvi's class-function inner product $(\alpha,\beta)_G=|G|^{-1}\sum\alpha(g)\overline{\beta(g)}$.
--
--   The main result is `irreducibleCharacter_inner` (first orthogonality: irreducible characters are orthonormal). The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CharacterRowOrthogonality.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CharacterRowOrthogonality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterConjugate
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SecondOrthogonality
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open Classical in
/-- **First orthogonality relation.** Irreducible characters are orthonormal under Peterfalvi's
class-function inner product: `(χ, ψ)_G = if χ = ψ then 1 else 0`.

Bridges mathlib's `Representation.char_orthonormal` (stated with the `g⁻¹` summand) to the
conjugate-summand inner product via `character_inv`. -/
theorem irreducibleCharacter_inner [Fintype G] [Invertible (Nat.card G : ℂ)]
    (χ ψ : IrreducibleCharacter G) :
    ClassFunction.inner (χ : ClassFunction G ℂ) (ψ : ClassFunction G ℂ) =
      if χ = ψ then 1 else 0 := by
  by_cases hχψ : χ = ψ
  · -- Diagonal: extract one irreducible representation and apply `char_orthonormal ρ ρ`.
    subst hχψ
    obtain ⟨V, _, _, _, ρ, hρ, hcoe⟩ := χ.isIrreducible
    have : Representation.IsIrreducible ρ := hρ
    rw [if_pos rfl, ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum,
      invOf_eq_inv]
    have hsum : ∀ g : G,
        (χ : ClassFunction G ℂ) g * star ((χ : ClassFunction G ℂ) g) =
          ρ.character g * ρ.character g⁻¹ := by
      intro g
      rw [congrFun hcoe g, ← character_inv ρ g]
    rw [Finset.sum_congr rfl (fun g _ => hsum g), ρ.char_orthonormal,
      if_pos ⟨Representation.Equiv.refl ρ⟩]
  · -- Off-diagonal: distinct characters ⇒ non-isomorphic representations ⇒ the `0` branch.
    obtain ⟨Vχ, _, _, _, ρχ, hρχ, hcoeχ⟩ := χ.isIrreducible
    obtain ⟨Vψ, _, _, _, ρψ, hρψ, hcoeψ⟩ := ψ.isIrreducible
    have : Representation.IsIrreducible ρχ := hρχ
    have : Representation.IsIrreducible ρψ := hρψ
    rw [if_neg hχψ, ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum,
      invOf_eq_inv]
    have hsum : ∀ g : G,
        (χ : ClassFunction G ℂ) g * star ((ψ : ClassFunction G ℂ) g) =
          ρχ.character g * ρψ.character g⁻¹ := by
      intro g
      rw [congrFun hcoeχ g, congrFun hcoeψ g, ← character_inv ρψ g]
    rw [Finset.sum_congr rfl (fun g _ => hsum g), ρχ.char_orthonormal]
    rw [if_neg]
    rintro ⟨e⟩
    -- An equivalence `ρψ ≃ ρχ` forces equal characters, hence `ψ = χ`.
    apply hχψ
    apply IrreducibleCharacter.ext
    apply ClassFunction.ext
    intro g
    rw [congrFun hcoeχ g, congrFun hcoeψ g, ← congrFun (Representation.char_iso e) g]

/-- **`CharacterTableRowOrthogonality` holds unconditionally.** Discharges the row-orthogonality
input assumed throughout `SecondOrthogonality.lean`, via `irreducibleCharacter_inner`. -/
theorem characterTableRowOrthogonality_holds [Fintype G] [Invertible (Nat.card G : ℂ)] :
    CharacterTableRowOrthogonality (G := G) := by
  refine ⟨fun χ => ?_, fun χ ψ hχψ => ?_⟩
  · rw [characterTableRowPairing_eq_inner, irreducibleCharacter_inner, if_pos rfl]
  · rw [characterTableRowPairing_eq_inner, irreducibleCharacter_inner, if_neg hχψ]

end OddOrder.RepresentationTheory


