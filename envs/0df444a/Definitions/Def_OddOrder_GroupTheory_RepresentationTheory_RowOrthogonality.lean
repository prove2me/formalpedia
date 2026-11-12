-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_RowOrthogonality
-- name    : OddOrder_GroupTheory_RepresentationTheory_RowOrthogonality
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:59:07.608908+00:00
-- url     : https://prove2.me/theorems/cf918434-9d71-4102-b84e-7c2847686dab
-- title:
--   Row orthogonality of irreducible characters, as a theorem
-- statement:
--   The second-orthogonality development states the first (row) orthogonality relation `CharacterTableRowOrthogonality` as a `Prop` and uses it as a hypothesis in the column-orthogonality matrix argument. This file discharges that hypothesis: `characterTableRowOrthogonality` is proved outright. The bridge is Mathlib's `Representation.char_orthonormal`, stated with the inverse argument $\sigma.\mathrm{char}(g^{-1})$, translated to Peterfalvi's class-function inner product.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/RowOrthogonality.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/RowOrthogonality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterConjugate
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SecondOrthogonality
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace OddOrder.RepresentationTheory

open scoped BigOperators

variable {G : Type*} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **First (row) orthogonality** of irreducible complex characters, proved as a
theorem rather than assumed.  This discharges the `CharacterTableRowOrthogonality`
hypothesis used by the column-orthogonality matrix argument and, downstream, by
the Peterfalvi §3 (1.4) isometry difference-pair core. -/
theorem characterTableRowOrthogonality :
    CharacterTableRowOrthogonality (G := G) := by
  classical
  refine ⟨fun χ => ?_, fun χ ψ hχψ => ?_⟩
  · -- Diagonal entry `(χ, χ)` equals `1`.
    obtain ⟨V, _, _, _, ρ, hρ, hχ⟩ := χ.isIrreducible
    have : Representation.IsIrreducible ρ := hρ
    have hsum : ∑ g : G, (χ : ClassFunction G ℂ) g * star ((χ : ClassFunction G ℂ) g)
        = ∑ g : G, ρ.character g * ρ.character g⁻¹ :=
      Finset.sum_congr rfl fun g _ => by rw [congrFun hχ g, ← character_inv ρ g]
    rw [characterTableRowPairing_eq_inv_card_sum, hsum, invOf_eq_inv,
      Representation.char_orthonormal ρ ρ, if_pos ⟨Representation.Equiv.refl ρ⟩]
  · -- Off-diagonal entry `(χ, ψ)` with `χ ≠ ψ` equals `0`.
    obtain ⟨Vχ, _, _, _, ρ, hρ, hχ⟩ := χ.isIrreducible
    obtain ⟨Vψ, _, _, _, σ, hσ, hψ⟩ := ψ.isIrreducible
    have : Representation.IsIrreducible ρ := hρ
    have : Representation.IsIrreducible σ := hσ
    have hsum : ∑ g : G, (χ : ClassFunction G ℂ) g * star ((ψ : ClassFunction G ℂ) g)
        = ∑ g : G, ρ.character g * σ.character g⁻¹ :=
      Finset.sum_congr rfl fun g _ => by
        rw [congrFun hχ g, congrFun hψ g, ← character_inv σ g]
    -- An equivalence `σ ≃ ρ` would make the two irreducible characters equal.
    have hnc : ¬ Nonempty (σ.Equiv ρ) := by
      rintro ⟨φ⟩
      apply hχψ
      apply IrreducibleCharacter.ext
      apply ClassFunction.ext
      intro g
      rw [congrFun hχ g, congrFun hψ g]
      exact (congrFun (Representation.char_iso φ) g).symm
    rw [characterTableRowPairing_eq_inv_card_sum, hsum, invOf_eq_inv,
      Representation.char_orthonormal ρ σ, if_neg hnc]

end OddOrder.RepresentationTheory


