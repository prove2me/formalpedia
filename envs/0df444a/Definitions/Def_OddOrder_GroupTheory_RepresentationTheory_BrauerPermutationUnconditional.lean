-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
-- name    : OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:07:54.386312+00:00
-- url     : https://prove2.me/theorems/6888a6c7-4456-4e8d-8e43-0ee0562b372f
-- title:
--   Brauer's permutation lemma, unconditional form
-- statement:
--   Discharges the explicit hypotheses of `brauer_permutation_lemma` for an arbitrary finite group, giving the hypothesis-free statement $\#\{\chi\in\mathrm{Irr}\,G:\bar\chi=\chi\}=\#\{C:C^{-1}=C\}$ (Isaacs, *Character Theory of Finite Groups*, Thm 6.32). Two ingredients are supplied: the square character-table indexing with weighted row orthogonality, now unconditional for finite groups, and the complex-conjugation involution on irreducible characters.
--
--   Main definitions: `Subrepresentation.dualAnnihilator` and `Subrepresentation.dualCoann` (dual annihilator and coannihilator of subrepresentations), `Subrepresentation.dualOrderIso` (the antitone order isomorphism between subrepresentations of $\rho^*$ and of $\rho$) and `IrreducibleCharacter.conjPerm` (the conjugation involution on $\mathrm{Irr}\,G$).
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/BrauerPermutationUnconditional.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/BrauerPermutationUnconditional.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutation
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterConjugate
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCompleteness
import Mathlib.LinearAlgebra.Dual.Lemmas

namespace Representation

open scoped MonoidAlgebra

section Dual

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- The dual-annihilator of a subrepresentation of `ρ`, as a subrepresentation of `ρ.dual`.

If `S` is `ρ`-stable, then its annihilator `S° = {f : V* | f|_S = 0}` is `ρ.dual`-stable, because
`(ρ.dual g f) w = f (ρ g⁻¹ w)` and `ρ g⁻¹ w ∈ S` whenever `w ∈ S`. -/
def Subrepresentation.dualAnnihilator (S : Subrepresentation ρ) : Subrepresentation ρ.dual where
  toSubmodule := S.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule g f hf := by
    rw [Submodule.mem_dualAnnihilator] at hf ⊢
    intro w hw
    -- `(ρ.dual g) f = (ρ g⁻¹).transpose`, so `(ρ.dual g f) w = f (ρ g⁻¹ w)`.
    rw [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
    exact hf _ (S.apply_mem_toSubmodule g⁻¹ hw)

/-- The dual-coannihilator of a subrepresentation of `ρ.dual`, as a subrepresentation of `ρ`.

If `S` is `ρ.dual`-stable, then `S^∘ = {w : V | f w = 0 for all f ∈ S}` is `ρ`-stable: for
`φ ∈ S` we have `ρ.dual g⁻¹ φ ∈ S` and `(ρ.dual g⁻¹ φ) w = φ (ρ g w)`, which vanishes for
`w ∈ S^∘`. -/
def Subrepresentation.dualCoann (S : Subrepresentation ρ.dual) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule g w hw := by
    rw [Submodule.mem_dualCoannihilator] at hw ⊢
    intro φ hφ
    have hφ' : ρ.dual g⁻¹ φ ∈ S.toSubmodule := S.apply_mem_toSubmodule g⁻¹ hφ
    have := hw _ hφ'
    rwa [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, inv_inv] at this

variable [FiniteDimensional k V]

/-- The antitone order isomorphism between subrepresentations of `ρ.dual` and (the order dual of)
subrepresentations of `ρ`, given by `dualCoannihilator`/`dualAnnihilator`.

This is the `G`-stable analogue of `Subspace.orderIsoFiniteDimensional` (same `dualAnnihilator` /
`dualCoannihilator` round-trips).  Combined with `OrderIso.isSimpleOrder_iff`, it transports
irreducibility of `ρ` to `ρ.dual`. -/
def Subrepresentation.dualOrderIso :
    Subrepresentation ρ.dual ≃o (Subrepresentation ρ)ᵒᵈ where
  toFun S := OrderDual.toDual (Subrepresentation.dualCoann ρ S)
  invFun S := Subrepresentation.dualAnnihilator ρ (OrderDual.ofDual S)
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    have : FiniteDimensional k S.toSubmodule := inferInstance
    exact Subspace.dualCoannihilator_dualAnnihilator_eq
  right_inv S := by
    apply OrderDual.toDual.injective
    apply Subrepresentation.toSubmodule_injective
    exact Subspace.dualAnnihilator_dualCoannihilator_eq
  map_rel_iff' {S T} := by
    have : FiniteDimensional k S.toSubmodule := inferInstance
    have : FiniteDimensional k T.toSubmodule := inferInstance
    change T.toSubmodule.dualCoannihilator ≤ S.toSubmodule.dualCoannihilator ↔
      S.toSubmodule ≤ T.toSubmodule
    rw [← Subspace.dualAnnihilator_le_dualAnnihilator_iff (W := S.toSubmodule.dualCoannihilator)
      (W' := T.toSubmodule.dualCoannihilator),
      Subspace.dualCoannihilator_dualAnnihilator_eq,
      Subspace.dualCoannihilator_dualAnnihilator_eq]

/-- **The dual of a finite-dimensional irreducible representation is irreducible.**

Subrepresentations of `ρ.dual` are in antitone bijection with subrepresentations of `ρ` (via
annihilators), so `ρ.dual` is simple iff `ρ` is. -/
theorem IsIrreducible.dual [IsIrreducible ρ] : IsIrreducible ρ.dual :=
  (Subrepresentation.dualOrderIso ρ).isSimpleOrder_iff.mpr OrderDual.instIsSimpleOrder

end Dual

end Representation

namespace OddOrder.RepresentationTheory

open Module (finrank)

variable {G : Type*} [Group G]

/-- **The complex conjugate of an irreducible character is irreducible.**

If `φ = χ_ρ` for an irreducible representation `ρ`, then `φ̄(g) = star(χ_ρ(g)) = χ_ρ(g⁻¹) =
χ_{ρ*}(g)`, so `φ̄` is the character of the dual representation `ρ*`, which is irreducible by
`Representation.IsIrreducible.dual`. -/
theorem IsIrreducibleCharacter.conj [Finite G] {φ : ClassFunction G ℂ}
    (hφ : IsIrreducibleCharacter φ) : IsIrreducibleCharacter φ.conj := by
  obtain ⟨V, _, _, _, ρ, hρ, hχ⟩ := hφ
  have : Representation.IsIrreducible ρ := hρ
  refine ⟨Module.Dual ℂ V, inferInstance, inferInstance, inferInstance, ρ.dual,
    Representation.IsIrreducible.dual ρ, ?_⟩
  funext g
  -- `φ.conj g = star (φ g) = star (ρ.character g) = ρ.character g⁻¹ = ρ.dual.character g`.
  rw [ClassFunction.conj_apply, congrFun hχ g, ← character_inv ρ g, Representation.char_dual]

variable (G)

/-- The complex-conjugation involution `χ ↦ χ̄` on the irreducible characters of `G`.

Well-defined because the conjugate of an irreducible character is irreducible
(`IsIrreducibleCharacter.conj`); involutive because `ClassFunction.conj` is. -/
noncomputable def IrreducibleCharacter.conjPerm [Finite G] :
    Equiv.Perm (IrreducibleCharacter G) where
  toFun χ := ⟨(χ : ClassFunction G ℂ).conj, χ.isIrreducible.conj⟩
  invFun χ := ⟨(χ : ClassFunction G ℂ).conj, χ.isIrreducible.conj⟩
  left_inv χ := IrreducibleCharacter.ext (by simp)
  right_inv χ := IrreducibleCharacter.ext (by simp)

variable {G}

@[simp] theorem IrreducibleCharacter.conjPerm_apply_coe [Finite G] (χ : IrreducibleCharacter G) :
    ((IrreducibleCharacter.conjPerm G χ : IrreducibleCharacter G) : ClassFunction G ℂ) =
      (χ : ClassFunction G ℂ).conj :=
  rfl

/-- A fixed point of the conjugation involution is exactly a real irreducible character. -/
theorem IrreducibleCharacter.conjPerm_eq_self_iff [Finite G] (χ : IrreducibleCharacter G) :
    IrreducibleCharacter.conjPerm G χ = χ ↔ ClassFunction.IsReal (χ : ClassFunction G ℂ) := by
  rw [ClassFunction.IsReal, IrreducibleCharacter.ext_iff, IrreducibleCharacter.conjPerm_apply_coe]

/-- Compatibility of the conjugation involution with class inversion at the level of
character-table entries: `χ̄(C) = χ(C⁻¹)`.

Concretely `χ̄(rep C) = star (χ (rep C)) = χ ((rep C)⁻¹)`, the last step being
`character_inv` for the representation underlying `χ`. -/
theorem conjPerm_compat [Finite G] (χ : IrreducibleCharacter G) (C : ConjClasses G) :
    characterTableEntry (IrreducibleCharacter.conjPerm G χ) C =
      characterTableEntry χ (ConjClasses.inv C) := by
  -- Recover a representation `ρ` underlying `χ` to apply `character_inv`.
  obtain ⟨V, _, _, _, ρ, _, hχ⟩ := χ.isIrreducible
  induction C using Quotient.inductionOn with
  | _ g =>
    have hinv : ConjClasses.inv (ConjClasses.mk g) = ConjClasses.mk g⁻¹ := ConjClasses.inv_mk g
    change characterTableEntry (IrreducibleCharacter.conjPerm G χ) (ConjClasses.mk g) =
      characterTableEntry χ (ConjClasses.inv (ConjClasses.mk g))
    rw [hinv, characterTableEntry_mk, characterTableEntry_mk,
      IrreducibleCharacter.conjPerm_apply_coe, ClassFunction.conj_apply,
      congrFun hχ g, congrFun hχ g⁻¹, character_inv ρ g]

variable [Finite G]

/-- **Brauer's permutation lemma** (Isaacs, *Character Theory of Finite Groups*, Thm 6.32),
unconditional form.

For a finite group `G`, the number of real irreducible complex characters equals the number of
self-inverse (real) conjugacy classes. -/
theorem brauer_permutation_lemma' :
    Nat.card (RealIrreducibleCharacter G) = Nat.card (ConjClasses.RealClass G) := by
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact brauer_permutation_lemma (instCharacterTableIndexingOfFinite (G := G))
    (CharacterTableWeightedRowOrthogonality.ofRowOrthogonality
      (instCharacterTableIndexingOfFinite (G := G)) (characterTableRowOrthogonality_holds (G := G)))
    (IrreducibleCharacter.conjPerm G)
    IrreducibleCharacter.conjPerm_eq_self_iff
    conjPerm_compat

/-- Odd-order specialization of Brauer's permutation lemma, unconditional form.

In a finite group of odd order, there is exactly one real irreducible character (the trivial one).
This is the cardinal form of Peterfalvi §3 (1.1). -/
theorem card_realIrreducibleCharacters_eq_one_of_odd_card' (hodd : Odd (Nat.card G)) :
    Nat.card (RealIrreducibleCharacter G) = 1 := by
  rw [brauer_permutation_lemma', ConjClasses.card_realClasses_eq_one_of_odd_card hodd]

/-- In a finite group of odd order, every real irreducible character is the trivial
irreducible character.  Unconditional form (no character-table hypotheses). -/
theorem realIrreducibleCharacter_eq_trivial_of_odd_card' (hodd : Odd (Nat.card G))
    (χ : RealIrreducibleCharacter G) :
    (χ : IrreducibleCharacter G) = trivialIrreducibleCharacter G := by
  obtain ⟨η, hη⟩ :=
    Nat.card_eq_one_iff_exists.mp (card_realIrreducibleCharacters_eq_one_of_odd_card' hodd)
  have hχ : χ = η := hη χ
  have htriv : trivialRealIrreducibleCharacter G = η := hη (trivialRealIrreducibleCharacter G)
  exact congrArg (fun ξ : RealIrreducibleCharacter G => (ξ : IrreducibleCharacter G))
    (hχ.trans htriv.symm)

/-- **Peterfalvi (1.1)**, pointwise unconditional form.

In a finite group of odd order, a nontrivial irreducible complex character is not real
(its complex conjugate `χ̄` differs from `χ`).  This is the parity core of the odd-order
character theory: the only self-conjugate irreducible character is the trivial one. -/
theorem not_isReal_of_ne_trivial_of_odd_card' (hodd : Odd (Nat.card G))
    {χ : IrreducibleCharacter G} (hχ : χ ≠ trivialIrreducibleCharacter G) :
    ¬ ClassFunction.IsReal (χ : ClassFunction G ℂ) := by
  intro hreal
  exact hχ (realIrreducibleCharacter_eq_trivial_of_odd_card' hodd ⟨χ, hreal⟩)

end OddOrder.RepresentationTheory


