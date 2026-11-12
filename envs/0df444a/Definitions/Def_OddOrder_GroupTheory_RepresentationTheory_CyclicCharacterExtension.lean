-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclicCharacterExtension
-- name    : OddOrder_GroupTheory_RepresentationTheory_CyclicCharacterExtension
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:56:59.879178+00:00
-- url     : https://prove2.me/theorems/861971f1-65f1-44d1-954a-ccd19bcf368e
-- title:
--   Extension of an invariant irreducible character along a cyclic quotient
-- statement:
--   Isaacs, *Character Theory of Finite Groups*, Theorem 11.22 (cyclic case, direct construction): let $H\trianglelefteq K$ with $K/H$ cyclic and let $\theta\in\mathrm{Irr}(H)$ be $K$-invariant. Then $\theta$ extends to an irreducible character $\chi\in\mathrm{Irr}(K)$ with $\mathrm{Res}_H\chi=\theta$. This file is the $\mathbb{C}$ / character-level layer of the construction.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CyclicCharacterExtension.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CyclicCharacterExtension.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclicExtension
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ZIrr
import Mathlib.Analysis.Complex.Polynomial.Basic

namespace OddOrder.RepresentationTheory

variable {K : Type*} [Group K] {H : Subgroup K} [hH : H.Normal]

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

section Intertwiner

variable [FiniteDimensional ℂ V]

/-- **Equal characters give an equivalence with the conjugate** (step 1 of Isaacs 11.22).
If the conjugate representation `ρ^g` has the same character as the irreducible `ρ` — i.e.
the character of `ρ` is `g`-invariant — then `ρ ≅ ρ^g` as representations of `H`.  This is
character orthogonality: `⟨χ, χ⟩ = 1 ≠ 0` forces the `if Nonempty (Equiv _ _)` branch.

This is the one step that genuinely needs `|H|` invertible in the field; Bender-Glauberman
Prop 2.2(b) assumes `ρ ≅ ρ^g` outright and so avoids it entirely. -/
theorem nonempty_equiv_conjRep_of_character_eq [Finite ↥H] [Invertible (Nat.card ↥H : ℂ)]
    (ρ : Representation ℂ ↥H V) [Representation.IsIrreducible ρ] (g : K)
    (hinv : (conjRep ρ g).character = ρ.character) :
    Nonempty (ρ.Equiv (conjRep ρ g)) := by
  have : Fintype ↥H := Fintype.ofFinite _
  have := isIrreducible_conjRep ρ g
  have h1 : (Nat.card ↥H : ℂ)⁻¹ * ∑ h : ↥H, ρ.character h * ρ.character h⁻¹ = 1 := by
    rw [Representation.char_orthonormal, if_pos ⟨Representation.Equiv.refl _⟩]
  have key := Representation.char_orthonormal (conjRep ρ g) ρ
  rw [hinv, h1] at key
  by_contra hc
  rw [if_neg hc] at key
  exact one_ne_zero key

end Intertwiner

section Normalization

variable [FiniteDimensional ℂ V]

/-- **The normalized conjugation unit over `ℂ`** (steps 2-3 of Isaacs 11.22), from
`g`-invariance of the *character*.  Over `ℂ` the hypothesis `|H|` invertible is automatic, so
character invariance alone suffices; the construction itself is the characteristic-free
`exists_normalized_conjugation_unit_of_nonempty_equiv`. -/
theorem exists_normalized_conjugation_unit [Finite K]
    (ρ : Representation ℂ ↥H V) [Representation.IsIrreducible ρ] (g : K)
    (hinv : (conjRep ρ g).character = ρ.character) :
    ∃ P : (Module.End ℂ V)ˣ,
      (∀ h : ↥H, P * ρ.asGroupHom h
        = ρ.asGroupHom (ClassFunction.conjByMulEquiv (G := K) (H := H) g h) * P) ∧
      ∀ (t : ℤ) (ht : g ^ t ∈ H), P ^ t = ρ.asGroupHom ⟨g ^ t, ht⟩ := by
  have : Invertible (Nat.card ↥H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact exists_normalized_conjugation_unit_of_nonempty_equiv ρ g
    (nonempty_equiv_conjRep_of_character_eq ρ g hinv)

end Normalization

section CharacterLevel

/-- **Extension along a cyclic quotient — Isaacs, _Character Theory_, Theorem 11.22 (cyclic
case).**  Let `H ⊴ K` with `K` finite and the image of `g : K` generating `K/H`, and let `θ`
be an irreducible character of `H` fixed by `g`-conjugation (equivalently, `K`-invariant,
since `H ≤ I_K(θ)` always).  Then `θ` **extends** to `K`: there is an irreducible character
`χ` of `K` with `Res_H χ = θ`.

This is the (G1) cyclic building block of the constructive Clifford correspondence
(Peterfalvi (1.7)(b) -- the **general**, not-yet-formalized one; the coprime (1.7)(c) does not
need this route); the abelian inertia quotient case follows by iterating along a composition
series.

The representation-level, characteristic-free analogue over any algebraically closed field is
`exists_extension_of_nonempty_equiv_conjRep` (BG Prop 2.2(b)). -/
theorem IsIrreducibleCharacter.exists_extension_of_conjBy_eq [Finite K]
    {θ : ClassFunction ↥H ℂ} (hθ : IsIrreducibleCharacter θ) {g : K}
    (hgen : ∀ k : K, ∃ i : ℤ, (g ^ i)⁻¹ * k ∈ H)
    (hinv : ClassFunction.conjBy g θ = θ) :
    ∃ χ : ClassFunction K ℂ, IsIrreducibleCharacter χ ∧
      ClassFunction.restrict H χ = θ := by
  obtain ⟨V, _, _, _, ρ, hρirr, hchar⟩ := hθ
  have := hρirr
  -- the conjugate representation has the same character, by invariance of `θ`
  have hinv' : (conjRep ρ g).character = ρ.character := by
    funext h
    rw [conjRep_character,
      ← congrFun hchar (ClassFunction.conjByMulEquiv (G := K) (H := H) g h),
      ← congrFun hchar h]
    exact congrFun (congrArg (fun f : ClassFunction ↥H ℂ => (f : ↥H → ℂ)) hinv) h
  obtain ⟨P, hP, hPt⟩ := exists_normalized_conjugation_unit ρ g hinv'
  refine ⟨repCharacterClassFunction (cyclicExtension ρ g P hP hPt hgen),
    ⟨V, inferInstance, inferInstance, inferInstance, cyclicExtension ρ g P hP hPt hgen,
      isIrreducible_cyclicExtension hP hPt hgen, rfl⟩, ?_⟩
  ext h
  rw [ClassFunction.restrict_apply]
  have h3 : cyclicExtension ρ g P hP hPt hgen ((h : K)) = ρ h :=
    DFunLike.congr_fun (cyclicExtension_comp_subtype hP hPt hgen) h
  have h4 : (cyclicExtension ρ g P hP hPt hgen).character (h : K) = ρ.character h :=
    congrArg (LinearMap.trace ℂ V) h3
  change (cyclicExtension ρ g P hP hPt hgen).character (h : K) = _
  rw [h4, ← congrFun hchar h]

end CharacterLevel

end OddOrder.RepresentationTheory


