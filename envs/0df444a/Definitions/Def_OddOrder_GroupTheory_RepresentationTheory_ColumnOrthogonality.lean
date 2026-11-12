-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
-- name    : OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:06:14.298704+00:00
-- url     : https://prove2.me/theorems/f2d7a0a3-ed1b-46f1-b015-18715e195e57
-- title:
--   Second (column) orthogonality of irreducible characters, unconditional form
-- statement:
--   Supplies the hypothesis-free public form of the second (column) orthogonality relation (Isaacs Thm 2.18 / Thm 6.10) for a finite group $G$. The matrix proof core states the column relations relative to two inputs that were still hypotheses at that stage: a square indexing package for the character table, and row orthogonality; both are now discharged.
--
--   Declarations: the canonical `Fintype` structure on the irreducible characters of a finite group, and `char_one_mul_star_eq_sq` (the summand $\chi(g)\,\overline{\chi(g)}$ of the diagonal column relation equals $|\chi(g)|^2$).
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ColumnOrthogonality.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/ColumnOrthogonality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterCompleteness
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterRowOrthogonality
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ZIrrFourier

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Finite G]

/-- The canonical `Fintype` on `IrreducibleCharacter G` for a finite group, used as the
summation index of the public column-orthogonality theorems below. -/
noncomputable instance : Fintype (IrreducibleCharacter G) :=
  letI := finite_irreducibleCharacter (G := G)
  Fintype.ofFinite _

/-- The class-weighted first orthogonality input for the matrix proof core, discharged
unconditionally for a finite group from `characterTableRowOrthogonality_holds`. -/
private theorem weightedRowOrthogonality_ofFinite :
    CharacterTableWeightedRowOrthogonality (instCharacterTableIndexingOfFinite (G := G)) := by
  have : Fintype G := Fintype.ofFinite G
  have : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact CharacterTableWeightedRowOrthogonality.ofRowOrthogonality
    (instCharacterTableIndexingOfFinite (G := G)) (characterTableRowOrthogonality_holds (G := G))

/-- Bridge between the ambient `Fintype (IrreducibleCharacter G)` summation index and the one
carried by `instCharacterTableIndexingOfFinite`: `Fintype` is a subsingleton, so the two index
finsets coincide and any sum over `IrreducibleCharacter G` is unchanged. -/
private theorem sum_irreducibleCharacter_idx_eq {M : Type*} [AddCommMonoid M]
    (f : IrreducibleCharacter G → M) :
    (letI := (instCharacterTableIndexingOfFinite (G := G)).irrFintype
      ∑ χ : IrreducibleCharacter G, f χ) = ∑ χ : IrreducibleCharacter G, f χ :=
  congrArg (∑ χ ∈ ·, f χ)
    (congrArg (@Finset.univ (IrreducibleCharacter G))
      (Subsingleton.elim (instCharacterTableIndexingOfFinite (G := G)).irrFintype _))

/-- **Second (column) orthogonality**, diagonal case ([Isaacs] Thm 2.18 / Thm 6.10).

For a finite group `G` and `g : G`, the squared column norm equals the centralizer order:
`∑_{χ ∈ Irr G} χ(g) · star (χ(g)) = |C_G(g)|` in `ℂ`. -/
theorem column_orthogonality_diagonal (g : G) :
    ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) g) =
      (Nat.card (Subgroup.centralizer ({g} : Set G)) : ℂ) := by
  rw [← sum_irreducibleCharacter_idx_eq]
  exact column_orthogonality_diag (instCharacterTableIndexingOfFinite (G := G))
    weightedRowOrthogonality_ofFinite g

/-- **Second (column) orthogonality**, non-conjugate case ([Isaacs] Thm 2.18 / Thm 6.10).

For a finite group `G` and non-conjugate elements `g ≁ h`,
`∑_{χ ∈ Irr G} χ(g) · star (χ(h)) = 0` in `ℂ`. -/
theorem column_orthogonality_not_conjugate {g h : G} (hgh : ¬ IsConj g h) :
    ∑ χ : IrreducibleCharacter G,
        ((χ : ClassFunction G ℂ) g) * star ((χ : ClassFunction G ℂ) h) = 0 := by
  rw [← sum_irreducibleCharacter_idx_eq]
  exact column_orthogonality_not_conj (instCharacterTableIndexingOfFinite (G := G))
    weightedRowOrthogonality_ofFinite hgh

omit [Finite G] in
/-- The summand `χ(g) · star (χ(g))` of the diagonal column relation equals `χ(g)²`
whenever `χ(g)` is a real natural number cast, in particular at `g = 1` where
`χ(1)` is the (positive integer) degree of `χ`. -/
private theorem char_one_mul_star_eq_sq (χ : IrreducibleCharacter G) :
    ((χ : ClassFunction G ℂ) 1) * star ((χ : ClassFunction G ℂ) 1) =
      ((χ : ClassFunction G ℂ) 1) ^ 2 := by
  obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  rw [hd, star_natCast, sq]

/-- **Burnside degree-sum identity** (Peterfalvi (1.5.d); the diagonal column relation
[Isaacs] Thm 2.18 at `g = 1`).

The sum of the squares of the degrees of all irreducible characters of a finite group `G`
equals the group order: `∑_{χ ∈ Irr G} χ(1)² = |G|` in `ℂ`. -/
theorem sumIrreducibleDegreeSq :
    ∑ χ : IrreducibleCharacter G, ((χ : ClassFunction G ℂ) 1) ^ 2 = (Nat.card G : ℂ) := by
  have hcentralizer : (Subgroup.centralizer ({(1 : G)} : Set G)) = ⊤ :=
    Subgroup.centralizer_eq_top_iff_subset.mpr
      (Set.singleton_subset_iff.mpr (Subgroup.one_mem _))
  have h := column_orthogonality_diagonal (1 : G)
  rw [Finset.sum_congr rfl (fun χ _ => char_one_mul_star_eq_sq χ)] at h
  rw [h, hcentralizer, Subgroup.card_top]

end OddOrder.RepresentationTheory


