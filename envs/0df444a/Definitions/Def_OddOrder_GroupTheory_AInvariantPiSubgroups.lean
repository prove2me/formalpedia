-- Prove2me | Definitions.Def_OddOrder_GroupTheory_AInvariantPiSubgroups
-- name    : OddOrder_GroupTheory_AInvariantPiSubgroups
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:51:57.008646+00:00
-- url     : https://prove2.me/theorems/4a4bd082-c523-4e2b-9ed0-2c5d7b8960be
-- title:
--   $A$-invariant $\pi$-subgroup families $\mathcal{H}_H(A;\pi)$ and $\mathcal{H}^*_H(A;\pi)$
-- statement:
--   A shared module for the Bender–Glauberman families of $A$-invariant $\pi$-subgroups of a subgroup $H$ and their maximal members, introduced in BG §7 (Hypothesis 7.1). They carry the whole Transitivity Theorem machinery and recur through §8–§16.
--
--   Main definitions: `hInvariant` (BG $\mathcal{H}_H(A;\pi)$: the $A$-invariant $\pi$-subgroups $Q\le H$) and `hInvariantStar` ($\mathcal{H}^*_H(A;\pi)$: the members maximal under inclusion), with lemmas relating normalizers to the conjugation action fixing a subgroup.
--
--   The bundle also proves 13 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/AInvariantPiSubgroups.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/AInvariantPiSubgroups.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_OpResidual
import Mathlib.Algebra.Group.Subgroup.Pointwise

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **BG `ℋ_H(A;π)`** (§7): the set of subgroups `Q ≤ H` that are `π`-subgroups and are
normalized by `A` (i.e. `A ⊆ N_G(Q)`). -/
def hInvariant (H A : Subgroup G) (π : Set ℕ) : Set (Subgroup G) :=
  {Q | Q ≤ H ∧ A ≤ Subgroup.normalizer Q ∧ Subgroup.IsPiSubgroup π Q}

/-- **BG `ℋ_H*(A;π)`** (§7): the members of `ℋ_H(A;π)` maximal under inclusion within the
family `ℋ_H(A;π)`. The Transitivity Theorem (§7) studies the `O_{π'}(C_G(A))`-action on this
set. The single-prime form `ℋ_H*(A;q)` is `hInvariantStar H A {q}`. -/
def hInvariantStar (H A : Subgroup G) (π : Set ℕ) : Set (Subgroup G) :=
  {Q | Q ∈ hInvariant H A π ∧ ∀ Q' ∈ hInvariant H A π, Q ≤ Q' → Q' = Q}

@[simp]
theorem mem_hInvariant {H A : Subgroup G} {π : Set ℕ} {Q : Subgroup G} :
    Q ∈ hInvariant H A π ↔
      Q ≤ H ∧ A ≤ Subgroup.normalizer Q ∧ Subgroup.IsPiSubgroup π Q :=
  Iff.rfl

@[simp]
theorem mem_hInvariantStar {H A : Subgroup G} {π : Set ℕ} {Q : Subgroup G} :
    Q ∈ hInvariantStar H A π ↔
      Q ∈ hInvariant H A π ∧ ∀ Q' ∈ hInvariant H A π, Q ≤ Q' → Q' = Q :=
  Iff.rfl

/-- A member of `ℋ_H(A;π)` is normalized by `A`. -/
theorem hInvariant_le_normalizer {H A : Subgroup G} {π : Set ℕ} {Q : Subgroup G}
    (hQ : Q ∈ hInvariant H A π) :
    A ≤ Subgroup.normalizer Q :=
  hQ.2.1

/-- A member of `ℋ_H(A;π)` is a `π`-subgroup. -/
theorem hInvariant_isPiSubgroup {H A : Subgroup G} {π : Set ℕ} {Q : Subgroup G}
    (hQ : Q ∈ hInvariant H A π) :
    Subgroup.IsPiSubgroup π Q :=
  hQ.2.2

/-- A member of `ℋ_H*(A;π)` is in `ℋ_H(A;π)`. -/
theorem hInvariantStar_mem_hInvariant {H A : Subgroup G} {π : Set ℕ} {Q : Subgroup G}
    (hQ : Q ∈ hInvariantStar H A π) :
    Q ∈ hInvariant H A π :=
  hQ.1

/-- A member of `ℋ_H*(A;π)` is normalized by `A`. -/
theorem hInvariantStar_le_normalizer {H A : Subgroup G} {π : Set ℕ} {Q : Subgroup G}
    (hQ : Q ∈ hInvariantStar H A π) :
    A ≤ Subgroup.normalizer Q :=
  hQ.1.2.1

/-- A member of `ℋ_H*(A;π)` is a `π`-subgroup. -/
theorem hInvariantStar_isPiSubgroup {H A : Subgroup G} {π : Set ℕ} {Q : Subgroup G}
    (hQ : Q ∈ hInvariantStar H A π) :
    Subgroup.IsPiSubgroup π Q :=
  hQ.1.2.2

/-- Maximality inside `ℋ_H(A;π)` for a member of `ℋ_H*(A;π)`. -/
theorem hInvariantStar_eq_of_le {H A : Subgroup G} {π : Set ℕ} {Q Q' : Subgroup G}
    (hQ : Q ∈ hInvariantStar H A π) (hQ' : Q' ∈ hInvariant H A π) (hQQ' : Q ≤ Q') :
    Q' = Q :=
  hQ.2 Q' hQ' hQQ'

open scoped Pointwise

set_option backward.isDefEq.respectTransparency false in
/-- Conjugation by an element of the normalizer fixes the subgroup (pointwise-`smul` form). -/
theorem conj_smul_eq_self_of_mem_normalizer {Q : Subgroup G} {a : G}
    (ha : a ∈ Subgroup.normalizer Q) : MulAut.conj a • Q = Q := by
  have hnorm := Subgroup.mem_normalizer_iff.mp ha
  ext x
  rw [Subgroup.pointwise_smul_def, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hnorm y).mp hy
  · intro hx
    refine ⟨a⁻¹ * x * a, ?_, ?_⟩
    · have h2 := hnorm (a⁻¹ * x * a)
      have h3 : a * (a⁻¹ * x * a) * a⁻¹ = x := by group
      rw [h3] at h2
      exact h2.mpr hx
    · change MulAut.conj a (a⁻¹ * x * a) = x
      simp only [MulAut.conj_apply]
      group

set_option backward.isDefEq.respectTransparency false in
/-- Converse of `conj_smul_eq_self_of_mem_normalizer`. -/
theorem mem_normalizer_of_conj_smul_eq_self {Q : Subgroup G} {a : G}
    (h : MulAut.conj a • Q = Q) : a ∈ Subgroup.normalizer Q := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h, Subgroup.pointwise_smul_def, Subgroup.mem_map]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h, Subgroup.pointwise_smul_def, Subgroup.mem_map] at hy
    obtain ⟨z, hz, hz_eq⟩ := hy
    have h1 : a * z * a⁻¹ = a * y * a⁻¹ := by
      simpa only [MulDistribMulAction.toMonoidEnd_apply, MulDistribMulAction.toMonoidHom_apply,
        MulAut.smul_def, MulAut.conj_apply] using hz_eq
    have hzy : z = y := mul_left_cancel (mul_right_cancel h1)
    exact hzy ▸ hz

/-- **`ℋ_⊤(A;π)` is stable under conjugation by `C_G(A)`**. -/
theorem conj_smul_mem_hInvariant_top {A : Subgroup G} {π : Set ℕ} {Q : Subgroup G}
    (hQ : Q ∈ hInvariant ⊤ A π) {k : G} (hk : k ∈ Subgroup.centralizer (A : Set G)) :
    MulAut.conj k • Q ∈ hInvariant ⊤ A π := by
  obtain ⟨-, hQnorm, hQpi⟩ := hQ
  refine ⟨le_top, ?_, ?_⟩
  · intro a ha
    apply mem_normalizer_of_conj_smul_eq_self
    have hcomm : a * k = k * a := Subgroup.mem_centralizer_iff.mp hk a ha
    calc MulAut.conj a • MulAut.conj k • Q
        = MulAut.conj (a * k) • Q := by rw [smul_smul, ← map_mul]
      _ = MulAut.conj (k * a) • Q := by rw [hcomm]
      _ = MulAut.conj k • MulAut.conj a • Q := by rw [smul_smul, ← map_mul]
      _ = MulAut.conj k • Q := by
          rw [conj_smul_eq_self_of_mem_normalizer (hQnorm ha)]
  · have hcard : Nat.card ↥(MulAut.conj k • Q) = Nat.card ↥Q :=
      (Nat.card_congr (Subgroup.equivSMul (MulAut.conj k) Q).toEquiv).symm
    intro r hr
    rw [hcard] at hr
    exact hQpi r hr

/-- **`ℋ_⊤*(A;π)` is stable under conjugation by `C_G(A)`**: maximality transports along
the order isomorphism `Q ↦ Q^k`. -/
theorem conj_smul_mem_hInvariantStar_top {A : Subgroup G} {π : Set ℕ} {Q : Subgroup G}
    (hQ : Q ∈ hInvariantStar ⊤ A π) {k : G} (hk : k ∈ Subgroup.centralizer (A : Set G)) :
    MulAut.conj k • Q ∈ hInvariantStar ⊤ A π := by
  obtain ⟨hQmem, hQmax⟩ := hQ
  refine ⟨conj_smul_mem_hInvariant_top hQmem hk, ?_⟩
  intro Q' hQ' hle
  have h1 : MulAut.conj k⁻¹ • Q' ∈ hInvariant ⊤ A π :=
    conj_smul_mem_hInvariant_top hQ' (inv_mem hk)
  have h2 : Q ≤ MulAut.conj k⁻¹ • Q' := by
    calc Q = MulAut.conj k⁻¹ • MulAut.conj k • Q := by
          rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      _ ≤ MulAut.conj k⁻¹ • Q' := by
          rw [Subgroup.pointwise_smul_le_pointwise_smul_iff]
          exact hle
  have h3 : MulAut.conj k⁻¹ • Q' = Q := hQmax _ h1 h2
  calc Q' = MulAut.conj k • MulAut.conj k⁻¹ • Q' := by
        rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    _ = MulAut.conj k • Q := by rw [h3]

/-- **`ℋ_⊤(A;π)` is stable under conjugation by `N_G(A)`**.
If `g` normalizes `A`, then conjugating an `A`-invariant `π`-subgroup by `g`
again gives an `A`-invariant `π`-subgroup. -/
theorem conj_smul_mem_hInvariant_top_of_normalizer {A : Subgroup G} {π : Set ℕ}
    {Q : Subgroup G} (hQ : Q ∈ hInvariant ⊤ A π) {g : G}
    (hgA : MulAut.conj g • A = A) :
    MulAut.conj g • Q ∈ hInvariant ⊤ A π := by
  obtain ⟨-, hQnorm, hQpi⟩ := hQ
  have hgA' : MulAut.conj g⁻¹ • A = A := by
    conv_lhs => rw [← hgA]
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  refine ⟨le_top, ?_, ?_⟩
  · intro a ha
    apply mem_normalizer_of_conj_smul_eq_self
    have ha' : g⁻¹ * a * g ∈ A := by
      have hmem : MulAut.conj g⁻¹ a ∈ MulAut.conj g⁻¹ • A :=
        Subgroup.smul_mem_pointwise_smul_iff.mpr ha
      rw [hgA'] at hmem
      simpa only [MulAut.conj_apply, inv_inv] using hmem
    calc MulAut.conj a • MulAut.conj g • Q
        = MulAut.conj (a * g) • Q := by rw [smul_smul, ← map_mul]
      _ = MulAut.conj (g * (g⁻¹ * a * g)) • Q := by group
      _ = MulAut.conj g • MulAut.conj (g⁻¹ * a * g) • Q := by
          rw [smul_smul, ← map_mul]
      _ = MulAut.conj g • Q := by
          rw [conj_smul_eq_self_of_mem_normalizer (hQnorm ha')]
  · have hcard : Nat.card ↥(MulAut.conj g • Q) = Nat.card ↥Q :=
      (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g) Q).toEquiv).symm
    intro r hr
    rw [hcard] at hr
    exact hQpi r hr

/-- **`ℋ_⊤^*(A;π)` is stable under conjugation by `N_G(A)`**. -/
theorem conj_smul_mem_hInvariantStar_top_of_normalizer {A : Subgroup G} {π : Set ℕ}
    {Q : Subgroup G} (hQ : Q ∈ hInvariantStar ⊤ A π) {g : G}
    (hgA : MulAut.conj g • A = A) :
    MulAut.conj g • Q ∈ hInvariantStar ⊤ A π := by
  obtain ⟨hQmem, hQmax⟩ := hQ
  have hgA' : MulAut.conj g⁻¹ • A = A := by
    conv_lhs => rw [← hgA]
    rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  refine ⟨conj_smul_mem_hInvariant_top_of_normalizer hQmem hgA, ?_⟩
  intro Q' hQ' hle
  have h1 : MulAut.conj g⁻¹ • Q' ∈ hInvariant ⊤ A π :=
    conj_smul_mem_hInvariant_top_of_normalizer hQ' hgA'
  have h2 : Q ≤ MulAut.conj g⁻¹ • Q' := by
    calc Q = MulAut.conj g⁻¹ • MulAut.conj g • Q := by
          rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      _ ≤ MulAut.conj g⁻¹ • Q' := by
          rw [Subgroup.pointwise_smul_le_pointwise_smul_iff]
          exact hle
  have h3 : MulAut.conj g⁻¹ • Q' = Q := hQmax _ h1 h2
  calc Q' = MulAut.conj g • MulAut.conj g⁻¹ • Q' := by
        rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    _ = MulAut.conj g • Q := by rw [h3]

/-- **Every `A`-invariant `π`-subgroup extends to a maximal one** (`[Finite G]`):
`Q ∈ ℋ_H(A;π)` lies under some `Q* ∈ ℋ_H*(A;π)`. -/
theorem exists_le_hInvariantStar [Finite G] {H A : Subgroup G} {π : Set ℕ} {Q : Subgroup G}
    (hQ : Q ∈ hInvariant H A π) :
    ∃ Qs ∈ hInvariantStar H A π, Q ≤ Qs := by
  obtain ⟨Qs, hQQs, hQs_mem, hQs_max⟩ :=
    exists_maximal_ge_of_wellFoundedGT (· ∈ hInvariant H A π) Q hQ
  refine ⟨Qs, ⟨hQs_mem, ?_⟩, hQQs⟩
  intro Q' hQ' hle
  exact le_antisymm (hQs_max hQ' hle) hle

end OddOrder.GroupTheory


