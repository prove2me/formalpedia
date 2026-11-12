-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S09_CrossOrthogonality
-- name    : OddOrder_Peterfalvi_S09_CrossOrthogonality
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:38:58.349407+00:00
-- url     : https://prove2.me/theorems/b4cc0bad-3635-4813-a9bc-a47b4a64e396
-- title:
--   Cross-orthogonality of coherent images (Peterfalvi (7.9) primitive)
-- statement:
--   The linear-algebra lemma behind the cross-family orthogonality $\langle\zeta_1^{\nu_1},\zeta_2^{\nu_2}\rangle=0$ used in Peterfalvi (7.9) (mathcomp `orthonormal_vchar_diff_ortho`, consumed by `disjoint_coherent_ortho`). If $\{a,b\}$ and $\{c,d\}$ are two orthonormal pairs of virtual characters, the cross inner products are controlled.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_CrossOrthogonality.lean

/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_CrossOrthogonality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterRowOrthogonality
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ZIrrFourier

namespace OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

/-- **A signed integer times a positive natural equals another such product only with equal sign.**
If `s, t ∈ {±1}`, `m, n > 0`, and `(s : ℂ) * m = (t : ℂ) * n`, then `s = t`: the sign of `s·m`
(with `m > 0`) is `s`.  The arithmetic core of the equal-degree ⟹ equal-sign step. -/
private theorem sign_eq_of_mul_pos_cast {s t : ℤ} {m n : ℕ}
    (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (hm : 0 < m) (hn : 0 < n)
    (h : (s : ℂ) * (m : ℂ) = (t : ℂ) * (n : ℂ)) : s = t := by
  have hcast : s * (m : ℤ) = t * (n : ℤ) := by exact_mod_cast h
  rcases hs with hs | hs <;> rcases ht with ht | ht <;> subst hs <;> subst ht <;> omega

/-- **Cross-orthogonality from difference-orthogonality of two equal-degree orthonormal pairs**
(Peterfalvi (7.9) §1 primitive; coq `orthonormal_vchar_diff_ortho`).

`{a, b}` and `{c, d}` orthonormal in `ℤ[Irr G]`, of equal degree within each pair (`a 1 = b 1`,
`c 1 = d 1`), with `⟨a − b, c − d⟩ = 0`, force `⟨a, c⟩ = 0`.  The equal-degree hypotheses `hab1`,
`hcd1` are essential (see the module docstring). -/
theorem orthonormal_vchar_diff_ortho
    {a b c d : ClassFunction G ℂ}
    (haZ : a ∈ ZIrr G) (hbZ : b ∈ ZIrr G) (hcZ : c ∈ ZIrr G) (hdZ : d ∈ ZIrr G)
    (hana : ClassFunction.inner a a = 1) (hbnb : ClassFunction.inner b b = 1)
    (hcnc : ClassFunction.inner c c = 1) (hdnd : ClassFunction.inner d d = 1)
    (hab : ClassFunction.inner a b = 0) (hcd : ClassFunction.inner c d = 0)
    (hdiff : ClassFunction.inner (a - b) (c - d) = 0)
    (hab1 : a 1 = b 1) (hcd1 : c 1 = d 1) :
    ClassFunction.inner a c = 0 := by
  classical
  obtain ⟨ε, μ, hε, rfl⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one haZ hana
  obtain ⟨ε', μ', hε', rfl⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hbZ hbnb
  obtain ⟨δ, ν, hδ, rfl⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hcZ hcnc
  obtain ⟨δ', ν', hδ', rfl⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hdZ hdnd
  -- `⟨m·φ, n·ψ⟩ = m · n · [φ = ψ]` for irreducibles `φ, ψ`.
  have key : ∀ (m n : ℤ) (φ ψ : IrreducibleCharacter G),
      ClassFunction.inner (m • (φ : ClassFunction G ℂ)) (n • (ψ : ClassFunction G ℂ))
        = (m : ℂ) * (n : ℂ) * (if φ = ψ then (1 : ℂ) else 0) := by
    intro m n φ ψ
    rw [← Int.cast_smul_eq_zsmul ℂ m (φ : ClassFunction G ℂ),
        ← Int.cast_smul_eq_zsmul ℂ n (ψ : ClassFunction G ℂ),
        ClassFunction.inner_smul_left, ClassFunction.inner_smul_right,
        irreducibleCharacter_inner, star_intCast, ← mul_assoc]
  -- The four signs are nonzero.
  have hε_ne : (ε : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by rcases hε with h | h <;> simp [h])
  have hε'_ne : (ε' : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by rcases hε' with h | h <;> simp [h])
  have hδ_ne : (δ : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by rcases hδ with h | h <;> simp [h])
  have hδ'_ne : (δ' : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by rcases hδ' with h | h <;> simp [h])
  -- Orthogonality forces distinct underlying irreducibles.
  have hμμ' : μ ≠ μ' := by
    intro h
    rw [h, key ε ε' μ' μ', if_pos rfl, mul_one] at hab
    exact (mul_ne_zero hε_ne hε'_ne) hab
  have hνν' : ν ≠ ν' := by
    intro h
    rw [h, key δ δ' ν' ν', if_pos rfl, mul_one] at hcd
    exact (mul_ne_zero hδ_ne hδ'_ne) hcd
  -- Equal degree within each pair forces equal signs.
  obtain ⟨dμ, hdμpos, hdμ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast μ
  obtain ⟨dμ', hdμ'pos, hdμ'⟩ := irreducibleCharacter_apply_one_eq_pos_natCast μ'
  obtain ⟨dν, hdνpos, hdν⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ν
  obtain ⟨dν', hdν'pos, hdν'⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ν'
  have hεε' : ε = ε' := by
    apply sign_eq_of_mul_pos_cast hε hε' hdμpos hdμ'pos
    rw [← Int.cast_smul_eq_zsmul ℂ ε (μ : ClassFunction G ℂ),
        ← Int.cast_smul_eq_zsmul ℂ ε' (μ' : ClassFunction G ℂ),
        ClassFunction.smul_apply, ClassFunction.smul_apply, hdμ, hdμ'] at hab1
    exact hab1
  have hδδ' : δ = δ' := by
    apply sign_eq_of_mul_pos_cast hδ hδ' hdνpos hdν'pos
    rw [← Int.cast_smul_eq_zsmul ℂ δ (ν : ClassFunction G ℂ),
        ← Int.cast_smul_eq_zsmul ℂ δ' (ν' : ClassFunction G ℂ),
        ClassFunction.smul_apply, ClassFunction.smul_apply, hdν, hdν'] at hcd1
    exact hcd1
  -- `⟨a, c⟩ = ε · δ · [μ = ν]`; it suffices to show `μ ≠ ν`.
  rw [key ε δ μ ν]
  suffices hμν : μ ≠ ν by rw [if_neg hμν, mul_zero]
  intro hμν
  -- Expand `⟨a − b, c − d⟩ = 0`; only the surviving cross-terms remain after `μ = ν`.
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, key ε δ μ ν, key ε δ' μ ν',
      key ε' δ μ' ν, key ε' δ' μ' ν'] at hdiff
  have h2 : μ ≠ ν' := by rw [hμν]; exact hνν'
  have h3 : μ' ≠ ν := by rw [hμν.symm]; exact fun h => hμμ' h.symm
  rw [if_pos hμν, if_neg h2, if_neg h3] at hdiff
  by_cases h4 : μ' = ν'
  · rw [if_pos h4, hεε', hδδ'] at hdiff
    have hx : (ε' : ℂ) * (δ' : ℂ) = 0 := by linear_combination hdiff / 2
    exact (mul_ne_zero hε'_ne hδ'_ne) hx
  · rw [if_neg h4] at hdiff
    have hx : (ε : ℂ) * (δ : ℂ) = 0 := by linear_combination hdiff
    exact (mul_ne_zero hε_ne hδ_ne) hx

end OddOrder.RepresentationTheory


