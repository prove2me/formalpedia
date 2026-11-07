-- Prove2me | Definitions.Def_LosslessQLTC_rev
-- name    : LosslessQLTC_rev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:17:06.008566+00:00
-- url     : https://prove2.me/theorems/5936f0b2-fad3-4ff5-adc6-5e0ae78647f2
-- title:
--   The reversed complex $X^{\mathrm{rev}}$
-- statement:
--   Choosing $[k]$ as the origin reverses every edge orientation. The reversed complex $X^{\mathrm{rev}}$ has the same vertices, edges and declared squares, with $V_I^{\mathrm{rev}}=V_{[k]\setminus I}$, $D_i^{\mathrm{rev}}=D'_i$ and $(D'_i)^{\mathrm{rev}}=D_i$. The labels of the directions do not change. It is again a square complex, and this is how the $X$-code of the CSS construction is studied.
--
--   **Formalization Note.** The identification of level $s$ of $X$ with level $k-s$ of $X^{\mathrm{rev}}$ is an explicit equivalence for $s+t=k$, which is the identity on vertices.
-- source:
--   Cohen, Leigh, Reiner, Ta-Shma, Tzalik, Good Quantum Locally Testable Codes from Lossless Cubical Complexes, arXiv:2610.00525 (held version, sha256 d61f0ed9…), p.18

import Mathlib
import Definitions.Def_LosslessQLTC_normC

namespace LosslessQLTC

variable {k : ℕ}

/-- The reversed complex `X^rev` (arXiv:2610.00525, held version, sha256 d61f0ed9…, p.18): the same
vertices, edges and declared squares, with `V_I^rev = V_{[k] ∖ I}`, every orientation reversed, and
`D_i^rev = D′_i`, `(D′_i)^rev = D_i`. The direction labels are kept. -/
def rev (X : SquareComplex k) : SquareComplex k where
  Vtx := X.Vtx
  type v := Finset.univ \ X.type v
  block_nonempty I := by
    obtain ⟨v, hv⟩ := X.block_nonempty (Finset.univ \ I)
    exact ⟨v, by simp [hv]⟩
  up x y := X.up y x
  decUp x y := X.decUp y x
  up_type {x y} h := by
    obtain ⟨i, hi, hty⟩ := X.up_type h
    refine ⟨i, ?_, ?_⟩
    · simp [hty]
    · ext j
      simp only [hty, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, not_or]
      by_cases hj : j = i
      · subst hj; simp [hi]
      · simp [hj]
  D := X.D'
  D' := X.D
  D_pos := X.D'_pos
  D'_pos := X.D_pos
  deg_up x i hi := by
    have hi' : i ∈ X.type x := by simpa using hi
    rw [← X.deg_down x i hi']
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h
      ext j
      have := Finset.ext_iff.mp h j
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert] at this
      simp only [Finset.mem_erase]
      by_cases hj : j = i
      · subst hj; simp at this; simpa using this
      · simp only [hj, false_or] at this; simp [hj]; tauto
    · intro h
      ext j
      simp only [h, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_erase,
        Finset.mem_insert]
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
  deg_down y i hi := by
    have hi' : i ∉ X.type y := by simpa using hi
    rw [← X.deg_up y i hi']
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h
      ext j
      have := Finset.ext_iff.mp h j
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_erase] at this
      simp only [Finset.mem_insert]
      by_cases hj : j = i
      · subst hj; simpa using this
      · simp only [hj, false_or]; simp [hj] at this; tauto
    · intro h
      ext j
      simp only [h, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_erase,
        Finset.mem_insert, not_or]
  Square a b b' c := X.Square c b b' a
  square_symm h := X.square_symm h
  square_up h := by
    obtain ⟨h1, h2, h3, h4⟩ := X.square_up h
    exact ⟨h3, h4, h1, h2⟩
  square_type {a b b' c} h := by
    intro heq
    apply X.square_type h
    ext j
    have := Finset.ext_iff.mp heq j
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at this
    tauto
  complete_bottom {c b b'} h1 h2 h3 :=
    X.complete_top h1 h2 (fun heq => h3 (by rw [heq]))
  complete_top {a b b'} h1 h2 h3 :=
    X.complete_bottom h1 h2 (fun heq => h3 (by rw [heq]))
  complete_middle {a b c} h1 h2 := X.complete_middle h2 h1

/-- The identity on vertices identifies level `s` of `X` with level `t = k − s` of `X^rev`
(arXiv:2610.00525, Lemma 2.12, p.18). The hypothesis `s + t = k` replaces natural-number
subtraction. -/
def revLevel (X : SquareComplex k) (s t : ℕ) (h : s + t = k) : Level X s ≃ Level (rev X) t where
  toFun v := ⟨v.1, by
    have h1 : (X.type v.1).card = s := v.2
    change (Finset.univ \ X.type v.1).card = t
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [h1]; omega⟩
  invFun v := ⟨v.1, by
    have h1 : (Finset.univ \ X.type v.1).card = t := v.2
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)] at h1
    have h2 : (X.type v.1).card ≤ k := by
      simpa using Finset.card_le_univ (X.type v.1)
    simp at h1
    omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

end LosslessQLTC


