-- Prove2me | Definitions.Def_GirvingAKS_Misc_Fin
-- name    : GirvingAKS_Misc_Fin
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:29:37.677191+00:00
-- url     : https://prove2.me/theorems/2321e977-9e21-44d0-9a54-3fad6a45867d
-- title:
--   AKS sorting networks (Seiferas port) — Fin Arithmetic Helpers
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/Misc/Fin.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Reusable `Fin` encode/decode lemmas for product-type indexing. Used by graph constructions in `Graph/Regular.lean` and `ZigZag.lean` that represent `Fin n × Fin d` as `Fin (n * d)` via `j * d + i` encoding.
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/Misc/Fin.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/Misc/Fin.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Fin Arithmetic Helpers

  Reusable `Fin` encode/decode lemmas for product-type indexing.
  Used by graph constructions in `Graph/Regular.lean` and `ZigZag.lean` that represent
  `Fin n × Fin d` as `Fin (n * d)` via `j * d + i` encoding.
-/


section


/-- Encoding a pair `(j, i) : Fin n × Fin d` as `j * d + i` stays in bounds. -/
theorem Fin.pair_lt {n d : ℕ} (j : Fin n) (i : Fin d) :
    j.val * d + i.val < n * d :=
  calc j.val * d + i.val
      < j.val * d + d := Nat.add_lt_add_left i.isLt _
    _ = (j.val + 1) * d := by ring
    _ ≤ n * d := Nat.mul_le_mul_right d (Nat.succ_le_of_lt j.isLt)

/-- Decode-encode: dividing `x * d + y` by `d` gives `x`. -/
theorem fin_encode_fst {n d : ℕ} (x : Fin n) (y : Fin d)
    (h : (x.val * d + y.val) / d < n) :
    (⟨(x.val * d + y.val) / d, h⟩ : Fin n) = x := by
  apply Fin.ext
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact absurd y.isLt (by omega))
  show (x.val * d + y.val) / d = x.val
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt y.isLt]; omega

/-- Decode-encode: `x * d + y` mod `d` gives `y`. -/
theorem fin_encode_snd {n d : ℕ} (x : Fin n) (y : Fin d)
    (h : (x.val * d + y.val) % d < d) :
    (⟨(x.val * d + y.val) % d, h⟩ : Fin d) = y := by
  apply Fin.ext
  show (x.val * d + y.val) % d = y.val
  have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; exact absurd y.isLt (by omega))
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt y.isLt]

/-- Encode-decode: `(ij / d) * d + ij % d = ij`. -/
theorem fin_div_add_mod {n d : ℕ} (ij : Fin (n * d))
    (h : (ij.val / d) * d + ij.val % d < n * d) :
    (⟨(ij.val / d) * d + ij.val % d, h⟩ : Fin (n * d)) = ij := by
  apply Fin.ext
  show (ij.val / d) * d + ij.val % d = ij.val
  rw [Nat.mul_comm]; exact Nat.div_add_mod ij.val d


/-! **Counting** -/

/-- Count of `Fin n` elements with value < t equals t (when t ≤ n). -/
lemma card_filter_val_lt (n t : ℕ) (h : t ≤ n) :
    (Finset.univ.filter (fun i : Fin n ↦ i.val < t)).card = t := by
  by_cases ht : t < n
  · have : (Finset.univ.filter (fun i : Fin n ↦ i.val < t)) = Finset.Iio ⟨t, ht⟩ := by
      ext i; simp [Finset.mem_Iio, Fin.lt_def]
    rw [this, Fin.card_Iio]
  · push_neg at ht; obtain rfl := le_antisymm h ht
    have : (Finset.univ.filter (fun i : Fin t ↦ i.val < t)) = Finset.univ := by ext i; simp
    rw [this, Finset.card_fin]

/-- Count of `Fin n` elements with value ≥ thresh equals n - thresh. -/
lemma card_filter_val_ge (n thresh : ℕ) (h : thresh ≤ n) :
    (Finset.univ.filter (fun i : Fin n ↦ thresh ≤ i.val)).card = n - thresh := by
  have htotal : (Finset.univ.filter (fun i : Fin n ↦ i.val < thresh)).card +
      (Finset.univ.filter (fun i : Fin n ↦ ¬ i.val < thresh)).card = n := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter_not _ _ _)]
    rw [Finset.filter_union_filter_not_eq]; exact Finset.card_fin n
  have hconv : (Finset.univ.filter (fun i : Fin n ↦ thresh ≤ i.val)) =
      (Finset.univ.filter (fun i : Fin n ↦ ¬ i.val < thresh)) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  rw [← hconv, card_filter_val_lt n thresh h] at htotal; omega


/-! **Order** -/

/-- Strict inequality from `≤` and `≠` for `Fin`. -/
lemma Fin.lt_of_le_of_ne {n : ℕ} {a b : Fin n} (h1 : a ≤ b) (h2 : a ≠ b) : a < b := by
  by_contra h
  push_neg at h
  exact h2 (Fin.le_antisymm h1 h)


/-! **Rank** -/

/-- The rank of an element: the number of strictly smaller elements.
    For `Fin n`, this equals the element's value. -/
def rank {α : Type*} [Fintype α] [LinearOrder α] (a : α) : ℕ :=
  (Finset.univ.filter (· < a)).card

/-- The rank of a `Fin n` element equals its value. -/
lemma rank_fin_val {n : ℕ} (i : Fin n) : rank i = i.val := by
  unfold rank
  have : Finset.univ.filter (· < i) = Finset.Iio i := by
    ext x; simp [Finset.mem_Iio]
  rw [this, Fin.card_Iio]

/-- The rank of a `Fin n` element in the order dual equals `n - 1 - i.val`. -/
lemma rank_fin_od_val {n : ℕ} (i : Fin n) :
    rank (α := (Fin n)ᵒᵈ) (OrderDual.toDual i) = n - 1 - i.val := by
  unfold rank
  -- In (Fin n)ᵒᵈ, b <_od a means a <_orig b, i.e., i < b
  have hcard : (Finset.univ.filter (· < OrderDual.toDual i) : Finset (Fin n)ᵒᵈ).card =
    (Finset.univ.filter (fun b : Fin n ↦ i < b)).card := by
    apply Finset.card_nbij' (fun a ↦ OrderDual.ofDual a) (fun b ↦ OrderDual.toDual b)
    · intro a ha
      rw [Finset.mem_coe, Finset.mem_filter] at ha ⊢
      exact ⟨Finset.mem_univ _, ha.2⟩
    · intro b hb
      rw [Finset.mem_coe, Finset.mem_filter] at hb ⊢
      exact ⟨Finset.mem_univ _, hb.2⟩
    · intro _ _; rfl
    · intro _ _; rfl
  rw [hcard]
  have : Finset.univ.filter (fun b : Fin n ↦ i < b) = Finset.Ioi i := by
    ext x; simp [Finset.mem_Ioi]
  rw [this, Fin.card_Ioi]

/-- `rank` on `(Fin n)ᵒᵈ` in terms of `.val`. Matches goals after unfolding
    `FinalNearsorted` where the variable is already of type `(Fin n)ᵒᵈ`. -/
@[simp] lemma rank_fin_od {n : ℕ} (a : (Fin n)ᵒᵈ) :
    rank a = n - 1 - a.val :=
  rank_fin_od_val (OrderDual.ofDual a)

/-- Variant of `rank_fin_od` for a `Fin n`-typed term read in `(Fin n)ᵒᵈ`
(e.g. `w x` with `w : Fin n → Fin n`). -/
@[simp] lemma rank_fin_od_fin {n : ℕ} (a : Fin n) :
    rank (α := (Fin n)ᵒᵈ) a = n - 1 - a.val :=
  rank_fin_od_val a


/-! **Fin (2 * m) Partition Helpers** -/

/-- Partition a predicate on `Fin (2*m)` into top half (`val < m`) and bottom half
    (`m ≤ val`), each bijecting with `Fin m`. -/
lemma card_filter_fin_double {m : ℕ} (P : Fin (2 * m) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
    (Finset.univ.filter (fun v : Fin m ↦ P ⟨v.val, by omega⟩)).card +
    (Finset.univ.filter (fun u : Fin m ↦ P ⟨m + u.val, by omega⟩)).card := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [← Finset.card_filter_add_card_filter_not (fun i : Fin (2 * m) ↦ i.val < m),
        Finset.filter_filter, Finset.filter_filter]
    congr 1
    · apply Finset.card_nbij'
        (fun i ↦ ⟨i.val % m, Nat.mod_lt _ hm⟩)
        (fun v ↦ ⟨v.val, by omega⟩)
      · intro i hi
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        convert hi.1 using 1; ext1; exact Nat.mod_eq_of_lt hi.2
      · intro v hv
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
        exact ⟨hv, v.isLt⟩
      · intro i hi
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        ext1; exact Nat.mod_eq_of_lt hi.2
      · intro v _; ext1; exact Nat.mod_eq_of_lt v.isLt
    · apply Finset.card_nbij'
        (fun i ↦ ⟨i.val - m, by omega⟩)
        (fun u ↦ ⟨m + u.val, by omega⟩)
      · intro i hi
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          not_lt] at hi ⊢
        convert hi.1 using 1; ext1; dsimp; omega
      · intro u hu
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          not_lt] at hu ⊢
        exact ⟨hu, by omega⟩
      · intro i hi
        simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
          not_lt] at hi
        have := hi.2; ext1; dsimp; omega
      · intro u _; ext1; dsimp; omega

/-- Top-half card equivalence:
    `#{i : Fin (2m) | i.val < m ∧ P i} = #{v : Fin m | P ⟨v.val, _⟩}` -/
lemma card_filter_top_half {m : ℕ} (P : Fin (2 * m) → Prop) [DecidablePred P] :
    ((Finset.univ.filter (fun i : Fin (2 * m) ↦ (i : ℕ) < m)).filter P).card =
    (Finset.univ.filter (fun v : Fin m ↦ P ⟨v.val, by omega⟩)).card := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [Finset.filter_filter]
    apply Finset.card_nbij'
      (fun i ↦ ⟨i.val % m, Nat.mod_lt _ hm⟩)
      (fun v ↦ ⟨v.val, by omega⟩)
    · intro i hi
      simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      convert hi.2 using 1; ext1; exact Nat.mod_eq_of_lt hi.1
    · intro v hv
      simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
      exact ⟨v.isLt, hv⟩
    · intro i hi
      simp only [SetLike.mem_coe, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      ext1; exact Nat.mod_eq_of_lt hi.1
    · intro v _; ext1; exact Nat.mod_eq_of_lt v.isLt

end


