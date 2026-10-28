-- Prove2me | solution 1 for AryaANN.Search.disjoint_box_count
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-24T09:46:26.79432+00:00
-- url     : https://prove2.me/submissions/7f699598-3c31-4926-9fb4-9d2730b4b3e9

import Mathlib
import Definitions.Def_AryaANN_Search_Setting

namespace AryaANN.Search

/-- A finite strict grid hits the interior of every interval wider than its spacing
that overlaps the interior of the grid's span. -/
theorem interval_grid_hit (n : ℕ) (hn : 0 < n) (t δ lo hi : ℝ)
    (hδ : 0 < δ) (hwidth : δ < hi - lo)
    (hleft : t < hi) (hright : lo < t + ((n : ℝ) - 1) * δ) :
    ∃ j : Fin n, lo < t + (j : ℝ) * δ ∧ t + (j : ℝ) * δ < hi := by
  by_cases hlt : lo < t
  · exact ⟨⟨0, hn⟩, by simpa using hlt, by simpa using hleft⟩
  · have hlo : t ≤ lo := le_of_not_gt hlt
    let a := (lo - t) / δ
    have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hlo) hδ.le
    have ha_eq : a * δ = lo - t := div_mul_cancel₀ _ hδ.ne'
    have hfloor : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha
    have hfloor' : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
    have hjlt : ((⌊a⌋₊ + 1 : ℕ) : ℝ) < n := by
      push_cast
      nlinarith
    have hjn : ⌊a⌋₊ + 1 < n := by exact_mod_cast hjlt
    refine ⟨⟨⌊a⌋₊ + 1, hjn⟩, ?_, ?_⟩ <;> dsimp <;> push_cast <;> nlinarith

/-- Strict coordinate inequalities describe the actual topological interior. -/
theorem rect_mem_interior_iff {d : ℕ} (R : Rect d) (x : Fin d → ℝ) :
    x ∈ interior R.toSet ↔ ∀ i, R.lo i < x i ∧ x i < R.hi i := by
  rw [Rect.toSet, ← Set.pi_univ_Icc, interior_pi_set Set.finite_univ]
  simp only [Set.mem_pi, Set.mem_univ, forall_true_left, interior_Icc, Set.mem_Ioo]

/-- Interior-disjoint rectangles hit by a finite Cartesian grid inject into that grid.
The side hypothesis is strictly larger than the grid spacing, not an aspect ratio. -/
theorem disjoint_rect_count_grid {d N n : ℕ} (hn : 0 < n)
    (B : Fin N → Rect d) (t : Fin d → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hwidth : ∀ k i, δ < (B k).len i)
    (hleft : ∀ k i, t i < (B k).hi i)
    (hright : ∀ k i, (B k).lo i < t i + ((n : ℝ) - 1) * δ)
    (hdisj : Pairwise (fun k l => Disjoint (interior (B k).toSet) (interior (B l).toSet))) :
    N ≤ n ^ d := by
  classical
  have hhit (k : Fin N) (i : Fin d) :
      ∃ j : Fin n, (B k).lo i < t i + (j : ℝ) * δ ∧
        t i + (j : ℝ) * δ < (B k).hi i :=
    interval_grid_hit n hn (t i) δ ((B k).lo i) ((B k).hi i)
      hδ (hwidth k i) (hleft k i) (hright k i)
  choose g hg using hhit
  have hmem (k : Fin N) : (fun i => t i + (g k i : ℝ) * δ) ∈ interior (B k).toSet :=
    (rect_mem_interior_iff _ _).mpr (hg k)
  have hinj : Function.Injective g := by
    intro k l hkl
    by_contra hne
    have hp := hmem k
    have hq : (fun i => t i + (g k i : ℝ) * δ) ∈ interior (B l).toSet := by
      rw [hkl]
      exact hmem l
    exact Set.disjoint_left.mp (hdisj hne) hp hq
  simpa using Fintype.card_le_of_injective g hinj

/-- Finitely many strict bounds have a common positive strict bound below r,
including when the index type is empty. -/
theorem finite_strict_radius {ι : Type*} [Fintype ι] (f : ι → ℝ) (r : ℝ)
    (hr : 0 < r) (hf : ∀ i, f i < r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧ ∀ i, f i < ρ := by
  classical
  let S : Finset ℝ := insert 0 (Finset.univ.image f)
  have hS : S.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have hmax : S.max' hS < r := by
    have hy := S.max'_mem hS
    rcases Finset.mem_insert.mp hy with hy | hy
    · rw [hy]
      exact hr
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hy
      rw [← hi]
      exact hf i
  obtain ⟨ρ, hρlo, hρhi⟩ := exists_between hmax
  refine ⟨ρ, ?_, hρhi, ?_⟩
  · exact (S.le_max' 0 (Finset.mem_insert_self _ _)).trans_lt hρlo
  · intro i
    exact (S.le_max' (f i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))).trans_lt hρlo

/-- A coordinate difference is bounded by the platform's Minkowski distance. -/
theorem coord_le_lmDist {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (c x : Fin d → ℝ) (i : Fin d) :
    |x i - c i| ≤ lmDist m c x := by
  by_cases ht : m = ⊤
  · simpa [lmDist, ht, abs_sub_comm] using
      (le_ciSup (Finite.bddAbove_range (fun j : Fin d => |c j - x j|)) i)
  · have hk : 1 ≤ m.toNat := by simpa using ENat.toNat_le_toNat hm ht
    have hk0 : m.toNat ≠ 0 := by omega
    calc
      |x i - c i| = (|c i - x i| ^ m.toNat) ^ ((1 : ℝ) / m.toNat) := by
        rw [one_div, Real.pow_rpow_inv_natCast (abs_nonneg _) hk0, abs_sub_comm]
      _ ≤ (∑ j, |c j - x j| ^ m.toNat) ^ ((1 : ℝ) / m.toNat) := by
        have hterm : |c i - x i| ^ m.toNat ≤ ∑ j, |c j - x j| ^ m.toNat :=
          Finset.single_le_sum (fun j _ => pow_nonneg (abs_nonneg (c j - x j)) m.toNat)
            (Finset.mem_univ i)
        exact Real.rpow_le_rpow (pow_nonneg (abs_nonneg _) _) hterm (by positivity)
      _ = lmDist m c x := by simp [lmDist, ht]


/-- A finite counting bound for arbitrary interior-disjoint rectangles with a uniform
side lower bound, meeting an open coordinate cube. No aspect ratio is needed. -/
theorem disjoint_rect_count_open_cube {d : ℕ} (c : Fin d → ℝ) (r a : ℝ)
    (hr : 0 < r) (ha : 0 < a) (N : ℕ) (B : Fin N → Rect d)
    (hside : ∀ k i, a ≤ (B k).len i)
    (hdisj : Pairwise (fun k l => Disjoint (interior (B k).toSet) (interior (B l).toSet)))
    (hmeet : ∀ k, ∃ x ∈ (B k).toSet, ∀ i, |x i - c i| < r) :
    N ≤ ⌈1 + 2 * r / a⌉₊ ^ d := by
  classical
  choose x hxB hxcoord using hmeet
  obtain ⟨ρ, hρpos, hρr, hρall⟩ :=
    finite_strict_radius (fun j : Fin N × Fin d => |x j.1 j.2 - c j.2|) r hr
      (fun j => hxcoord j.1 j.2)
  let n : ℕ := ⌈1 + 2 * r / a⌉₊
  have hceil : 1 + 2 * r / a ≤ (n : ℝ) := Nat.le_ceil _
  have hquotpos : 0 < 2 * r / a := div_pos (by linarith) ha
  have hnreal : (1 : ℝ) < n := by linarith
  have hn : 0 < n := by exact_mod_cast (lt_trans zero_lt_one hnreal)
  have hden : 0 < (n : ℝ) - 1 := by linarith
  have hcover : 2 * r ≤ ((n : ℝ) - 1) * a :=
    (div_le_iff₀ ha).mp (by linarith)
  let δ : ℝ := 2 * ρ / ((n : ℝ) - 1)
  have hδpos : 0 < δ := div_pos (by linarith) hden
  have hδa : δ < a := (div_lt_iff₀ hden).mpr (by nlinarith)
  have hspan : δ * ((n : ℝ) - 1) = 2 * ρ := div_mul_cancel₀ _ hden.ne'
  change N ≤ n ^ d
  apply disjoint_rect_count_grid hn B (fun i => c i - ρ) δ hδpos
  · intro k i
    exact hδa.trans_le (hside k i)
  · intro k i
    have hc := (abs_lt.mp (hρall (k, i))).1
    have hb := (Set.mem_Icc.mp (hxB k)).2 i
    dsimp at hc ⊢
    linarith
  · intro k i
    have hc := (abs_lt.mp (hρall (k, i))).2
    have hb := (Set.mem_Icc.mp (hxB k)).1 i
    dsimp at hc ⊢
    nlinarith [hspan]
  · exact hdisj


end AryaANN.Search

open AryaANN.Search

theorem solution {d : ℕ} (m : ℕ∞) (hm : 1 ≤ m) (c : Fin d → ℝ) (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (N : ℕ) (B : Fin N → Rect d)
    (hbox : ∀ k, IsBox (B k))
    (hside : ∀ k i, s / 3 ≤ (B k).len i)
    (hdisj : Pairwise (fun k l => Disjoint (interior (B k).toSet) (interior (B l).toSet)))
    (hmeet : ∀ k, ((B k).toSet ∩ {x | lmDist m c x < r}).Nonempty) :
    N ≤ ⌈1 + 6 * r / s⌉₊ ^ d := by
  -- The general rectangle count below does not need the aspect-ratio hypothesis.
  clear hbox
  have hmeet' : ∀ k, ∃ x ∈ (B k).toSet, ∀ i, |x i - c i| < r := by
    intro k
    obtain ⟨x, hxB, hxball⟩ := hmeet k
    exact ⟨x, hxB, fun i => (coord_le_lmDist m hm c x i).trans_lt hxball⟩
  have hquot : 1 + 2 * r / (s / 3) = 1 + 6 * r / s := by ring
  simpa only [hquot] using
    disjoint_rect_count_open_cube c r (s / 3) hr (by positivity) N B hside hdisj hmeet'


#print axioms solution
