-- Prove2me | solution 1 for ApproxVI.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:58:54.13207+00:00
-- url     : https://prove2.me/submissions/b905dee6-3a0b-4f86-a749-d178cce76acc

import Mathlib
import Definitions.Def_ApproxVI_Ttilde
import Definitions.Def_ApproxVI_IsMarchaud

namespace Aux_ApproxVI_l2
open ApproxVI Filter Topology

theorem wle {d : ℕ} (ν : Fin d → ℝ) (hν : ∀ i, 0 < ν i) (z : Fin d → ℝ) (ε : ℝ) (hε : 0 ≤ ε) :
    wNorm ν z ≤ ε ↔ ∀ i, |z i| ≤ ε * ν i := by
  unfold wNorm
  rcases isEmpty_or_nonempty (Fin d) with h | h
  · rw [Real.iSup_of_isEmpty]; exact ⟨fun _ i => isEmptyElim i, fun _ => hε⟩
  · rw [ciSup_le_iff (Set.finite_range _).bddAbove]
    exact forall_congr' fun i => div_le_iff₀ (hν i)

theorem wcoord {d : ℕ} (ν : Fin d → ℝ) (hν : ∀ i, 0 < ν i) (z : Fin d → ℝ) (i : Fin d) :
    |z i| ≤ ν i * wNorm ν z := by
  have := le_ciSup (Set.finite_range (fun i => |z i| / ν i)).bddAbove i
  rw [div_le_iff₀ (hν i)] at this
  unfold wNorm; linarith

theorem wle_sum {d : ℕ} (ν : Fin d → ℝ) (hν : ∀ i, 0 < ν i) (z : Fin d → ℝ) :
    wNorm ν z ≤ ∑ i, |z i| / ν i := by
  unfold wNorm
  rcases isEmpty_or_nonempty (Fin d) with h | h
  · rw [Real.iSup_of_isEmpty]; simp
  · apply ciSup_le
    intro i
    exact Finset.single_le_sum (f := fun i => |z i| / ν i)
      (fun j _ => div_nonneg (abs_nonneg _) (hν j).le) (Finset.mem_univ i)

theorem abs_le_eucl {d : ℕ} (z : Fin d → ℝ) (i : Fin d) : |z i| ≤ euclNorm z := by
  unfold euclNorm
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  exact Finset.single_le_sum (f := fun i => z i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem eucl_le_sum {d : ℕ} (z : Fin d → ℝ) : euclNorm z ≤ ∑ i, |z i| := by
  unfold euclNorm
  rw [Real.sqrt_le_left (Finset.sum_nonneg (fun i _ => abs_nonneg _))]
  calc ∑ i, z i ^ 2 = ∑ i, |z i| ^ 2 := by simp [sq_abs]
    _ ≤ (∑ i, |z i|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)

theorem eucl_nonneg {d : ℕ} (z : Fin d → ℝ) : 0 ≤ euclNorm z := Real.sqrt_nonneg _

theorem mem_T {d : ℕ} (ν : Fin d → ℝ) (hν : ∀ i, 0 < ν i) (T : (Fin d → ℝ) → (Fin d → ℝ))
    (ε : ℝ) (hε : 0 < ε) (x y : Fin d → ℝ) :
    y ∈ Ttilde ν T ε x ↔ ∀ i, |y i - T x i| ≤ ε * ν i := by
  unfold Ttilde ballNu
  simp only [Set.mem_setOf_eq]
  rw [wle ν hν _ ε hε.le]
  rfl

end Aux_ApproxVI_l2

open ApproxVI Filter Topology Aux_ApproxVI_l2 in
theorem solution {d : ℕ} (ν : Fin d → ℝ) (hν : ∀ i, 0 < ν i) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (T : (Fin d → ℝ) → (Fin d → ℝ))
    (hT : ∀ x y, wNorm ν (T x - T y) ≤ α * wNorm ν (x - y)) (ε : ℝ) (hε : 0 < ε) :
    IsMarchaud (Ttilde ν T ε) := by
  have hset : ∀ x, Ttilde ν T ε x = Set.pi Set.univ (fun i => Set.Icc (T x i - ε * ν i) (T x i + ε * ν i)) := by
    intro x
    ext y
    rw [mem_T ν hν T ε hε]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le]
    constructor
    · intro h i; constructor <;> linarith [(h i).1, (h i).2]
    · intro h i; constructor <;> linarith [(h i).1, (h i).2]
  set A := ∑ j, 1 / ν j with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun j _ => (one_div_pos.mpr (hν j)).le)
  have hwE : ∀ z : Fin d → ℝ, wNorm ν z ≤ A * euclNorm z := by
    intro z
    refine (wle_sum ν hν z).trans ?_
    rw [hA, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j _
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_left (abs_le_eucl z j) (one_div_pos.mpr (hν j)).le
  have hTc : ∀ x y i, |T x i - T y i| ≤ ν i * α * (A * euclNorm (x - y)) := by
    intro x y i
    have h1 := wcoord ν hν (T x - T y) i
    have h2 := hT x y
    have h3 := hwE (x - y)
    simp only [Pi.sub_apply] at h1
    have hνi := (hν i).le
    calc |T x i - T y i| ≤ ν i * wNorm ν (T x - T y) := h1
      _ ≤ ν i * (α * wNorm ν (x - y)) := mul_le_mul_of_nonneg_left h2 hνi
      _ ≤ ν i * (α * (A * euclNorm (x - y))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hα.1.le) hνi
      _ = ν i * α * (A * euclNorm (x - y)) := by ring
  refine ⟨fun x => ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hset]; exact convex_pi (fun i _ => convex_Icc _ _)
  · rw [hset]; exact isCompact_univ_pi (fun i => isCompact_Icc)
  · set B := ∑ i, (|T 0 i| + ε * ν i) with hB
    set C := ∑ i, ν i * α * A with hC
    have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => add_nonneg (abs_nonneg _)
      (mul_nonneg hε.le (hν i).le))
    have hC0 : 0 ≤ C := Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (hν i).le hα.1.le) hA0)
    refine ⟨B + C + 1, by linarith, fun x w hw => ?_⟩
    rw [mem_T ν hν T ε hε] at hw
    have hwi : ∀ i, |w i| ≤ (|T 0 i| + ε * ν i) + ν i * α * A * euclNorm x := by
      intro i
      have h1 := hw i
      have h2 := hTc x 0 i
      rw [sub_zero] at h2
      have : |w i| ≤ |w i - T x i| + |T x i - T 0 i| + |T 0 i| := by
        calc |w i| = |(w i - T x i) + (T x i - T 0 i) + T 0 i| := by ring_nf
          _ ≤ |(w i - T x i) + (T x i - T 0 i)| + |T 0 i| := abs_add_le _ _
          _ ≤ |w i - T x i| + |T x i - T 0 i| + |T 0 i| := by
              linarith [abs_add_le (w i - T x i) (T x i - T 0 i)]
      linarith
    have hsum : euclNorm w ≤ B + C * euclNorm x := by
      refine (eucl_le_sum w).trans ?_
      calc ∑ i, |w i| ≤ ∑ i, ((|T 0 i| + ε * ν i) + ν i * α * A * euclNorm x) :=
            Finset.sum_le_sum (fun i _ => hwi i)
        _ = B + C * euclNorm x := by
            rw [Finset.sum_add_distrib, hB, hC, Finset.sum_mul]
    have hx0 := eucl_nonneg x
    nlinarith
  · intro xs ys x y hxs hys hmem
    rw [mem_T ν hν T ε hε]
    intro i
    have hcontT : ∀ i, Continuous (fun x => T x i) := by
      intro i
      rw [Metric.continuous_iff]
      intro b δ hδ
      set L := ν i * α * A * Real.sqrt d + 1 with hL
      have hLpos : 0 < L := by
        have : 0 ≤ ν i * α * A * Real.sqrt d :=
          mul_nonneg (mul_nonneg (mul_nonneg (hν i).le hα.1.le) hA0) (Real.sqrt_nonneg _)
        linarith
      refine ⟨δ / L, div_pos hδ hLpos, fun a ha => ?_⟩
      rw [Real.dist_eq]
      have h1 := hTc a b i
      have he : euclNorm (a - b) ≤ Real.sqrt d * dist a b := by
        unfold euclNorm
        rw [← Real.sqrt_mul_self dist_nonneg, ← Real.sqrt_mul (Nat.cast_nonneg d)]
        apply Real.sqrt_le_sqrt
        calc ∑ j, (a - b) j ^ 2 ≤ ∑ _j : Fin d, dist a b * dist a b := by
              apply Finset.sum_le_sum
              intro j _
              have : |(a - b) j| ≤ dist a b := by
                rw [Pi.sub_apply, ← Real.dist_eq]; exact dist_le_pi_dist a b j
              rw [← sq_abs, sq]
              exact mul_le_mul this this (abs_nonneg _) dist_nonneg
          _ = d * (dist a b * dist a b) := by simp
      have hd : dist a b < δ / L := ha
      have hdb : 0 ≤ dist a b := dist_nonneg
      calc |T a i - T b i| ≤ ν i * α * (A * euclNorm (a - b)) := h1
        _ ≤ ν i * α * (A * (Real.sqrt d * dist a b)) := by
            apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hA0)
            exact mul_nonneg (hν i).le hα.1.le
        _ = (ν i * α * A * Real.sqrt d) * dist a b := by ring
        _ ≤ L * dist a b := by apply mul_le_mul_of_nonneg_right (by linarith) hdb
        _ < L * (δ / L) := by apply mul_lt_mul_of_pos_left hd hLpos
        _ = δ := by field_simp
    have hcont : Continuous (fun p : (Fin d → ℝ) × (Fin d → ℝ) => |p.2 i - T p.1 i|) :=
      ((continuous_apply i).comp continuous_snd |>.sub ((hcontT i).comp continuous_fst)).abs
    have htend : Tendsto (fun n => (xs n, ys n)) atTop (𝓝 (x, y)) := hxs.prodMk_nhds hys
    have := (hcont.tendsto (x, y)).comp htend
    exact le_of_tendsto this (Eventually.of_forall (fun n => (mem_T ν hν T ε hε _ _).mp (hmem n) i))
