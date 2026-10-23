-- Prove2me | solution 1 for ApproxOLO.FullInfo.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-22T18:58:19.262274+00:00
-- url     : https://prove2.me/submissions/b44ab2d1-90c4-449f-8369-9870ebd45803

import Mathlib
import Definitions.Def_ApproxOLO_FullInfo_Model
import Theorems.Thm_LinearOptimization_ellipsoid_update_halfspace_volume

set_option autoImplicit false

namespace ApproxOLO.FullInfo.EuclideanProof

open Matrix
open scoped RealInnerProductSpace

lemma euclNorm_nonneg {d : ℕ} (x : Vec d) : 0 ≤ euclNorm x := Real.sqrt_nonneg _

lemma euclNorm_eq_norm {d : ℕ} (x : Vec d) :
    euclNorm x = ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [euclNorm, dotProduct, Real.norm_eq_abs, pow_two]

lemma dot_eq_inner {d : ℕ} (x y : Vec d) :
    x ⬝ᵥ y = inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 y) := by
  simp [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]

lemma euclNorm_sq {d : ℕ} (x : Vec d) : euclNorm x ^ 2 = x ⬝ᵥ x := by
  apply Real.sq_sqrt
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i))

lemma euclNorm_zero {d : ℕ} : euclNorm (0 : Vec d) = 0 := by simp [euclNorm]

lemma euclNorm_eq_zero {d : ℕ} (x : Vec d) : euclNorm x = 0 ↔ x = 0 := by
  rw [euclNorm_eq_norm, norm_eq_zero]
  exact WithLp.toLp_eq_zero 2

lemma euclNorm_sub_comm {d : ℕ} (x y : Vec d) : euclNorm (x - y) = euclNorm (y - x) := by
  simp only [euclNorm_eq_norm, WithLp.toLp_sub]
  exact norm_sub_rev _ _

lemma euclNorm_smul {d : ℕ} (a : ℝ) (x : Vec d) : euclNorm (a • x) = |a| * euclNorm x := by
  simp only [euclNorm_eq_norm, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

lemma euclNorm_neg {d : ℕ} (x : Vec d) : euclNorm (-x) = euclNorm x := by
  simp only [euclNorm_eq_norm, WithLp.toLp_neg, norm_neg]

lemma euclNorm_add_le {d : ℕ} (x y : Vec d) : euclNorm (x + y) ≤ euclNorm x + euclNorm y := by
  simpa only [euclNorm_eq_norm, WithLp.toLp_add] using
    norm_add_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 y)

lemma euclNorm_sub_le {d : ℕ} (x y : Vec d) : euclNorm (x - y) ≤ euclNorm x + euclNorm y := by
  simpa only [euclNorm_eq_norm, WithLp.toLp_sub] using
    norm_sub_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 y)

lemma abs_dot_le_norm_mul {d : ℕ} (x y : Vec d) : |x ⬝ᵥ y| ≤ euclNorm x * euclNorm y := by
  simpa only [euclNorm_eq_norm, dot_eq_inner] using
    abs_real_inner_le_norm (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 y)

lemma dot_le_norm_mul {d : ℕ} (x y : Vec d) : x ⬝ᵥ y ≤ euclNorm x * euclNorm y :=
  (le_abs_self _).trans (abs_dot_le_norm_mul x y)

lemma neg_norm_mul_le_dot {d : ℕ} (x y : Vec d) : -(euclNorm x * euclNorm y) ≤ x ⬝ᵥ y :=
  (abs_le.mp (abs_dot_le_norm_mul x y)).1

lemma euclNorm_sub_sq {d : ℕ} (x y : Vec d) :
    euclNorm (x - y) ^ 2 = euclNorm x ^ 2 + euclNorm y ^ 2 - 2 * (x ⬝ᵥ y) := by
  simp only [euclNorm_sq, sub_dotProduct, dotProduct_sub, dotProduct_comm y x]
  ring

lemma euclNorm_step_sq {d : ℕ} (x z w : Vec d) (eps : ℝ) :
    euclNorm (x - eps • w - z) ^ 2 = euclNorm (x - z) ^ 2 +
      eps ^ 2 * euclNorm w ^ 2 - 2 * eps * ((x - z) ⬝ᵥ w) := by
  have heq : x - eps • w - z = (x - z) - eps • w := by abel
  rw [heq, euclNorm_sub_sq]
  simp only [euclNorm_sq, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

end ApproxOLO.FullInfo.EuclideanProof

namespace ApproxOLO.FullInfo.EllipsoidProof

open Matrix MeasureTheory LinearOptimization EuclideanProof
open scoped ENNReal

/-- Euclidean balls in the canonical coordinate-vector model. -/
def euclBall {d : ℕ} (z : Vec d) (r : ℝ) : Set (Vec d) :=
  {y | euclNorm (y - z) ≤ r}

lemma euclBall_volume_eq {d : ℕ} (z : Vec d) (r : ℝ) :
    volume (euclBall z r) =
      volume (Metric.closedBall (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin d)) r) := by
  have heq : euclBall z r = (WithLp.toLp 2) ⁻¹'
      Metric.closedBall (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin d)) r := by
    ext y
    simp only [euclBall, Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall,
      dist_eq_norm, euclNorm_eq_norm, WithLp.toLp_sub]
  rw [heq]
  exact (PiLp.volume_preserving_toLp (Fin d)).measure_preimage
    measurableSet_closedBall.nullMeasurableSet

lemma euclBall_volume_scale {d : ℕ} (z : Vec d) (r : ℝ) (hr : 0 ≤ r) :
    volume (euclBall z r) = ENNReal.ofReal (r ^ d) * volume (euclBall (0 : Vec d) 1) := by
  simp only [euclBall_volume_eq, WithLp.toLp_zero]
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using
    Measure.addHaar_closedBall' (volume : Measure (EuclideanSpace ℝ (Fin d)))
      (WithLp.toLp 2 z) hr

lemma euclBall_unit_volume_pos {d : ℕ} : 0 < volume (euclBall (0 : Vec d) 1) := by
  rw [euclBall_volume_eq]
  exact Metric.measure_closedBall_pos volume _ zero_lt_one

lemma euclBall_unit_volume_lt_top {d : ℕ} : volume (euclBall (0 : Vec d) 1) < ⊤ := by
  rw [euclBall_volume_eq]
  exact (isCompact_closedBall _ _).measure_lt_top

lemma ellipsoid_zero_one {d : ℕ} :
    ellipsoid (0 : Vec d) (1 : Matrix (Fin d) (Fin d) ℝ) = euclBall 0 1 := by
  ext y
  simp only [ellipsoid, euclBall, Set.mem_ofPred_eq, sub_zero, inv_one,
    Matrix.one_mulVec]
  have hs := euclNorm_sq y
  have hp := euclNorm_nonneg y
  constructor <;> intro h <;> nlinarith

lemma run_volume_bound {d : ℕ} (hd : 2 ≤ d) (S : Set (Vec d)) (hS : S.Nonempty)
    (w : ℕ → Vec d) (D : ℕ → Matrix (Fin d) (Fin d) ℝ) (a : ℕ → Vec d) (N : ℕ)
    (hD : (D 0).PosDef) (hcover : S ⊆ ellipsoid (w 0) (D 0))
    (hw : ∀ k < N, w (k + 1) = ellipsoidUpdateCenter (w k) (D k) (a k))
    (hmat : ∀ k < N, D (k + 1) = ellipsoidUpdateMatrix (D k) (a k))
    (hcut : ∀ k < N, ∀ y ∈ S, a k ⬝ᵥ w k < a k ⬝ᵥ y) :
    S ⊆ ellipsoid (w N) (D N) ∧
      volume (ellipsoid (w N) (D N)) ≤
        ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((d : ℝ) + 1)))) ^ N *
          volume (ellipsoid (w 0) (D 0)) := by
  let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((d : ℝ) + 1))))
  have hinv : ∀ k ≤ N, (D k).PosDef ∧ S ⊆ ellipsoid (w k) (D k) ∧
      volume (ellipsoid (w k) (D k)) ≤ q ^ k * volume (ellipsoid (w 0) (D 0)) := by
    intro k hk
    induction k with
    | zero => exact ⟨hD, hcover, by simp⟩
    | succ k ih =>
      have hklt : k < N := Nat.lt_of_succ_le hk
      have ihk := ih (Nat.le_trans (Nat.le_succ k) hk)
      have ha : a k ≠ 0 := by
        intro haz
        obtain ⟨y, hy⟩ := hS
        have hc := hcut k hklt y hy
        simp [haz] at hc
      have hu := ellipsoid_update_halfspace_volume hd (w k) (D k) ihk.1 (a k) ha
      refine ⟨?_, ?_, ?_⟩
      · rw [hmat k hklt]
        exact hu.1
      · intro y hy
        rw [hw k hklt, hmat k hklt]
        exact hu.2.1 ⟨ihk.2.1 hy, (hcut k hklt y hy).le⟩
      · rw [hw k hklt, hmat k hklt]
        calc
          _ ≤ q * volume (ellipsoid (w k) (D k)) := hu.2.2.le
          _ ≤ q * (q ^ k * volume (ellipsoid (w 0) (D 0))) :=
            mul_le_mul_of_nonneg_left ihk.2.2 zero_le
          _ = _ := by rw [pow_succ]; ac_rfl
  exact (hinv N le_rfl).2

lemma margin_ball {d N : ℕ} (x h : Vec d) (v : Fin N → Vec d) (eps r : ℝ)
    (hh : euclNorm h = 1) (hr : r ≤ 1 / 2)
    (hbound : ∀ i, euclNorm (x - v i) * r ≤ eps / 2)
    (hmargin : ∀ i, 3 * eps < (x - v i) ⬝ᵥ h) :
    euclBall ((1 / 2 : ℝ) • h) r ⊆ euclBall 0 1 ∧
      ∀ y ∈ euclBall ((1 / 2 : ℝ) • h) r, ∀ i, eps < (x - v i) ⬝ᵥ y := by
  have hhalf : euclNorm ((1 / 2 : ℝ) • h) = 1 / 2 := by
    rw [euclNorm_smul, hh]
    norm_num
  constructor
  · intro y hy
    change euclNorm (y - 0) ≤ 1
    rw [sub_zero]
    have hn := euclNorm_add_le (y - (1 / 2 : ℝ) • h) ((1 / 2 : ℝ) • h)
    rw [sub_add_cancel, hhalf] at hn
    change euclNorm (y - (1 / 2 : ℝ) • h) ≤ r at hy
    linarith
  · intro y hy i
    change euclNorm (y - (1 / 2 : ℝ) • h) ≤ r at hy
    have hmul := mul_le_mul_of_nonneg_left hy (euclNorm_nonneg (x - v i))
    have hc := neg_norm_mul_le_dot (x - v i) (y - (1 / 2 : ℝ) • h)
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul] at hc
    linarith [hbound i, hmargin i]

noncomputable def cutDirection {d : ℕ} (O : Vec d → Vec d) (alpha R : ℝ)
    (x : Vec d) (eps : ℝ) (k : ℕ) : Vec d :=
  if (x - (ellOut O alpha R x eps k).1) ⬝ᵥ (ellIter O alpha R x eps k).1 < eps
  then x - (ellOut O alpha R x eps k).1 else -(ellIter O alpha R x eps k).1

lemma ellIter_succ {d : ℕ} (O : Vec d → Vec d) (alpha R : ℝ)
    (x : Vec d) (eps : ℝ) (k : ℕ) :
    ellIter O alpha R x eps (k + 1) = ellStep O alpha R x eps (ellIter O alpha R x eps k) := by
  exact Function.iterate_succ_apply' _ _ _

lemma ellIter_succ_of_miss {d : ℕ} (O : Vec d → Vec d) (alpha R : ℝ)
    (x : Vec d) (eps : ℝ) (k : ℕ) (hmiss : ¬ ellFeasibleAt O alpha R x eps k) :
    ellIter O alpha R x eps (k + 1) =
      (ellipsoidUpdateCenter (ellIter O alpha R x eps k).1 (ellIter O alpha R x eps k).2
        (cutDirection O alpha R x eps k),
       ellipsoidUpdateMatrix (ellIter O alpha R x eps k).2 (cutDirection O alpha R x eps k)) := by
  rw [ellIter_succ]
  unfold ellStep cutDirection ellOut
  dsimp only
  split_ifs with hc hn
  · rfl
  · rfl
  · exact (hmiss ⟨le_of_not_gt hn, le_of_not_gt hc⟩).elim

lemma cut_strict_on_ball {d N : ℕ} (O : Vec d → Vec d) (alpha R : ℝ)
    (x : Vec d) (eps : ℝ) (S : Set (Vec d))
    (hunit : S ⊆ euclBall 0 1)
    (hmargin : ∀ y ∈ S, ∀ i : Fin N, eps < (x - (ellOut O alpha R x eps i).1) ⬝ᵥ y)
    (hmiss : ∀ k < N, ¬ ellFeasibleAt O alpha R x eps k) :
    ∀ k < N, ∀ y ∈ S,
      cutDirection O alpha R x eps k ⬝ᵥ (ellIter O alpha R x eps k).1 <
        cutDirection O alpha R x eps k ⬝ᵥ y := by
  intro k hk y hy
  unfold cutDirection
  split_ifs with hc
  · exact hc.trans (hmargin y hy ⟨k, hk⟩)
  · have hn : 1 < euclNorm (ellIter O alpha R x eps k).1 := by
      by_contra hn
      exact hmiss k hk ⟨le_of_not_gt hn, le_of_not_gt hc⟩
    have hyunit : euclNorm y ≤ 1 := by
      simpa only [euclBall, Set.mem_ofPred_eq, sub_zero] using hunit hy
    have hcs := dot_le_norm_mul (ellIter O alpha R x eps k).1 y
    have hmul := mul_le_mul_of_nonneg_left hyunit
      (euclNorm_nonneg (ellIter O alpha R x eps k).1)
    have hs := euclNorm_sq (ellIter O alpha R x eps k).1
    simp only [neg_dotProduct]
    nlinarith

lemma large_margin_volume_lower {d : ℕ} (hd : 2 ≤ d) (O : Vec d → Vec d)
    (alpha R : ℝ) (x h : Vec d) (eps B : ℝ) (N : ℕ)
    (heps : 0 < eps) (hB : 0 < B) (hepsB : eps ≤ B) (hh : euclNorm h = 1)
    (hv : ∀ k < N, euclNorm (ellOut O alpha R x eps k).1 ≤ B)
    (hmargin : ∀ i : Fin N, 3 * eps < (x - (ellOut O alpha R x eps i).1) ⬝ᵥ h)
    (hmiss : ∀ k < N, ¬ ellFeasibleAt O alpha R x eps k) :
    (eps / (2 * (B + euclNorm x))) ^ d ≤
      Real.exp (-(N : ℝ) / (2 * ((d : ℝ) + 1))) := by
  let r : ℝ := eps / (2 * (B + euclNorm x))
  have hD : 0 < B + euclNorm x := by linarith [euclNorm_nonneg x]
  have hden : 0 < 2 * (B + euclNorm x) := by positivity
  have hr : 0 < r := div_pos heps hden
  have hrhalf : r ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith [euclNorm_nonneg x]
  have hbound (i : Fin N) : euclNorm (x - (ellOut O alpha R x eps i).1) * r ≤ eps / 2 := by
    have hnorm : euclNorm (x - (ellOut O alpha R x eps i).1) ≤ B + euclNorm x := by
      have hs := euclNorm_sub_le x (ellOut O alpha R x eps i).1
      linarith [hv i i.isLt]
    calc
      _ ≤ (B + euclNorm x) * r := mul_le_mul_of_nonneg_right hnorm hr.le
      _ = eps / 2 := by
        dsimp [r]
        field_simp
  have hball := margin_ball x h (fun i : Fin N => (ellOut O alpha R x eps i).1)
    eps r hh hrhalf hbound hmargin
  let S : Set (Vec d) := euclBall ((1 / 2 : ℝ) • h) r
  have hS : S.Nonempty := by
    refine ⟨(1 / 2 : ℝ) • h, ?_⟩
    change euclNorm ((1 / 2 : ℝ) • h - (1 / 2 : ℝ) • h) ≤ r
    simpa only [sub_self, euclNorm_zero] using hr.le
  have hcover : S ⊆ ellipsoid (ellIter O alpha R x eps 0).1
      (ellIter O alpha R x eps 0).2 := by
    simpa only [ellIter, Function.iterate_zero, id_eq, Prod.fst, Prod.snd,
      ellipsoid_zero_one] using hball.1
  have hmat0 : (ellIter O alpha R x eps 0).2.PosDef := by
    simpa only [ellIter, Function.iterate_zero, id_eq, Prod.snd] using
      (Matrix.PosDef.one : (1 : Matrix (Fin d) (Fin d) ℝ).PosDef)
  have hrun := run_volume_bound hd S hS
    (fun k => (ellIter O alpha R x eps k).1)
    (fun k => (ellIter O alpha R x eps k).2)
    (cutDirection O alpha R x eps) N hmat0 hcover
    (fun k hk => congrArg Prod.fst (ellIter_succ_of_miss O alpha R x eps k (hmiss k hk)))
    (fun k hk => congrArg Prod.snd (ellIter_succ_of_miss O alpha R x eps k (hmiss k hk)))
    (cut_strict_on_ball O alpha R x eps S hball.1 hball.2 hmiss)
  have hvol : volume S ≤
      ENNReal.ofReal (Real.exp (-(1 : ℝ) / (2 * ((d : ℝ) + 1)))) ^ N *
        volume (euclBall (0 : Vec d) 1) := by
    have hv' := (measure_mono hrun.1).trans hrun.2
    simpa only [ellIter, Function.iterate_zero, id_eq, Prod.fst, Prod.snd,
      ellipsoid_zero_one] using hv'
  change volume (euclBall ((1 / 2 : ℝ) • h) r) ≤ _ at hvol
  rw [euclBall_volume_scale _ r hr.le] at hvol
  have hcancel := (ENNReal.mul_le_mul_iff_left
    (ne_of_gt (euclBall_unit_volume_pos (d := d)))
    (ne_of_lt (euclBall_unit_volume_lt_top (d := d)))).mp hvol
  rw [← ENNReal.ofReal_pow (Real.exp_pos _).le] at hcancel
  have hreal := (ENNReal.ofReal_le_ofReal_iff (pow_nonneg (Real.exp_pos _).le N)).mp hcancel
  calc
    _ ≤ Real.exp (-(1 : ℝ) / (2 * ((d : ℝ) + 1))) ^ N := hreal
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end ApproxOLO.FullInfo.EllipsoidProof

namespace ApproxOLO.FullInfo.OracleProof

open Matrix EuclideanProof

lemma dot_nonneg {d : ℕ} (x y : Vec d) (hx : IsNonneg x) (hy : IsNonneg y) :
    0 ≤ x ⬝ᵥ y := Finset.sum_nonneg (fun i _ => mul_nonneg (hx i) (hy i))

lemma dot_nonpos {d : ℕ} (x y : Vec d) (hx : IsNonneg x) (hy : ∀ i, y i ≤ 0) :
    x ⬝ᵥ y ≤ 0 := Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hx i) (hy i))

lemma pos_nonneg {d : ℕ} (c : Vec d) : IsNonneg (posCoord c) := fun i => le_max_right (c i) 0
lemma neg_nonpos {d : ℕ} (c : Vec d) (i : Fin d) : negCoord c i ≤ 0 := min_le_right (c i) 0
lemma neg_neg_nonneg {d : ℕ} (c : Vec d) : IsNonneg (-negCoord c) :=
  fun i => neg_nonneg.mpr (neg_nonpos c i)

lemma coord_decomp {d : ℕ} (c : Vec d) : posCoord c + negCoord c = c := by
  ext i
  exact (max_add_min (c i) 0).trans (add_zero _)

lemma coord_orthogonal {d : ℕ} (c : Vec d) : posCoord c ⬝ᵥ negCoord c = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  change max (c i) 0 * min (c i) 0 = 0
  by_cases h : 0 ≤ c i
  · simp [max_eq_left h, min_eq_right h]
  · simp [max_eq_right (le_of_not_ge h), min_eq_left (le_of_not_ge h)]

lemma unitDir_norm_le {d : ℕ} (x : Vec d) : euclNorm (unitDir x) ≤ 1 := by
  by_cases hx : 0 < euclNorm x
  · rw [unitDir, if_pos hx, euclNorm_smul, abs_of_nonneg (inv_nonneg.mpr hx.le)]
    simp only [inv_mul_cancel₀ hx.ne', le_refl]
  · simp only [unitDir, if_neg hx, euclNorm_zero, zero_le_one]

lemma unitDir_nonneg {d : ℕ} (x : Vec d) (hx : IsNonneg x) : IsNonneg (unitDir x) := by
  unfold unitDir
  split_ifs with hp
  · intro i
    exact mul_nonneg (inv_nonneg.mpr (euclNorm_nonneg x)) (hx i)
  · intro i
    exact le_rfl

lemma unitDir_nonpos {d : ℕ} (x : Vec d) (hx : ∀ i, x i ≤ 0) :
    ∀ i, unitDir x i ≤ 0 := by
  unfold unitDir
  split_ifs with hp
  · intro i
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (euclNorm_nonneg x)) (hx i)
  · intro i
    exact le_rfl

lemma unitDir_dot_self {d : ℕ} (x : Vec d) : unitDir x ⬝ᵥ x = euclNorm x := by
  by_cases hx : 0 < euclNorm x
  · rw [unitDir, if_pos hx, smul_dotProduct, smul_eq_mul, ← euclNorm_sq]
    field_simp
  · have hz : x = 0 := (euclNorm_eq_zero x).mp (le_antisymm (le_of_not_gt hx) (euclNorm_nonneg x))
    subst x
    simp [euclNorm_zero]

lemma unitDir_dot_orthogonal {d : ℕ} (x y : Vec d) (hxy : x ⬝ᵥ y = 0) :
    unitDir x ⬝ᵥ y = 0 := by
  unfold unitDir
  split_ifs <;> simp [smul_dotProduct, hxy]

lemma unit_neg_dot {d : ℕ} (c : Vec d) : unitDir (negCoord c) ⬝ᵥ c = euclNorm (negCoord c) := by
  calc
    _ = unitDir (negCoord c) ⬝ᵥ (posCoord c + negCoord c) := by rw [coord_decomp]
    _ = _ := by rw [dotProduct_add, unitDir_dot_self,
    unitDir_dot_orthogonal _ _ (by rw [dotProduct_comm]; exact coord_orthogonal c), zero_add]

lemma unit_pos_dot {d : ℕ} (c : Vec d) : unitDir (posCoord c) ⬝ᵥ c = euclNorm (posCoord c) := by
  calc
    _ = unitDir (posCoord c) ⬝ᵥ (posCoord c + negCoord c) := by rw [coord_decomp]
    _ = _ := by rw [dotProduct_add, unitDir_dot_self,
      unitDir_dot_orthogonal _ _ (coord_orthogonal c), add_zero]

lemma dot_coord {d : ℕ} (x c : Vec d) : x ⬝ᵥ c = x ⬝ᵥ posCoord c + x ⬝ᵥ negCoord c := by
  rw [← dotProduct_add, coord_decomp]

lemma shifted_distance {d : ℕ} (s u : Vec d) (a : ℝ) (ha : 0 ≤ a)
    (hu : euclNorm u ≤ 1) : euclNorm (s - a • u - s) ≤ a := by
  have heq : s - a • u - s = -(a • u) := by abel
  rw [heq, euclNorm_neg, euclNorm_smul, abs_of_nonneg ha]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hu ha

lemma shifted_norm {d : ℕ} (s u : Vec d) (R a : ℝ) (hs : euclNorm s ≤ R)
    (ha : 0 ≤ a) (hu : euclNorm u ≤ 1) : euclNorm (s - a • u) ≤ R + a := by
  calc
    _ ≤ euclNorm s + euclNorm (a • u) := euclNorm_sub_le _ _
    _ = euclNorm s + a * euclNorm u := by rw [euclNorm_smul, abs_of_nonneg ha]
    _ ≤ R + a := by nlinarith

end ApproxOLO.FullInfo.OracleProof

open ApproxOLO.FullInfo ApproxOLO.FullInfo.EuclideanProof ApproxOLO.FullInfo.OracleProof Matrix

theorem oracle_properties {d : ℕ} (K Fs : Set (Vec d)) (R Fb C alpha : ℝ) (O : Vec d → Vec d)
    (hinst : IsInstance K Fs R Fb C) (halpha : 0 < alpha) (hO : IsApproxOracle K alpha O)
    (c : Vec d) :
    (extOracle O alpha R c).2 ∈ K ∧
    (∃ k ∈ K, euclNorm ((extOracle O alpha R c).1 - k) ≤ (1 + alpha) * R) ∧
    (∀ z ∈ K, (extOracle O alpha R c).1 ⬝ᵥ c ≤ (alpha • z) ⬝ᵥ c) ∧
    (∀ f ∈ Fs, (1 ≤ alpha → (extOracle O alpha R c).2 ⬝ᵥ f ≤ (extOracle O alpha R c).1 ⬝ᵥ f) ∧
      (alpha < 1 → (extOracle O alpha R c).1 ⬝ᵥ f ≤ (extOracle O alpha R c).2 ⬝ᵥ f)) ∧
    euclNorm (extOracle O alpha R c).1 ≤ (alpha + 2) * R := by
  obtain ⟨_, _, _, hKpos, hFpos, hR, _, _, hKnorm, _, _⟩ := hinst
  by_cases ha : 1 ≤ alpha
  · obtain ⟨hs, hmin, _⟩ := hO (posCoord c) (pos_nonneg c)
    simp only [extOracle, if_pos ha]
    refine ⟨hs, ⟨O (posCoord c), hs, ?_⟩, ?_, ?_, ?_⟩
    · have hb := shifted_distance (O (posCoord c)) (unitDir (negCoord c)) (alpha * R)
        (mul_nonneg halpha.le hR.le) (unitDir_norm_le _)
      linarith
    · intro z hz
      have hpos := hmin ha z hz
      have hsneg := dot_nonpos (O (posCoord c)) (negCoord c) (hKpos _ hs) (neg_nonpos c)
      have hlow : -(R * euclNorm (negCoord c)) ≤ z ⬝ᵥ negCoord c := by
        have hcs := neg_norm_mul_le_dot z (negCoord c)
        have hb := mul_le_mul_of_nonneg_right (hKnorm z hz) (euclNorm_nonneg (negCoord c))
        linarith
      have halow := mul_le_mul_of_nonneg_left hlow halpha.le
      simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, unit_neg_dot]
      rw [dot_coord (O (posCoord c)) c, dot_coord z c]
      nlinarith
    · intro f hf
      constructor
      · intro _
        have huf : unitDir (negCoord c) ⬝ᵥ f ≤ 0 := by
          rw [dotProduct_comm]
          exact dot_nonpos f _ (hFpos f hf) (unitDir_nonpos _ (neg_nonpos c))
        simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
        have := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg halpha.le hR.le) huf
        linarith
      · intro hlt
        exact (not_lt_of_ge ha hlt).elim
    · have hb := shifted_norm (O (posCoord c)) (unitDir (negCoord c)) R (alpha * R)
        (hKnorm _ hs) (mul_nonneg halpha.le hR.le) (unitDir_norm_le _)
      linarith
  · have ha' : alpha < 1 := lt_of_not_ge ha
    obtain ⟨hs, _, hmax⟩ := hO (-negCoord c) (neg_neg_nonneg c)
    simp only [extOracle, if_neg ha]
    refine ⟨hs, ⟨O (-negCoord c), hs, ?_⟩, ?_, ?_, ?_⟩
    · have hb := shifted_distance (O (-negCoord c)) (unitDir (posCoord c)) R hR.le (unitDir_norm_le _)
      nlinarith
    · intro z hz
      have hneg : O (-negCoord c) ⬝ᵥ negCoord c ≤ alpha * (z ⬝ᵥ negCoord c) := by
        have ho := hmax ha' z hz
        simp only [dotProduct_neg] at ho
        linarith
      have hspos : O (-negCoord c) ⬝ᵥ posCoord c ≤ R * euclNorm (posCoord c) :=
        (dot_le_norm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (hKnorm _ hs) (euclNorm_nonneg _))
      have hzpos := dot_nonneg z (posCoord c) (hKpos z hz) (pos_nonneg c)
      have hap := mul_nonneg halpha.le hzpos
      simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul, unit_pos_dot]
      rw [dot_coord (O (-negCoord c)) c, dot_coord z c]
      nlinarith
    · intro f hf
      constructor
      · intro hge
        exact (ha hge).elim
      · intro _
        have huf := dot_nonneg (unitDir (posCoord c)) f (unitDir_nonneg _ (pos_nonneg c)) (hFpos f hf)
        simp only [sub_dotProduct, smul_dotProduct, smul_eq_mul]
        have := mul_nonneg hR.le huf
        linarith
    · have hb := shifted_norm (O (-negCoord c)) (unitDir (posCoord c)) R R
        (hKnorm _ hs) hR.le (unitDir_norm_le _)
      nlinarith

namespace ApproxOLO.FullInfo.DistanceProof
open Matrix

lemma quadratic_direction_nonneg (A B : ℝ) (hB : 0 ≤ B)
    (h : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ t * (2 * A + t * B)) : 0 ≤ A := by
  by_contra hA
  have hA' : A < 0 := lt_of_not_ge hA
  let t : ℝ := min 1 (-A / (B + 1))
  have hden : 0 < B + 1 := by linarith
  have ht : 0 < t := lt_min zero_lt_one (div_pos (neg_pos.mpr hA') hden)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htB : t * (B + 1) ≤ -A := (le_div_iff₀ hden).mp (min_le_right _ _)
  have hp : 0 ≤ 2 * A + t * B := nonneg_of_mul_nonneg_right (h t ht.le ht1) ht
  nlinarith

lemma simplex_opt_dot_variational {d N : ℕ} (x : Vec d) (v : Fin N → Vec d)
    (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i) (hasum : ∑ i, a i = 1)
    (hopt : ∀ b : Fin N → ℝ, (∀ i, 0 ≤ b i) → ∑ i, b i = 1 →
      (∑ i, a i • v i - x) ⬝ᵥ (∑ i, a i • v i - x) ≤
      (∑ i, b i • v i - x) ⬝ᵥ (∑ i, b i • v i - x)) (i : Fin N) :
    0 ≤ (∑ j, a j • v j - x) ⬝ᵥ (v i - ∑ j, a j • v j) := by
  classical
  let p : Vec d := ∑ j, a j • v j
  let r : Vec d := p - x
  let q : Vec d := v i - p
  change 0 ≤ r ⬝ᵥ q
  apply quadratic_direction_nonneg (r ⬝ᵥ q) (q ⬝ᵥ q)
  · exact Finset.sum_nonneg (fun j _ => mul_self_nonneg (q j))
  intro t ht ht1
  let b : Fin N → ℝ := fun j => (1-t)*a j + if j=i then t else 0
  have hb (j : Fin N) : 0 ≤ b j := by
    dsimp [b]
    exact add_nonneg (mul_nonneg (by linarith) (ha j)) (by split_ifs <;> positivity)
  have hbsum : ∑ j, b j = 1 := by
    simp [b, Finset.sum_add_distrib, ← Finset.mul_sum, hasum]
  have hbpoint : ∑ j, b j • v j = (1-t) • p + t • v i := by
    dsimp [b, p]
    simp [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum, ite_smul]
  have hbr : (∑ j, b j • v j) - x = r + t • q := by
    rw [hbpoint]
    ext l
    simp only [r, q, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hh := hopt b hb hbsum
  change r ⬝ᵥ r ≤ _ at hh
  rw [hbr] at hh
  have he : (r + t • q) ⬝ᵥ (r + t • q) =
      r ⬝ᵥ r + t * (2 * (r ⬝ᵥ q) + t * (q ⬝ᵥ q)) := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm q r]
    ring
  rw [he] at hh
  linarith

end ApproxOLO.FullInfo.DistanceProof

namespace ApproxOLO.FullInfo.DistanceProof
open Matrix EuclideanProof

lemma simplex_opt_variational {d N : ℕ} (x : Vec d) (v : Fin N → Vec d)
    (a : Fin N → ℝ) (ha : IsSimplexOpt v x a) (i : Fin N) :
    0 ≤ (∑ j, a j • v j - x) ⬝ᵥ (v i - ∑ j, a j • v j) := by
  apply simplex_opt_dot_variational x v a ha.1 ha.2.1 _ i
  intro b hb hbsum
  have h := ha.2.2 b hb hbsum
  simp only [euclNorm_sq] at h
  linarith

end ApproxOLO.FullInfo.DistanceProof

open ApproxOLO.FullInfo Matrix

theorem simplex_distance_bound {d N : ℕ} (hN : 1 ≤ N) (x : Vec d) (v : Fin N → Vec d) (eps : ℝ)
    (heps : 0 < eps) (hmin : ∀ w : Vec d, euclNorm w = 1 → ∃ i, (x - v i) ⬝ᵥ w ≤ eps)
    (a : Fin N → ℝ) (ha : IsSimplexOpt v x a) :
    euclNorm (∑ i, a i • v i - x) ≤ eps := by
  have _hN := hN
  let p : Vec d := ∑ i, a i • v i
  change euclNorm (p-x) ≤ eps
  by_contra hbound
  have hgap : eps < euclNorm (p-x) := lt_of_not_ge hbound
  let s : ℝ := euclNorm (x-p)
  have hs : 0 < s := by
    dsimp [s]
    rw [EuclideanProof.euclNorm_sub_comm]
    linarith
  have hunit : euclNorm (s⁻¹ • (x-p)) = 1 := by
    rw [EuclideanProof.euclNorm_smul, abs_of_pos (inv_pos.mpr hs)]
    change s⁻¹ * s = 1
    exact inv_mul_cancel₀ hs.ne'
  obtain ⟨i, hi⟩ := hmin (s⁻¹ • (x-p)) hunit
  have hvar : 0 ≤ (p-x) ⬝ᵥ (v i-p) := DistanceProof.simplex_opt_variational x v a ha i
  have hrel : (x-v i) ⬝ᵥ (x-p) =
      (x-p) ⬝ᵥ (x-p) + (p-x) ⬝ᵥ (v i-p) := by
    simp only [sub_dotProduct, dotProduct_sub]
    rw [dotProduct_comm (v i) x, dotProduct_comm (v i) p, dotProduct_comm p x]
    ring
  have hlo : s^2 ≤ (x-v i) ⬝ᵥ (x-p) := by
    rw [hrel]
    have hsq : s^2 = (x-p) ⬝ᵥ (x-p) := EuclideanProof.euclNorm_sq (x-p)
    linarith
  rw [dotProduct_smul, smul_eq_mul] at hi
  have hscale := mul_le_mul_of_nonneg_left hi hs.le
  rw [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at hscale
  have hgap' : eps < s := by
    dsimp [s]
    rw [EuclideanProof.euclNorm_sub_comm]
    exact hgap
  have hprod := mul_pos hs (sub_pos.mpr hgap')
  nlinarith

namespace ApproxOLO.FullInfo.LogBoundProof

/-- A scalar estimate converting the iteration threshold into strict volume decrease. -/
theorem log_iteration_bound (d N : ℕ) (hd : 2 ≤ d) (A eps D : ℝ)
    (hA : 0 < A) (heps : 0 < eps) (hsmall : 3 * eps < 2 * A)
    (hD : 0 < D) (hDbnd : D ≤ 2 * A)
    (hN : (100 : ℝ) * (d : ℝ)^2 * Real.log (A / eps) ≤ (N : ℝ)) :
    Real.exp (-(N : ℝ) / (2 * ((d : ℝ) + 1))) < (eps / (2 * D))^d := by
  let L : ℝ := Real.log (A / eps)
  have hratio : eps / A < (2 : ℝ) / 3 := by
    apply (div_lt_iff₀ hA).2
    linarith
  have hloglower := Real.one_sub_inv_le_log_of_pos (div_pos hA heps)
  rw [inv_div] at hloglower
  have hL : (1 : ℝ) / 3 < L := by
    dsimp [L]
    linarith
  have hLpos : 0 < L := by linarith
  have hlog4 : Real.log 4 ≤ (3 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have harg : 2 * D / eps ≤ 4 * (A / eps) := by
    calc
      2 * D / eps ≤ (4 * A) / eps :=
        div_le_div_of_nonneg_right (by linarith) heps.le
      _ = 4 * (A / eps) := by ring
  have hlogupper := Real.log_le_log (div_pos (mul_pos (by norm_num) hD) heps) harg
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (div_pos hA heps).ne'] at hlogupper
  have hlogten : Real.log (2 * D / eps) < 10 * L := by
    dsimp [L] at hL ⊢
    linarith
  have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hden : 0 < 2 * ((d : ℝ) + 1) := by positivity
  have hcoef : 20 * (d : ℝ) * ((d : ℝ) + 1) < 100 * (d : ℝ)^2 := by
    nlinarith
  have hmul := mul_lt_mul_of_pos_right hcoef hLpos
  have hquot : 10 * (d : ℝ) * L < (N : ℝ) / (2 * ((d : ℝ) + 1)) := by
    apply (lt_div_iff₀ hden).2
    change 100 * (d : ℝ)^2 * L ≤ (N : ℝ) at hN
    nlinarith
  have htotal : (d : ℝ) * Real.log (2 * D / eps) <
      (N : ℝ) / (2 * ((d : ℝ) + 1)) := by
    calc
      (d : ℝ) * Real.log (2 * D / eps) < (d : ℝ) * (10 * L) :=
        mul_lt_mul_of_pos_left hlogten hdpos
      _ = 10 * (d : ℝ) * L := by ring
      _ < (N : ℝ) / (2 * ((d : ℝ) + 1)) := hquot
  have hbase : 0 < eps / (2 * D) := div_pos heps (mul_pos (by norm_num) hD)
  have hinv : Real.log (eps / (2 * D)) = - Real.log (2 * D / eps) := by
    rw [Real.log_div heps.ne' (mul_pos (by norm_num) hD).ne',
      Real.log_div (mul_pos (by norm_num) hD).ne' heps.ne']
    ring
  rw [← Real.exp_log (pow_pos hbase d)]
  apply Real.exp_lt_exp.mpr
  rw [Real.log_pow, hinv, neg_div, mul_neg]
  exact neg_lt_neg htotal

end ApproxOLO.FullInfo.LogBoundProof

namespace ApproxOLO.FullInfo.EllipsoidProof

open Matrix EuclideanProof

lemma finite_direction_certificate {d : ℕ} (hd : 2 ≤ d)
    (K Fs : Set (Vec d)) (R Fb C alpha : ℝ) (O : Vec d → Vec d) (x : Vec d)
    (eps : ℝ) (N : ℕ) (hinst : IsInstance K Fs R Fb C) (halpha : 0 < alpha)
    (hO : IsApproxOracle K alpha O) (heps : 0 < eps) (hepsB : eps ≤ (alpha + 2) * R)
    (hN : 1 ≤ N)
    (hiterations : (100 : ℝ) * (d : ℝ) ^ 2 *
      Real.log (((alpha + 1) * R + euclNorm x) / eps) ≤ (N : ℝ))
    (hmiss : ∀ k < N, ¬ ellFeasibleAt O alpha R x eps k) :
    ∀ h : Vec d, euclNorm h = 1 →
      ∃ i : Fin N, (x - (ellOut O alpha R x eps i).1) ⬝ᵥ h ≤ 3 * eps := by
  classical
  intro h hh
  by_contra hbad
  push Not at hbad
  let B : ℝ := (alpha + 2) * R
  let A : ℝ := (alpha + 1) * R + euclNorm x
  let D : ℝ := B + euclNorm x
  have hR : 0 < R := hinst.2.2.2.2.2.1
  have hB : 0 < B := mul_pos (by linarith) hR
  have hA : 0 < A := add_pos_of_pos_of_nonneg
    (mul_pos (by linarith) hR) (euclNorm_nonneg x)
  have hD : 0 < D := add_pos_of_pos_of_nonneg hB (euclNorm_nonneg x)
  have hDbnd : D ≤ 2 * A := by
    dsimp [D, B, A]
    nlinarith [euclNorm_nonneg x, mul_pos halpha hR]
  have hv (k : ℕ) (_hk : k < N) : euclNorm (ellOut O alpha R x eps k).1 ≤ B :=
    (oracle_properties K Fs R Fb C alpha O hinst halpha hO
      (-(ellIter O alpha R x eps k).1)).2.2.2.2
  let i₀ : Fin N := ⟨0, by omega⟩
  have hsmall : 3 * eps < 2 * A := by
    have hgap := hbad i₀
    have hcs := dot_le_norm_mul (x - (ellOut O alpha R x eps i₀).1) h
    rw [hh, mul_one] at hcs
    have htri := euclNorm_sub_le x (ellOut O alpha R x eps i₀).1
    have hv₀ := hv i₀ i₀.isLt
    dsimp [D] at hDbnd
    linarith
  have hlower := large_margin_volume_lower hd O alpha R x h eps B N heps hB hepsB hh
    hv hbad hmiss
  have hupper := LogBoundProof.log_iteration_bound d N hd A eps D hA heps hsmall hD
    hDbnd hiterations
  exact (not_lt_of_ge hlower) hupper

lemma feasible_is_separator {d : ℕ} (K Fs : Set (Vec d)) (R Fb C alpha : ℝ)
    (O : Vec d → Vec d) (x : Vec d) (eps : ℝ)
    (hinst : IsInstance K Fs R Fb C) (halpha : 0 < alpha)
    (hO : IsApproxOracle K alpha O) (k : ℕ)
    (hfeas : ellFeasibleAt O alpha R x eps k) :
    (∀ z ∈ K, eps ≤ (x - alpha • z) ⬝ᵥ (ellIter O alpha R x eps k).1) ∧
      euclNorm (ellIter O alpha R x eps k).1 ≤ 1 := by
  refine ⟨?_, hfeas.1⟩
  intro z hz
  have ho := (oracle_properties K Fs R Fb C alpha O hinst halpha hO
    (-(ellIter O alpha R x eps k).1)).2.2.1 z hz
  have hf := hfeas.2
  change eps ≤ (x - (extOracle O alpha R (-(ellIter O alpha R x eps k).1)).1) ⬝ᵥ
    (ellIter O alpha R x eps k).1 at hf
  simp only [dotProduct_neg] at ho
  simp only [sub_dotProduct] at hf ⊢
  linarith

end ApproxOLO.FullInfo.EllipsoidProof

open ApproxOLO.FullInfo Matrix

/-- The universal constant 100 suffices for the canonical ellipsoid run. -/
theorem solution : ∃ c : ℝ, 0 < c ∧ ∀ (d : ℕ), 2 ≤ d →
    ∀ (K Fs : Set (Vec d)) (R Fb C alpha : ℝ) (O : Vec d → Vec d) (x : Vec d) (eps : ℝ)
      (N : ℕ),
    IsInstance K Fs R Fb C → 0 < alpha → IsApproxOracle K alpha O →
    0 < eps → eps ≤ (alpha + 2) * R → 1 ≤ N →
    c * (d : ℝ) ^ 2 * Real.log (((alpha + 1) * R + euclNorm x) / eps) ≤ (N : ℝ) →
    (∀ k < N, ellFeasibleAt O alpha R x eps k →
      (∀ z ∈ K, eps ≤ (x - alpha • z) ⬝ᵥ (ellIter O alpha R x eps k).1) ∧
        euclNorm (ellIter O alpha R x eps k).1 ≤ 1) ∧
    ((∀ k < N, ¬ ellFeasibleAt O alpha R x eps k) →
      ∀ a : Fin N → ℝ, IsSimplexOpt (fun i => (ellOut O alpha R x eps i).1) x a →
        euclNorm (x - ∑ i, a i • (ellOut O alpha R x eps i).1) ≤ 3 * eps) := by
  refine ⟨100, by norm_num, ?_⟩
  intro d hd K Fs R Fb C alpha O x eps N hinst halpha hO heps hepsB hN hiterations
  constructor
  · intro k _hk hfeas
    exact EllipsoidProof.feasible_is_separator K Fs R Fb C alpha O x eps hinst halpha hO k hfeas
  · intro hmiss a ha
    have hcert := EllipsoidProof.finite_direction_certificate hd K Fs R Fb C alpha O x eps N
      hinst halpha hO heps hepsB hN hiterations hmiss
    have hdist := simplex_distance_bound hN x (fun i : Fin N => (ellOut O alpha R x eps i).1)
      (3 * eps) (by positivity) hcert a ha
    rwa [EuclideanProof.euclNorm_sub_comm] at hdist
