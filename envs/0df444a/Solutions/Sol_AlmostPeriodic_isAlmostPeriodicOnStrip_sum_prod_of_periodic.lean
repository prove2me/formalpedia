-- Prove2me | solution 1 for AlmostPeriodic.isAlmostPeriodicOnStrip_sum_prod_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @WalrusPaul
-- created : 2026-11-22T18:54:17.334056+00:00
-- url     : https://prove2.me/submissions/012bab7c-24e7-4b72-b527-304e24ac40bf

import Mathlib
import Definitions.Def_AlmostPeriodic_AnalyticStrip

open Filter Topology

set_option autoImplicit false

open AlmostPeriodic

namespace AlmostPeriodicSumProdAux

/-- A vertical period `P` on the strip gives every integer multiple `n * P` as a period. -/
lemma int_period (f : ℂ → ℂ) (P a b : ℝ)
    (hper : ∀ z : ℂ, a < z.re → z.re < b → f (z + (P : ℂ) * Complex.I) = f z) :
    ∀ n : ℤ, ∀ z : ℂ, a < z.re → z.re < b →
      f (z + (n : ℂ) * (P : ℂ) * Complex.I) = f z := by
  intro n
  induction n using Int.induction_on with
  | zero => intro z _ _; simp
  | succ i ih =>
    intro z h1 h2
    have hre : (z + ((i : ℤ) : ℂ) * (P : ℂ) * Complex.I).re = z.re := by simp
    have := hper (z + ((i : ℤ) : ℂ) * (P : ℂ) * Complex.I) (by rw [hre]; exact h1)
      (by rw [hre]; exact h2)
    rw [← ih z h1 h2, ← this]
    congr 1
    push_cast; ring
  | pred i ih =>
    intro z h1 h2
    have hre : (z + ((-(i : ℤ) - 1 : ℤ) : ℂ) * (P : ℂ) * Complex.I).re = z.re := by simp
    have := hper (z + ((-(i : ℤ) - 1 : ℤ) : ℂ) * (P : ℂ) * Complex.I) (by rw [hre]; exact h1)
      (by rw [hre]; exact h2)
    rw [← this, ← ih z h1 h2]
    congr 1
    push_cast; ring

/-- Reduction of a point modulo the vertical period. -/
lemma reduce (f : ℂ → ℂ) (P a b : ℝ) (hP : P ≠ 0)
    (hper : ∀ z : ℂ, a < z.re → z.re < b → f (z + (P : ℂ) * Complex.I) = f z) (z : ℂ) :
    ∃ w : ℂ, w.re = z.re ∧ |w.im| ≤ |P| ∧
      ∀ h : ℝ, a < z.re → z.re < b →
        f (z + (h : ℂ) * Complex.I) = f (w + (h : ℂ) * Complex.I) := by
  refine ⟨z - ((⌊z.im / P⌋ : ℤ) : ℂ) * (P : ℂ) * Complex.I, by simp, ?_, ?_⟩
  · have him : (z - ((⌊z.im / P⌋ : ℤ) : ℂ) * (P : ℂ) * Complex.I).im
        = P * Int.fract (z.im / P) := by
      rw [← Int.self_sub_floor, mul_sub, mul_div_cancel₀ _ hP]
      simp
      ring
    rw [him, abs_mul, abs_of_nonneg (Int.fract_nonneg (z.im / P))]
    exact mul_le_of_le_one_right (abs_nonneg _) (Int.fract_lt_one _).le
  · intro h h1 h2
    have hre : (z - ((⌊z.im / P⌋ : ℤ) : ℂ) * (P : ℂ) * Complex.I + (h : ℂ) * Complex.I).re
        = z.re := by simp
    have := int_period f P a b hper ⌊z.im / P⌋
      (z - ((⌊z.im / P⌋ : ℤ) : ℂ) * (P : ℂ) * Complex.I + (h : ℂ) * Complex.I)
      (by rw [hre]; exact h1) (by rw [hre]; exact h2)
    rw [← this]
    congr 1
    ring

/-- Boundedness and vertical uniform continuity on a closed substrip. -/
lemma unif_and_bound (f : ℂ → ℂ) (P a b : ℝ) (hP : P ≠ 0)
    (hc : ContinuousOn f {z : ℂ | a < z.re ∧ z.re < b})
    (hper : ∀ z : ℂ, a < z.re → z.re < b → f (z + (P : ℂ) * Complex.I) = f z)
    (α β : ℝ) (hα : a < α) (hβ : β < b) :
    (∃ M : ℝ, ∀ z : ℂ, α ≤ z.re → z.re ≤ β → ‖f z‖ ≤ M) ∧
    (∀ δ : ℝ, 0 < δ → ∃ η > 0, ∀ z : ℂ, α ≤ z.re → z.re ≤ β → ∀ h : ℝ, |h| < η →
        ‖f (z + (h : ℂ) * Complex.I) - f z‖ < δ) := by
  set C : Set ℂ := Set.Icc α β ×ℂ Set.Icc (-(|P| + 1)) (|P| + 1) with hCdef
  have hC : IsCompact C := (isCompact_Icc).reProdIm isCompact_Icc
  have hCS : C ⊆ {z : ℂ | a < z.re ∧ z.re < b} := by
    intro z hz
    rw [hCdef, Complex.mem_reProdIm] at hz
    exact ⟨lt_of_lt_of_le hα hz.1.1, lt_of_le_of_lt hz.1.2 hβ⟩
  have hcC : ContinuousOn f C := hc.mono hCS
  have memC : ∀ w : ℂ, α ≤ w.re → w.re ≤ β → |w.im| ≤ |P| + 1 → w ∈ C := by
    intro w h1 h2 h3
    rw [hCdef, Complex.mem_reProdIm]
    exact ⟨⟨h1, h2⟩, abs_le.1 h3⟩
  have key : ∀ z : ℂ, α ≤ z.re → z.re ≤ β → ∃ w : ℂ, w ∈ C ∧ f z = f w ∧
      ∀ h : ℝ, |h| ≤ 1 → (w + (h : ℂ) * Complex.I) ∈ C ∧
        f (z + (h : ℂ) * Complex.I) = f (w + (h : ℂ) * Complex.I) := by
    intro z h1 h2
    obtain ⟨w, hwre, hwim, hw⟩ := reduce f P a b hP hper z
    have ha : a < z.re := lt_of_lt_of_le hα h1
    have hb : z.re < b := lt_of_le_of_lt h2 hβ
    refine ⟨w, memC w (hwre ▸ h1) (hwre ▸ h2) (by linarith), ?_, ?_⟩
    · have := hw 0 ha hb
      simpa using this
    · intro h hh
      refine ⟨memC _ (by simp [hwre, h1]) (by simp [hwre, h2]) ?_, hw h ha hb⟩
      have e : (w + (h : ℂ) * Complex.I).im = w.im + h := by simp
      rw [e]
      calc |w.im + h| ≤ |w.im| + |h| := abs_add_le _ _
        _ ≤ |P| + 1 := by linarith
  constructor
  · obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcC
    refine ⟨M, fun z h1 h2 => ?_⟩
    obtain ⟨w, hwC, hfw, -⟩ := key z h1 h2
    rw [hfw]; exact hM w hwC
  · intro δ hδ
    obtain ⟨η0, hη0, hU⟩ :=
      Metric.uniformContinuousOn_iff.1 (hC.uniformContinuousOn_of_continuous hcC) δ hδ
    refine ⟨min η0 1, lt_min hη0 one_pos, fun z h1 h2 h hh => ?_⟩
    obtain ⟨w, hwC, hfw, hwh⟩ := key z h1 h2
    obtain ⟨hwhC, hfwh⟩ := hwh h (le_trans hh.le (min_le_right _ _))
    rw [hfw, hfwh, ← dist_eq_norm]
    apply hU _ hwhC _ hwC
    have e : dist (w + (h : ℂ) * Complex.I) w = |h| := by
      rw [dist_eq_norm]; simp
    rw [e]
    exact lt_of_lt_of_le hh (min_le_left _ _)

/-- Simultaneous approximation: shifts that are close to integer multiples of finitely many
periods form a relatively dense set. -/
lemma simul_approx {κ : Type*} [Fintype κ] (Q : κ → ℝ) (c : ℝ) (hc : 0 < c) :
    ∃ L > 0, ∀ a : ℝ, ∃ τ ∈ Set.Icc a (a + L), ∀ j, ∃ n : ℤ, |τ / Q j - n| < c := by
  let v : ℝ → (κ → ℝ) := fun t j => Int.fract (t / Q j)
  have hsub : Set.range v ⊆ Metric.closedBall 0 1 := by
    rintro _ ⟨t, rfl⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro j
    simp only [v, Real.norm_eq_abs]
    rw [abs_of_nonneg (Int.fract_nonneg _)]
    exact (Int.fract_lt_one _).le
  have hcpt : IsCompact (closure (Set.range v)) :=
    (Metric.isBounded_closedBall.subset hsub).isCompact_closure
  have hcov : closure (Set.range v) ⊆ ⋃ t : ℝ, Metric.ball (v t) c := by
    intro x hx
    obtain ⟨y, ⟨t, rfl⟩, hxy⟩ := Metric.mem_closure_iff.1 hx c hc
    exact Set.mem_iUnion.2 ⟨t, by rw [Metric.mem_ball]; exact hxy⟩
  obtain ⟨F, hF⟩ := hcpt.elim_finite_subcover (fun t => Metric.ball (v t) c)
    (fun _ => Metric.isOpen_ball) hcov
  set C : ℝ := ∑ t ∈ F, |t| with hCdef
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun t _ => abs_nonneg t)
  have hCt : ∀ t ∈ F, |t| ≤ C := fun t ht =>
    Finset.single_le_sum (f := fun t => |t|) (fun t _ => abs_nonneg t) ht
  refine ⟨2 * C + 1, by linarith, fun a => ?_⟩
  have hmem : v (a + C) ∈ closure (Set.range v) := subset_closure ⟨a + C, rfl⟩
  have := hF hmem
  rw [Set.mem_iUnion₂] at this
  obtain ⟨t, htF, ht⟩ := this
  have htC := abs_le.1 (hCt t htF)
  refine ⟨a + C - t, ⟨by linarith, by linarith⟩, fun j => ?_⟩
  refine ⟨⌊(a + C) / Q j⌋ - ⌊t / Q j⌋, ?_⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hc] at ht
  have hj := ht j
  simp only [v, Real.dist_eq] at hj
  have e : (a + C - t) / Q j - ((⌊(a + C) / Q j⌋ - ⌊t / Q j⌋ : ℤ) : ℝ)
      = Int.fract ((a + C) / Q j) - Int.fract (t / Q j) := by
    simp only [← Int.self_sub_floor, sub_div]; push_cast; ring
  rw [e]; exact hj

lemma exists_pos_le {κ : Type*} [Finite κ] (g : κ → ℝ) (hg : ∀ j, 0 < g j) :
    ∃ c > 0, ∀ j, c ≤ g j := by
  rcases isEmpty_or_nonempty κ with h | h
  · exact ⟨1, one_pos, fun j => (IsEmpty.false j).elim⟩
  · obtain ⟨j0, hj0⟩ := Finite.exists_min g
    exact ⟨g j0, hg j0, hj0⟩

lemma relDense_mono {A B : Set ℝ} (hA : IsRelativelyDense A) (hAB : A ⊆ B) :
    IsRelativelyDense B := by
  obtain ⟨L, hL, h⟩ := hA
  exact ⟨L, hL, fun a => (h a).mono (Set.inter_subset_inter_left _ hAB)⟩

/-- A continuous function of finitely many vertically periodic functions has relatively dense
sets of almost periods on every closed substrip. -/
lemma lemD {κ : Type*} [Fintype κ] (f : κ → ℂ → ℂ) (P : κ → ℝ) (a b : ℝ)
    (hc : ∀ j, ContinuousOn (f j) {z : ℂ | a < z.re ∧ z.re < b})
    (hP : ∀ j, P j ≠ 0)
    (hper : ∀ j, ∀ z : ℂ, a < z.re → z.re < b → f j (z + (P j : ℂ) * Complex.I) = f j z)
    (Φ : (κ → ℂ) → ℂ) (hΦ : Continuous Φ) (α β : ℝ) (hα : a < α) (hβ : β < b)
    (ε : ℝ) (hε : 0 < ε) :
    IsRelativelyDense {τ : ℝ | ∀ z : ℂ, α ≤ z.re → z.re ≤ β →
      ‖Φ (fun j => f j (z + (τ : ℂ) * Complex.I)) - Φ (fun j => f j z)‖ ≤ ε} := by
  have hUB := fun j => unif_and_bound (f j) (P j) a b (hP j) (hc j) (hper j) α β hα hβ
  choose M hM using fun j => (hUB j).1
  set M0 : ℝ := ∑ j, |M j| with hM0def
  have hM0 : 0 ≤ M0 := Finset.sum_nonneg (fun j _ => abs_nonneg (M j))
  have hbound : ∀ z : ℂ, α ≤ z.re → z.re ≤ β →
      (fun j => f j z) ∈ Metric.closedBall (0 : κ → ℂ) M0 := by
    intro z h1 h2
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hM0]
    intro j
    calc ‖f j z‖ ≤ M j := hM j z h1 h2
      _ ≤ |M j| := le_abs_self _
      _ ≤ M0 := Finset.single_le_sum (f := fun j => |M j|) (fun j _ => abs_nonneg _)
          (Finset.mem_univ j)
  obtain ⟨δ, hδ, hΦU⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : κ → ℂ) M0).uniformContinuousOn_of_continuous
      hΦ.continuousOn) ε hε
  choose η hη hηU using fun j => (hUB j).2 δ hδ
  obtain ⟨c, hc0, hcle⟩ := exists_pos_le (fun j => η j / |P j|)
    (fun j => div_pos (hη j) (abs_pos.2 (hP j)))
  obtain ⟨L, hL, hLa⟩ := simul_approx P c hc0
  refine ⟨L, hL, fun a0 => ?_⟩
  obtain ⟨τ, hτI, hτ⟩ := hLa a0
  refine ⟨τ, ?_, hτI⟩
  rw [Set.mem_ofPred_eq]
  intro z h1 h2
  have hz' : α ≤ (z + (τ : ℂ) * Complex.I).re := by simp [h1]
  have hz'' : (z + (τ : ℂ) * Complex.I).re ≤ β := by simp [h2]
  have hdist : dist (fun j => f j (z + (τ : ℂ) * Complex.I)) (fun j => f j z) < δ := by
    rw [dist_pi_lt_iff hδ]
    intro j
    obtain ⟨n, hn⟩ := hτ j
    set h : ℝ := τ - n * P j with hhdef
    have hPj : 0 < |P j| := abs_pos.2 (hP j)
    have hh : |h| < η j := by
      have e : h = P j * (τ / P j - n) := by
        rw [hhdef, mul_sub, mul_div_cancel₀ _ (hP j)]; ring
      rw [e, abs_mul]
      have := hcle j
      rw [le_div_iff₀ hPj] at this
      calc |P j| * |τ / P j - n| < |P j| * c := mul_lt_mul_of_pos_left hn hPj
        _ = c * |P j| := mul_comm _ _
        _ ≤ η j := this
    have ha : a < (z + (h : ℂ) * Complex.I).re := by simp; linarith
    have hb : (z + (h : ℂ) * Complex.I).re < b := by simp; linarith
    have hshift := int_period (f j) (P j) a b (hper j) n (z + (h : ℂ) * Complex.I) ha hb
    have eq : z + (h : ℂ) * Complex.I + (n : ℂ) * (P j : ℂ) * Complex.I
        = z + (τ : ℂ) * Complex.I := by
      rw [hhdef]; push_cast; ring
    rw [eq] at hshift
    rw [dist_eq_norm, hshift]
    exact hηU j z h1 h2 h hh
  have := hΦU _ (hbound _ hz' hz'') _ (hbound z h1 h2) hdist
  rw [dist_eq_norm] at this
  exact this.le

end AlmostPeriodicSumProdAux

open AlmostPeriodicSumProdAux in
theorem solution
    {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (P : ι → ℝ) (a b : ℝ)
    (hf : ∀ j ∈ s, DifferentiableOn ℂ (f j) {z : ℂ | a < z.re ∧ z.re < b})
    (hP : ∀ j ∈ s, P j ≠ 0)
    (hper : ∀ j ∈ s, ∀ z : ℂ, a < z.re → z.re < b →
      f j (z + (P j : ℂ) * Complex.I) = f j z) :
    IsAlmostPeriodicOnStrip (fun z => ∑ j ∈ s, f j z) a b ∧
      IsAlmostPeriodicOnStrip (fun z => ∏ j ∈ s, f j z) a b := by
  have hc' : ∀ j : s, ContinuousOn (f j) {z : ℂ | a < z.re ∧ z.re < b} :=
    fun j => (hf j j.2).continuousOn
  have hP' : ∀ j : s, P j ≠ 0 := fun j => hP j j.2
  have hper' : ∀ j : s, ∀ z : ℂ, a < z.re → z.re < b →
      f j (z + (P j : ℂ) * Complex.I) = f j z := fun j => hper j j.2
  refine ⟨⟨DifferentiableOn.fun_sum hf, ?_⟩, ⟨DifferentiableOn.fun_finsetProd hf, ?_⟩⟩
  · intro α β hα hβ ε hε
    have := lemD (fun j : s => f j) (fun j : s => P j) a b hc' hP' hper'
      (fun x => ∑ j, x j) (continuous_finsetSum _ fun j _ => continuous_apply j)
      α β hα hβ ε hε
    refine relDense_mono this ?_
    intro τ hτ z h1 h2
    have e1 : ∀ w : ℂ, (∑ j : s, f j w) = ∑ j ∈ s, f j w :=
      fun w => Finset.sum_coe_sort s (fun j => f j w)
    have := hτ z h1 h2
    dsimp only at this
    rwa [e1, e1] at this
  · intro α β hα hβ ε hε
    have := lemD (fun j : s => f j) (fun j : s => P j) a b hc' hP' hper'
      (fun x => ∏ j, x j) (continuous_finsetProd _ fun j _ => continuous_apply j)
      α β hα hβ ε hε
    refine relDense_mono this ?_
    intro τ hτ z h1 h2
    have e1 : ∀ w : ℂ, (∏ j : s, f j w) = ∏ j ∈ s, f j w :=
      fun w => Finset.prod_coe_sort s (fun j => f j w)
    have := hτ z h1 h2
    dsimp only at this
    rwa [e1, e1] at this
