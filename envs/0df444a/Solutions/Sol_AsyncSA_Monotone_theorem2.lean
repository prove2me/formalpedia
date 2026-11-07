-- Prove2me | solution 1 for AsyncSA.Monotone.theorem2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T11:45:53.402149+00:00
-- url     : https://prove2.me/submissions/76c2e5f2-7dff-4ace-b1d8-0d888ef5e356

import Mathlib
import Definitions.Def_AsyncSA_Monotone_Model
import Theorems.Thm_AsyncSA_Monotone_lemma4
import Theorems.Thm_AsyncSA_Monotone_lemma5
import Theorems.Thm_AsyncSA_Monotone_lemma7
import Theorems.Thm_AsyncSA_Contraction_lemma2

open MeasureTheory Filter Topology

namespace AsyncSAThm2Aux

open AsyncSA.Monotone

variable {n : ℕ} {Ω : Type*}

theorem tailW_eq (a w : ℕ → ℝ) (t0 t : ℕ) :
    AsyncSA.Contraction.tailW a w t0 t = tailW a w t0 t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [AsyncSA.Contraction.tailW, tailW, ih]

theorem tailW_neg (a w : ℕ → ℝ) (t0 t : ℕ) :
    tailW a (fun s => - w s) t0 t = - tailW a w t0 t := by
  induction t with
  | zero => simp [tailW]
  | succ t ih =>
    simp only [tailW, ih]
    split_ifs <;> ring

/-- The reflected algorithm `x ↦ -x`, `F ↦ (y ↦ -F(-y))`, `w ↦ -w`. -/
def negAlg (alg : Algorithm n Ω) : Algorithm n Ω where
  F := fun y => -alg.F (-y)
  x := fun t ω => -alg.x t ω
  α := alg.α
  w := fun i t ω => -alg.w i t ω
  τ := alg.τ
  α_mem := alg.α_mem
  τ_le := alg.τ_le
  update := by
    intro i t ω
    have h := alg.update i t ω
    have e : (-(fun j => (-alg.x (alg.τ i j t ω) ω) j)) = fun j => alg.x (alg.τ i j t ω) ω j := by
      funext j; simp
    simp only [Pi.neg_apply]
    rw [show (fun j => -alg.x (alg.τ i j t ω) ω j) = (fun j => (-alg.x (alg.τ i j t ω) ω) j)
      from rfl]
    rw [e, h]
    ring

theorem neg_assumption4 (F : (Fin n → ℝ) → Fin n → ℝ) (xstar : Fin n → ℝ)
    (h4 : Assumption4 F xstar) : Assumption4 (fun y => -F (-y)) (-xstar) where
  mono := fun a b hab => neg_le_neg (h4.mono (neg_le_neg hab))
  cont := (h4.cont.comp continuous_neg).neg
  fixed := by simp [h4.fixed]
  unique := by
    intro y hy
    have : F (-y) = -y := neg_eq_iff_eq_neg.1 hy
    have := h4.unique (-y) this
    rw [← this, neg_neg]
  shift := by
    intro x r hr
    obtain ⟨a, b, c⟩ := h4.shift (-x) r hr
    have e1 : -(x - r • (1 : Fin n → ℝ)) = -x + r • (1 : Fin n → ℝ) := by abel
    have e2 : -(x + r • (1 : Fin n → ℝ)) = -x - r • (1 : Fin n → ℝ) := by abel
    simp only [e1, e2]
    refine ⟨fun j => ?_, fun j => ?_, fun j => ?_⟩
    · have := c j; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at this ⊢; linarith
    · have := b j; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at this ⊢; linarith
    · have := a j; simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at this ⊢; linarith

theorem seq_neg (F : (Fin n → ℝ) → Fin n → ℝ) (xstar : Fin n → ℝ) (r : ℝ) (k : ℕ) :
    Useq (fun y => -F (-y)) (-xstar) r k = -Lseq F xstar r k ∧
      Lseq (fun y => -F (-y)) (-xstar) r k = -Useq F xstar r k := by
  induction k with
  | zero => constructor <;> · simp only [Useq, Lseq]; abel
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · simp only [Useq, Lseq, ih1, neg_neg]
      rw [← neg_add, smul_neg]
    · simp only [Useq, Lseq, ih2, neg_neg]
      rw [← neg_add, smul_neg]

/-- One step of the upper envelope: from `L^k ≤ x(t) ≤ U^k` eventually, get `x(t) ≤ U^{k+1}`
eventually (along a fixed sample path). -/
theorem upper_step (alg : Algorithm n Ω) (xstar : Fin n → ℝ) (r : ℝ)
    (h4 : Assumption4 alg.F xstar) (hr : 0 < r) (ω : Ω) (k tk : ℕ)
    (h18 : ∀ t, tk ≤ t →
      Lseq alg.F xstar r k ≤ alg.x t ω ∧ alg.x t ω ≤ Useq alg.F xstar r k)
    (hτ : ∀ i j, Tendsto (fun t => alg.τ i j t ω) atTop atTop)
    (hsum : ∀ i, Tendsto (fun T => ∑ t ∈ Finset.range T, alg.α i t ω) atTop atTop)
    (hW : ∀ i, ∀ δ : ℝ, 0 < δ → ∃ T : ℕ, ∀ t0 t : ℕ, T ≤ t0 → t0 ≤ t →
      |tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t0 t| ≤ δ) :
    ∃ T, ∀ t, T ≤ t → alg.x t ω ≤ Useq alg.F xstar r (k + 1) := by
  set U := Useq alg.F xstar r k with hUdef
  by_cases hUF : U = alg.F U
  · refine ⟨tk, fun t ht => ?_⟩
    have h := (h18 t ht).2
    show alg.x t ω ≤ (1 / 2 : ℝ) • (U + alg.F U)
    rw [← hUF]
    intro j
    have := h j
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    linarith
  · have hFU : alg.F U ≤ U :=
      ((lemma4 alg.F xstar r h4 hr k).1.1).trans (lemma4 alg.F xstar r h4 hr k).1.2
    set S : Finset (Fin n) := Finset.univ.filter (fun i => 0 < U i - alg.F U i) with hS
    have hne : S.Nonempty := by
      by_contra hcon
      apply hUF
      funext j
      have hj : j ∉ S := fun hj => hcon ⟨j, hj⟩
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
      have := hFU j
      linarith
    obtain ⟨i0, hi0, hmin⟩ := S.exists_min_image (fun i => (U i - alg.F U i) / 4) hne
    set δ := (U i0 - alg.F U i0) / 4 with hδdef
    have hi0' : 0 < U i0 - alg.F U i0 := by
      simpa [hS] using hi0
    have hδpos : 0 < δ := by rw [hδdef]; linarith
    have hδ : IsLeast ((fun i => (Useq alg.F xstar r k i - alg.F (Useq alg.F xstar r k) i) / 4) ''
        {i | 0 < Useq alg.F xstar r k i - alg.F (Useq alg.F xstar r k) i}) δ := by
      refine ⟨⟨i0, hi0', rfl⟩, ?_⟩
      rintro _ ⟨i, hi, rfl⟩
      exact hmin i (by simpa [hS] using hi)
    -- choose t'k
    have E1 : ∀ᶠ t0 in atTop, ∀ i, ∀ t, t0 ≤ t →
        |tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t0 t| ≤ δ := by
      refine eventually_all.2 fun i => ?_
      obtain ⟨T, hT⟩ := hW i δ hδpos
      exact eventually_atTop.2 ⟨T, fun t0 h t ht => hT t0 t h ht⟩
    have E2 : ∀ᶠ t0 in atTop, ∀ t, t0 ≤ t → ∀ i j, tk ≤ alg.τ i j t ω := by
      have h : ∀ᶠ t in atTop, ∀ i j, tk ≤ alg.τ i j t ω :=
        eventually_all.2 fun i => eventually_all.2 fun j => (hτ i j).eventually_ge_atTop tk
      obtain ⟨N, hN⟩ := eventually_atTop.1 h
      exact eventually_atTop.2 ⟨N, fun t0 h0 t ht => hN t (h0.trans ht)⟩
    obtain ⟨t'k, hE1, hE2⟩ := (E1.and E2).exists
    -- the relaxation sequence X, in closed form
    let X : Fin n → ℕ → ℝ := fun i t =>
      alg.F U i + (U i - alg.F U i) * ∏ s ∈ Finset.Ico t'k t, (1 - alg.α i s ω)
    have hX0 : ∀ i, X i t'k = U i := by
      intro i; simp [X]
    have hX : ∀ i t, t'k ≤ t →
        X i (t + 1) = (1 - alg.α i t ω) * X i t + alg.α i t ω * alg.F U i := by
      intro i t ht
      simp only [X, Finset.prod_Ico_succ_top ht]
      ring
    -- choose t''k
    have E3 : ∀ᶠ T in atTop, ∀ i,
        ∑ t ∈ Finset.range t'k, alg.α i t ω + 3 ≤ ∑ t ∈ Finset.range T, alg.α i t ω :=
      eventually_all.2 fun i => tendsto_atTop.1 (hsum i) _
    obtain ⟨t''k, hE3, hE4⟩ := (E3.and (eventually_ge_atTop t'k)).exists
    have hprod : ∀ i, ∏ s ∈ Finset.Ico t'k t''k, (1 - alg.α i s ω) ≤ 1 / 4 := by
      intro i
      have hsplit := Finset.sum_range_add_sum_Ico (fun t => alg.α i t ω) hE4
      have hIco : 3 ≤ ∑ s ∈ Finset.Ico t'k t''k, alg.α i s ω := by
        have := hE3 i; linarith
      have h1 : ∏ s ∈ Finset.Ico t'k t''k, (1 - alg.α i s ω) ≤
          ∏ s ∈ Finset.Ico t'k t''k, Real.exp (-alg.α i s ω) := by
        apply Finset.prod_le_prod
        · intro s _; have := (alg.α_mem i s ω).2; linarith
        · intro s _; have := Real.add_one_le_exp (-alg.α i s ω); linarith
      rw [← Real.exp_sum, Finset.sum_neg_distrib] at h1
      have h2 : Real.exp (-∑ s ∈ Finset.Ico t'k t''k, alg.α i s ω) ≤ Real.exp (-3) :=
        Real.exp_le_exp.2 (by linarith)
      have h3 : Real.exp (-3) ≤ 1 / 4 := by
        have := Real.add_one_le_exp (3 : ℝ)
        rw [Real.exp_neg]
        rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
        linarith
      linarith
    have hW' : ∀ t, t''k ≤ t → ∀ i,
        tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t'k t ≤ δ := by
      intro t ht i
      exact (le_abs_self _).trans (hE1 i t (hE4.trans ht))
    have h18' : ∀ t, tk ≤ t →
        Lseq alg.F xstar r k ≤ alg.x t ω ∧ alg.x t ω ≤ Useq alg.F xstar r k := h18
    have key := lemma7 alg xstar r h4 hr ω k tk t'k t''k h18' hE2 X hX0 hX hUF δ hδ hE4
      hprod hW'
    exact ⟨t''k, fun t ht i => key i t ht⟩

/-- The pathwise part of Theorem 2. -/
theorem pathwise (alg : Algorithm n Ω) (xstar : Fin n → ℝ)
    (h4 : Assumption4 alg.F xstar) (ω : Ω) (M : ℝ) (hM : ∀ t j, |alg.x t ω j| ≤ M)
    (hτ : ∀ i j, Tendsto (fun t => alg.τ i j t ω) atTop atTop)
    (hsum : ∀ i, Tendsto (fun T => ∑ t ∈ Finset.range T, alg.α i t ω) atTop atTop)
    (hW : ∀ i, ∀ δ : ℝ, 0 < δ → ∃ T : ℕ, ∀ t0 t : ℕ, T ≤ t0 → t0 ≤ t →
      |tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t0 t| ≤ δ) :
    Tendsto (fun t => alg.x t ω) atTop (𝓝 xstar) := by
  set r : ℝ := max M 0 + ∑ j, |xstar j| + 1 with hrdef
  have hsum0 : 0 ≤ ∑ j, |xstar j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hr : 0 < r := by
    have := le_max_right M 0
    rw [hrdef]; linarith
  have claim : ∀ k, ∃ tk, ∀ t, tk ≤ t →
      Lseq alg.F xstar r k ≤ alg.x t ω ∧ alg.x t ω ≤ Useq alg.F xstar r k := by
    intro k
    induction k with
    | zero =>
      refine ⟨0, fun t _ => ⟨fun j => ?_, fun j => ?_⟩⟩ <;>
      · have h1 := hM t j
        have h2 : |xstar j| ≤ ∑ j, |xstar j| :=
          Finset.single_le_sum (f := fun j => |xstar j|) (fun j _ => abs_nonneg _)
            (Finset.mem_univ j)
        have h3 := le_max_left M 0
        rw [abs_le] at h1
        have h4 := neg_abs_le (xstar j)
        have h5 := le_abs_self (xstar j)
        simp only [Lseq, Useq, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.one_apply,
          smul_eq_mul, mul_one]
        rw [hrdef]
        linarith
    | succ k ih =>
      obtain ⟨tk, htk⟩ := ih
      obtain ⟨T1, hT1⟩ := upper_step alg xstar r h4 hr ω k tk htk hτ hsum hW
      -- lower side by reflection
      have h4' := neg_assumption4 alg.F xstar h4
      have hs := seq_neg alg.F xstar r
      have h18' : ∀ t, tk ≤ t →
          Lseq (negAlg alg).F (-xstar) r k ≤ (negAlg alg).x t ω ∧
            (negAlg alg).x t ω ≤ Useq (negAlg alg).F (-xstar) r k := by
        intro t ht
        have e1 : Lseq (negAlg alg).F (-xstar) r k = -Useq alg.F xstar r k := (hs k).2
        have e2 : Useq (negAlg alg).F (-xstar) r k = -Lseq alg.F xstar r k := (hs k).1
        rw [e1, e2]
        exact ⟨neg_le_neg (htk t ht).2, neg_le_neg (htk t ht).1⟩
      have hW' : ∀ i, ∀ δ : ℝ, 0 < δ → ∃ T : ℕ, ∀ t0 t : ℕ, T ≤ t0 → t0 ≤ t →
          |tailW (fun s => (negAlg alg).α i s ω) (fun s => (negAlg alg).w i s ω) t0 t| ≤ δ := by
        intro i δ hδ
        obtain ⟨T, hT⟩ := hW i δ hδ
        refine ⟨T, fun t0 t h1 h2 => ?_⟩
        have := tailW_neg (fun s => alg.α i s ω) (fun s => alg.w i s ω) t0 t
        simp only [negAlg] at this ⊢
        rw [this, abs_neg]
        exact hT t0 t h1 h2
      obtain ⟨T2, hT2⟩ := upper_step (negAlg alg) (-xstar) r h4' hr ω k tk h18' hτ hsum hW'
      refine ⟨max T1 T2, fun t ht => ⟨?_, hT1 t (le_of_max_le_left ht)⟩⟩
      have h := hT2 t (le_of_max_le_right ht)
      have e2 : Useq (negAlg alg).F (-xstar) r (k + 1) = -Lseq alg.F xstar r (k + 1) :=
        (hs (k + 1)).1
      rw [e2] at h
      exact neg_le_neg_iff.1 h
  obtain ⟨hU, hL⟩ := lemma5 alg.F xstar r h4 hr
  rw [tendsto_pi_nhds]
  intro j
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hUj := (tendsto_pi_nhds.1 hU) j
  have hLj := (tendsto_pi_nhds.1 hL) j
  have e1 : ∀ᶠ k in atTop, Useq alg.F xstar r k j < xstar j + ε :=
    hUj.eventually (gt_mem_nhds (by linarith))
  have e2 : ∀ᶠ k in atTop, xstar j - ε < Lseq alg.F xstar r k j :=
    hLj.eventually (lt_mem_nhds (by linarith))
  obtain ⟨k, hk1, hk2⟩ := (e1.and e2).exists
  obtain ⟨tk, htk⟩ := claim k
  refine ⟨tk, fun t ht => ?_⟩
  have a1 := (htk t ht).1 j
  have a2 := (htk t ht).2 j
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

end AsyncSAThm2Aux

open AsyncSA.Monotone

theorem solution {n : ℕ} {Ω : Type*} [m0 : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (𝓕 : Filtration ℕ m0) (alg : Algorithm n Ω) (xstar : Fin n → ℝ)
    (h1 : alg.Assumption1 P) (h2 : alg.Assumption2 P 𝓕) (hx : alg.Adapted 𝓕)
    (h3 : alg.Assumption3 P) (h4 : Assumption4 alg.F xstar)
    (hbdd : ∀ᵐ ω ∂P, ∃ M : ℝ, ∀ t j, |alg.x t ω j| ≤ M) :
    ∀ᵐ ω ∂P, Tendsto (fun t => alg.x t ω) atTop (𝓝 xstar) := by
  obtain ⟨cA, cB, hvar⟩ := h2.var_bound
  obtain ⟨C, hC⟩ := h3.sum_sq
  set B : ℕ → Ω → ℝ := fun t ω => max (cA + cB * alg.runMax t ω ^ 2) 0 with hBdef
  have hrun_meas : ∀ t, Measurable[𝓕 t] (fun ω => alg.runMax t ω) := by
    intro t
    unfold Algorithm.runMax
    refine Measurable.iSup fun s => Measurable.iSup fun j => ?_
    have hs : (s : ℕ) ≤ t := Nat.lt_succ_iff.1 s.2
    exact (continuous_abs.measurable.comp ((hx s j).mono (𝓕.mono hs) le_rfl))
  have hBmeas : ∀ t, Measurable[𝓕 t] (B t) := by
    intro t
    exact (((hrun_meas t).pow_const 2).const_mul cB |>.const_add cA).max measurable_const
  have hBbdd : ∀ᵐ ω ∂P, ∃ K : ℝ, ∀ t, |B t ω| ≤ K := by
    filter_upwards [hbdd] with ω ⟨M, hM⟩
    refine ⟨|cA| + |cB| * (max M 0) ^ 2, fun t => ?_⟩
    have hR0 : 0 ≤ alg.runMax t ω :=
      Real.iSup_nonneg fun s => Real.iSup_nonneg fun j => abs_nonneg _
    have hRm : alg.runMax t ω ≤ max M 0 :=
      Real.iSup_le (fun s => Real.iSup_le (fun j => (hM s j).trans (le_max_left _ _))
        (le_max_right _ _)) (le_max_right _ _)
    have hR2 : alg.runMax t ω ^ 2 ≤ (max M 0) ^ 2 := pow_le_pow_left₀ hR0 hRm 2
    have h5 : cB * alg.runMax t ω ^ 2 ≤ |cB| * (max M 0) ^ 2 :=
      (mul_le_mul_of_nonneg_right (le_abs_self cB) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hR2 (abs_nonneg _))
    simp only [hBdef]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [le_abs_self cA]) (by positivity)
  have hl2 : ∀ i, ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ →
      ∃ T : ℕ, ∀ t₀ t : ℕ, T ≤ t₀ → t₀ ≤ t →
        |AsyncSA.Contraction.tailW (fun s => alg.α i s ω) (fun s => alg.w i s ω) t₀ t| ≤ δ := by
    intro i
    refine AsyncSA.Contraction.lemma2 P 𝓕 (alg.α i) (alg.w i) B C (h2.α_meas i) (h2.w_meas i)
      hBmeas (h2.mean_zero i) ?_ (Eventually.of_forall fun ω t => alg.α_mem i t ω)
      (h3.sum_inf i) (hC i) hBbdd
    intro t
    refine ⟨Eventually.of_forall fun ω => le_max_right _ _, ?_⟩
    intro S hS
    have h := hvar i t S hS
    have heq : (fun ω => ENNReal.ofReal (B t ω)) =
        fun ω => ENNReal.ofReal (cA + cB * alg.runMax t ω ^ 2) := by
      funext ω
      simp only [hBdef]
      rcases le_total (cA + cB * alg.runMax t ω ^ 2) 0 with h0 | h0
      · rw [max_eq_right h0, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h0]
      · rw [max_eq_left h0]
    rw [heq]
    exact h
  filter_upwards [hbdd, ae_all_iff.2 fun i => ae_all_iff.2 fun j => h1 i j,
    ae_all_iff.2 fun i => h3.sum_inf i, ae_all_iff.2 hl2] with ω hb hτ hs hw
  obtain ⟨M, hM⟩ := hb
  refine AsyncSAThm2Aux.pathwise alg xstar h4 ω M hM hτ hs ?_
  intro i δ hδ
  obtain ⟨T, hT⟩ := hw i δ hδ
  exact ⟨T, fun t0 t h1 h2 => by rw [← AsyncSAThm2Aux.tailW_eq]; exact hT t0 t h1 h2⟩
