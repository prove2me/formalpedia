-- Prove2me | solution 1 for AggGameNet.Sync.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:23:01.821173+00:00
-- url     : https://prove2.me/submissions/65f5b240-dc85-4d78-b28c-9def4c189caf

import Mathlib
import Definitions.Def_AggGameNet_Sync_Setting
import Theorems.Thm_AggGameNet_Sync_vi_exists_unique
import Theorems.Thm_AggGameNet_Sync_lemma_3
import Theorems.Thm_AggGameNet_Sync_relation_19
import Theorems.Thm_AggGameNet_Sync_relation_20

open AggGameNet.Sync

open Filter
open scoped Topology

theorem solution {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (E n)) (F : Fin N → E n → E n → E n)
    (h1 : Assumption1 K F) (h2 : Assumption2 K F)
    (Lbar : Fin N → ℝ) (h3 : Assumption3 K F Lbar)
    (G : ℕ → SimpleGraph (Fin N)) (Q : ℕ) (h4 : Assumption4 G Q)
    (W : ℕ → Matrix (Fin N) (Fin N) ℝ) (δ : ℝ)
    (hδ : 0 < δ) (h5 : Assumption5 G W δ)
    (α : ℕ → ℝ) (h6 : Assumption6 α)
    (x v : ℕ → Fin N → E n) (hrun : IsSyncRun K F W α x v) :
    ∃ xs, IsVISol K F xs ∧
      (∀ y, IsVISol K F y → y = xs) ∧ Tendsto x atTop (𝓝 xs) := by
  obtain ⟨xs, hxs, huniq⟩ := vi_exists_unique hN K F h1 h2
  refine ⟨xs, hxs, huniq, ?_⟩
  -- feasibility of the iterates
  have hfeas : ∀ k i, x k i ∈ K i := by
    intro k i
    cases k with
    | zero => exact hrun.1 i
    | succ k => exact ((hrun.2.2 k i).1).1
  have hxsK : ∀ i, xs i ∈ K i := hxs.1
  obtain ⟨hanti, hdiv, hsq⟩ := h6
  -- nonnegativity of the steps
  have hα : ∀ k, 0 ≤ α k := by
    intro k
    by_contra hk
    push Not at hk
    have hb : ∀ T : ℕ, ∑ j ∈ Finset.range (k + T), α j ≤
        ∑ j ∈ Finset.range k, α j + T * α k := by
      intro T
      induction T with
      | zero => simp
      | succ T ih =>
        rw [← add_assoc, Finset.sum_range_succ]
        have : α (k + T) ≤ α k := hanti (Nat.le_add_right k T)
        push_cast; linarith
    have hev := hdiv.eventually (eventually_ge_atTop (∑ j ∈ Finset.range k, α j + 1))
    obtain ⟨T0, hT0⟩ := eventually_atTop.1 hev
    have e1 := hT0 (k + T0) (by omega)
    have e2 := hb T0
    have e3 : (T0 : ℝ) * α k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hk.le
    linarith
  -- compactness
  have hP : IsCompact (Set.univ.pi K) := isCompact_univ_pi (fun i => (h1.1 i).2.1)
  have hKbar : IsCompact (Kbar K) := by
    have : Kbar K = (fun y : Fin N → E n => ∑ i, y i) '' (Set.univ.pi K) := by
      ext u
      simp only [Kbar, Set.mem_ofPred_eq, Set.mem_image, Set.mem_univ_pi]
      constructor
      · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
    rw [this]
    exact hP.image (continuous_finsetSum _ (fun i _ => continuous_apply i))
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ i, ∀ a ∈ K i, ‖a‖ ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_iUnion (fun i => (h1.1 i).2.1)).exists_bound_of_continuousOn
      (continuousOn_id (s := ⋃ i, K i))
    refine ⟨max M 0, le_max_right _ _, fun i a ha => ?_⟩
    have := hM a (Set.mem_iUnion.2 ⟨i, ha⟩)
    simp only [id] at this
    exact this.trans (le_max_left _ _)
  obtain ⟨Fmax, hF⟩ : ∃ Fmax : ℝ, ∀ i, ∀ xi ∈ K i, ∀ u ∈ Kbar K, ‖F i xi u‖ ≤ Fmax := by
    have hb : ∀ i, ∃ Ci : ℝ, ∀ q ∈ K i ×ˢ Kbar K, ‖F i q.1 q.2‖ ≤ Ci := fun i =>
      (((h1.1 i).2.1).prod hKbar).exists_bound_of_continuousOn (h1.2 i)
    choose Ci hCi using hb
    refine ⟨∑ i, max (Ci i) 0, fun i xi hxi u hu => ?_⟩
    have h := hCi i (xi, u) ⟨hxi, hu⟩
    have : max (Ci i) 0 ≤ ∑ j, max (Ci j) 0 :=
      Finset.single_le_sum (f := fun j => max (Ci j) 0) (fun j _ => le_max_right _ _)
        (Finset.mem_univ i)
    exact h.trans ((le_max_left _ _).trans this)
  obtain ⟨C, hC⟩ := lemma_3 hN K F h1 Lbar h3 G Q h4 W δ hδ h5 α x v hrun
  have hcol : ∀ k i, ∑ j, W k j i = 1 := fun k i => (h5 k).2.2 i
  have hrel := relation_19 hN K F h1 Lbar h3 W α x v hrun hcol hα xs hxs C Fmax M
    (fun i k => (hC i k).2) hF hM
  have hr20 := relation_20 hN K F h1 Lbar h3 G Q h4 W δ hδ h5 α ⟨hanti, hdiv, hsq⟩ x v hrun
  -- the sequences of Lemma 5
  set A : (Fin N → E n) → ℝ := fun y => ∑ i, ‖y i - xs i‖ ^ 2 with hAdef
  set cf : (Fin N → E n) → ℝ :=
    fun y => ∑ i, inner ℝ (phi F y i - phi F xs i) (y i - xs i) with hcfdef
  set b : ℕ → ℝ := fun k => (N : ℝ) * (2 * C ^ 2 + 2 * Fmax ^ 2) * α k ^ 2 +
      4 * α k * M * (N : ℝ) * (∑ i, Lbar i * ‖vhat W v k i - yavg v k‖) with hbdef
  have hrec : ∀ k, A (x (k + 1)) ≤ A (x k) + b k - 2 * α k * cf (x k) := by
    intro k
    have := hrel k
    simp only [hAdef, hcfdef, hbdef]
    linarith
  have hA0 : ∀ y, 0 ≤ A y := fun y => Finset.sum_nonneg (fun i _ => by positivity)
  have hcf0 : ∀ y, (∀ i, y i ∈ K i) → 0 ≤ cf y := by
    intro y hy
    by_cases hyx : y = xs
    · subst hyx; simp [hcfdef]
    · exact (h2 y xs hy hxsK hyx).le
  have hb0 : ∀ k, 0 ≤ b k := by
    intro k
    have : 0 ≤ ∑ i, Lbar i * ‖vhat W v k i - yavg v k‖ :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (h3.1 i).le (norm_nonneg _))
    have := hα k
    simp only [hbdef]
    positivity
  have hbsum : Summable b := by
    have e : b = fun k => ((N : ℝ) * (2 * C ^ 2 + 2 * Fmax ^ 2)) * α k ^ 2 +
        ∑ i, (4 * M * (N : ℝ) * Lbar i) * (α k * ‖vhat W v k i - yavg v k‖) := by
      funext k
      simp only [hbdef]
      rw [Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e]
    exact (hsq.mul_left _).add (summable_sum (fun i _ => (hr20 i).mul_left _))
  -- Lemma 5 (deterministic)
  set Bs : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, b j with hBs
  set Ds : ℕ → ℝ := fun k => ∑ j ∈ Finset.range k, α j * cf (x j) with hDs
  set d : ℕ → ℝ := fun k => A (x k) - Bs k + 2 * Ds k with hd
  have hd_anti : Antitone d := by
    apply antitone_nat_of_succ_le
    intro k
    simp only [hd, hBs, hDs, Finset.sum_range_succ]
    linarith [hrec k]
  have hBle : ∀ k, Bs k ≤ ∑' j, b j := fun k =>
    hbsum.sum_le_tsum _ (fun j _ => hb0 j)
  have hDnn : ∀ j, 0 ≤ α j * cf (x j) := fun j => mul_nonneg (hα j) (hcf0 _ (hfeas j))
  have hDle : ∀ k, Ds k ≤ (A (x 0) + ∑' j, b j) / 2 := by
    intro k
    have h0 := hd_anti (Nat.zero_le k)
    simp only [hd, hBs, hDs, Finset.sum_range_zero] at h0
    have := hBle k
    have := hA0 (x k)
    simp only [hBs, hDs] at *
    linarith
  have hDsum : Summable (fun j => α j * cf (x j)) := summable_of_sum_range_le hDnn hDle
  have hd_bdd : BddBelow (Set.range d) := by
    refine ⟨-(∑' j, b j), ?_⟩
    rintro _ ⟨k, rfl⟩
    have := hBle k
    have := hA0 (x k)
    have : 0 ≤ Ds k := Finset.sum_nonneg (fun j _ => hDnn j)
    simp only [hd]
    linarith
  have hd_t := tendsto_atTop_ciInf hd_anti hd_bdd
  have hB_t : Tendsto Bs atTop (𝓝 (∑' j, b j)) := hbsum.hasSum.tendsto_sum_nat
  have hD_t : Tendsto Ds atTop (𝓝 (∑' j, α j * cf (x j))) := hDsum.hasSum.tendsto_sum_nat
  set L := (⨅ k, d k) + ∑' j, b j - 2 * ∑' j, α j * cf (x j) with hL
  have ha_t : Tendsto (fun k => A (x k)) atTop (𝓝 L) := by
    have := (hd_t.add hB_t).sub (hD_t.const_mul 2)
    refine this.congr (fun k => ?_)
    simp only [hd]
    ring
  have hL0 : 0 ≤ L := ge_of_tendsto' ha_t (fun k => hA0 _)
  -- continuity of cf on the feasible set
  have hcont : ContinuousOn cf (Set.univ.pi K) := by
    simp only [hcfdef]
    apply continuousOn_finsetSum
    intro i _
    have hFi : ContinuousOn (fun y : Fin N → E n => F i (y i) (∑ j, y j)) (Set.univ.pi K) := by
      have hm : Set.MapsTo (fun y : Fin N → E n => (y i, ∑ j, y j)) (Set.univ.pi K)
          (K i ×ˢ Kbar K) := by
        intro y hy
        exact ⟨hy i (Set.mem_univ i), y, fun j => hy j (Set.mem_univ j), rfl⟩
      exact (h1.2 i).comp
        (((continuous_apply i).prodMk
          (continuous_finsetSum _ (fun j _ => continuous_apply j))).continuousOn) hm
    exact (hFi.sub continuousOn_const).inner
      (((continuous_apply i).continuousOn).sub continuousOn_const)
  have hLz : L = 0 := by
    by_contra hLne
    have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hLne)
    set S := Set.univ.pi K ∩ {y | L / 2 ≤ A y} with hS
    have hAcont : Continuous A := by
      simp only [hAdef]
      exact continuous_finsetSum _ (fun i _ =>
        ((continuous_apply i).sub continuous_const).norm.pow 2)
    have hScpt : IsCompact S := hP.inter_right (isClosed_le continuous_const hAcont)
    have hev : ∀ᶠ k in atTop, L / 2 ≤ A (x k) :=
      ha_t.eventually (eventually_ge_nhds (by linarith))
    obtain ⟨K0, hK0⟩ := eventually_atTop.1 hev
    have hmemS : ∀ k, K0 ≤ k → x k ∈ S := fun k hk =>
      ⟨fun i _ => hfeas k i, hK0 k hk⟩
    obtain ⟨y0, hy0S, hy0min⟩ :=
      hScpt.exists_isMinOn ⟨x K0, hmemS K0 le_rfl⟩ (hcont.mono Set.inter_subset_left)
    have hy0ne : y0 ≠ xs := by
      intro h
      have := hy0S.2
      simp only [Set.mem_ofPred_eq, h, hAdef, sub_self, norm_zero] at this
      norm_num at this
      linarith
    have hm : 0 < cf y0 := h2 y0 xs (fun i => hy0S.1 i (Set.mem_univ i)) hxsK hy0ne
    have hle : ∀ k, α (k + K0) * cf y0 ≤ α (k + K0) * cf (x (k + K0)) := fun k =>
      mul_le_mul_of_nonneg_left (hy0min (hmemS (k + K0) (by omega))) (hα _)
    have hs1 : Summable (fun k => α (k + K0) * cf y0) :=
      Summable.of_nonneg_of_le (fun k => mul_nonneg (hα _) hm.le) hle
        ((summable_nat_add_iff (f := fun j => α j * cf (x j)) K0).2 hDsum)
    have hs2 : Summable (fun k => α k * cf y0) := (summable_nat_add_iff (f := fun j => α j * cf y0) K0).1 hs1
    have hs3 : Summable α := by
      have := hs2.div_const (cf y0)
      simpa [mul_div_assoc, div_self hm.ne'] using this
    exact not_tendsto_atTop_of_tendsto_nhds hs3.hasSum.tendsto_sum_nat hdiv
  rw [hLz] at ha_t
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq_t : Tendsto (fun k => Real.sqrt (A (x k))) atTop (𝓝 0) := by
    simpa using ha_t.sqrt
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hsq_t
  apply Real.le_sqrt_of_sq_le
  exact Finset.single_le_sum (f := fun j => ‖x k j - xs j‖ ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i)

