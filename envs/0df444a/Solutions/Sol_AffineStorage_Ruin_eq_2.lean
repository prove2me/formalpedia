-- Prove2me | solution 1 for AffineStorage.Ruin.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T00:43:40.123289+00:00
-- url     : https://prove2.me/submissions/90b1a595-6ef8-46a5-88fc-ff5fe575b49d

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology
open AffineStorage.Ruin

/-! ### Counting functions of an increasing sequence of epochs -/

lemma affRuin2_cnt_mem {S : ℕ → ℝ} (hex : ∀ b, ∃ n, b < S n) (t : ℝ) :
    t < S (sInf {n | t < S n}) := Nat.sInf_mem (hex t)

lemma affRuin2_cnt_lt {S : ℕ → ℝ} (t : ℝ) {n : ℕ} (hn : n < sInf {n | t < S n}) : S n ≤ t :=
  not_lt.mp (Nat.notMem_of_lt_sInf hn)

/-- The counting function is constant on `[t, S (N t))`. -/
lemma affRuin2_cnt_right {S : ℕ → ℝ} (hex : ∀ b, ∃ n, b < S n) (t s : ℝ) (hts : t ≤ s)
    (hs : s < S (sInf {n | t < S n})) : sInf {n | s < S n} = sInf {n | t < S n} := by
  refine le_antisymm (Nat.sInf_le hs) ?_
  by_contra h
  push Not at h
  have h1 := affRuin2_cnt_lt (S := S) t h
  have h2 := affRuin2_cnt_mem hex s
  linarith

/-- Just left of `t`, the counting function equals the "strictly before" count. -/
lemma affRuin2_cnt_left {S : ℕ → ℝ} (hmono : StrictMono S) (hex : ∀ b, ∃ n, b < S n) (t : ℝ) :
    ∃ lb < t, ∀ s ∈ Set.Ioo lb t, sInf {n | s < S n} = sInf {n | t ≤ S n} := by
  have hexb : ({n | t ≤ S n} : Set ℕ).Nonempty := by
    obtain ⟨n, hn⟩ := hex t; exact ⟨n, hn.le⟩
  have hK : t ≤ S (sInf {n | t ≤ S n}) := Nat.sInf_mem hexb
  have hbelow : ∀ n, n < sInf {n | t ≤ S n} → S n < t :=
    fun n hn => not_le.mp (Nat.notMem_of_lt_sInf hn)
  rcases Nat.eq_zero_or_pos (sInf {n | t ≤ S n}) with h0 | hpos
  · refine ⟨t - 1, by linarith, fun s hs => ?_⟩
    rw [h0] at hK ⊢
    exact Nat.eq_zero_of_le_zero (Nat.sInf_le (show s < S 0 by linarith [hs.2]))
  · set K := sInf {n | t ≤ S n} with hK_def
    refine ⟨S (K - 1), hbelow _ (by omega), fun s hs => ?_⟩
    refine le_antisymm (Nat.sInf_le (show s < S K by linarith [hs.2])) ?_
    by_contra h
    push Not at h
    have hmem := Nat.sInf_mem (show ({n | s < S n} : Set ℕ).Nonempty from hex s)
    have : S (sInf {n | s < S n}) ≤ S (K - 1) := hmono.monotone (by omega)
    simp only [Set.mem_setOf_eq] at hmem
    linarith [hs.1]

lemma affRuin2_cnt_at {S : ℕ → ℝ} (hmono : StrictMono S) (n : ℕ) :
    sInf {m | S n < S m} = n + 1 := by
  refine le_antisymm (Nat.sInf_le (show S n < S (n + 1) from hmono (Nat.lt_succ_self n))) ?_
  by_contra h
  push Not at h
  have hmem := Nat.sInf_mem (show ({m | S n < S m} : Set ℕ).Nonempty from ⟨n + 1, hmono (Nat.lt_succ_self n)⟩)
  simp only [Set.mem_setOf_eq] at hmem
  have : S (sInf {m | S n < S m}) ≤ S n := hmono.monotone (by omega)
  linarith

lemma affRuin2_cntb_at {S : ℕ → ℝ} (hmono : StrictMono S) (n : ℕ) :
    sInf {m | S n ≤ S m} = n := by
  refine le_antisymm (Nat.sInf_le (show S n ≤ S n from le_rfl)) ?_
  by_contra h
  push Not at h
  have hmem := Nat.sInf_mem (show ({m | S n ≤ S m} : Set ℕ).Nonempty from ⟨n, show S n ≤ S n from le_rfl⟩)
  simp only [Set.mem_setOf_eq] at hmem
  have : S (sInf {m | S n ≤ S m}) < S n := hmono h
  linarith

lemma affRuin2_cnt_eq_cntb {S : ℕ → ℝ} (t : ℝ) (hne : ∀ m, S m ≠ t) :
    sInf {m | t < S m} = sInf {m | t ≤ S m} := by
  congr 1
  ext m
  simp only [Set.mem_setOf_eq]
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (Ne.symm (hne m))⟩

/-! ### Pathwise analysis of the closed form -/

section Path
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The closed form with frozen jump counts `N`, `M`. -/
noncomputable def affRuin2_g (B : Basis Ω) (P : Params) (x : ℝ) (ω : Ω) (N M : ℕ) (s : ℝ) : ℝ :=
  x * Real.exp (P.r * s) + P.p / P.r * (Real.exp (P.r * s) - 1)
    + ∑ n ∈ Finset.range N, Real.exp (P.r * (s - B.Tup n ω)) * B.Z (2, n) ω
    - ∑ n ∈ Finset.range M, Real.exp (P.r * (s - B.Tdown n ω)) * B.Z (3, n) ω

lemma affRuin2_g_cont (B : Basis Ω) (P : Params) (x : ℝ) (ω : Ω) (N M : ℕ) :
    Continuous (affRuin2_g B P x ω N M) := by
  unfold affRuin2_g
  fun_prop

lemma affRuin2_X_eq (B : Basis Ω) (P : Params) (x s : ℝ) (ω : Ω) :
    B.X P x s ω = affRuin2_g B P x ω (B.Nup s ω) (B.Ndown s ω) s := rfl

lemma affRuin2_Xminus_eq (B : Basis Ω) (P : Params) (x s : ℝ) (ω : Ω) :
    B.Xminus P x s ω = affRuin2_g B P x ω (B.NupBefore s ω) (B.NdownBefore s ω) s := rfl

lemma affRuin2_strictMono (B : Basis Ω) (i : Fin 4) (ω : Ω) (hz : ∀ k, 0 < B.Z (i, k) ω) :
    StrictMono (fun n => ∑ k ∈ Finset.range (n + 1), B.Z (i, k) ω) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  show ∑ k ∈ Finset.range (n + 1), B.Z (i, k) ω < ∑ k ∈ Finset.range (n + 1 + 1), B.Z (i, k) ω
  rw [Finset.sum_range_succ _ (n + 1)]
  linarith [hz (n + 1)]

lemma affRuin2_path (P : Params) (B : Basis Ω) (x : ℝ) (ω : Ω)
    (hz0 : ∀ k, 0 < B.Z (0, k) ω) (hz1 : ∀ k, 0 < B.Z (1, k) ω)
    (hu : ∀ b, ∃ n, b < B.Tup n ω) (hd : ∀ b, ∃ n, b < B.Tdown n ω)
    (hne : ∀ n m, B.Tup n ω ≠ B.Tdown m ω) :
    B.X P x 0 ω = x ∧
    (∀ t, ContinuousWithinAt (fun s => B.X P x s ω) (Set.Ici t) t) ∧
    (∀ t, Tendsto (fun s => B.X P x s ω) (𝓝[<] t) (𝓝 (B.Xminus P x t ω))) ∧
    (∀ n, B.X P x (B.Tup n ω) ω - B.Xminus P x (B.Tup n ω) ω = B.Z (2, n) ω) ∧
    (∀ n, B.X P x (B.Tdown n ω) ω - B.Xminus P x (B.Tdown n ω) ω = -B.Z (3, n) ω) := by
  have hmu : StrictMono (fun n => B.Tup n ω) := affRuin2_strictMono B 0 ω hz0
  have hmd : StrictMono (fun n => B.Tdown n ω) := affRuin2_strictMono B 1 ω hz1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `X_0 = x`
    have h0u : B.Nup 0 ω = 0 := by
      refine Nat.eq_zero_of_le_zero (Nat.sInf_le ?_)
      show (0:ℝ) < B.Tup 0 ω
      simp only [Basis.Tup, zero_add, Finset.sum_range_one]; exact hz0 0
    have h0d : B.Ndown 0 ω = 0 := by
      refine Nat.eq_zero_of_le_zero (Nat.sInf_le ?_)
      show (0:ℝ) < B.Tdown 0 ω
      simp only [Basis.Tdown, zero_add, Finset.sum_range_one]; exact hz1 0
    rw [affRuin2_X_eq, h0u, h0d]
    simp [affRuin2_g]
  · -- right-continuity
    intro t
    set N0 := B.Nup t ω
    set M0 := B.Ndown t ω
    have hN : t < B.Tup N0 ω := affRuin2_cnt_mem (S := fun n => B.Tup n ω) hu t
    have hM : t < B.Tdown M0 ω := affRuin2_cnt_mem (S := fun n => B.Tdown n ω) hd t
    have hev : (fun s => B.X P x s ω) =ᶠ[𝓝[≥] t] affRuin2_g B P x ω N0 M0 := by
      filter_upwards [Ico_mem_nhdsGE (lt_min hN hM)] with s hs
      have e1 : B.Nup s ω = N0 := affRuin2_cnt_right (S := fun n => B.Tup n ω) hu t s hs.1
        (lt_of_lt_of_le hs.2 (min_le_left _ _))
      have e2 : B.Ndown s ω = M0 := affRuin2_cnt_right (S := fun n => B.Tdown n ω) hd t s hs.1
        (lt_of_lt_of_le hs.2 (min_le_right _ _))
      rw [affRuin2_X_eq, e1, e2]
    exact ((affRuin2_g_cont B P x ω N0 M0).continuousWithinAt).congr_of_eventuallyEq hev rfl
  · -- left limits
    intro t
    obtain ⟨l1, hl1, h1⟩ := affRuin2_cnt_left (S := fun n => B.Tup n ω) hmu hu t
    obtain ⟨l2, hl2, h2⟩ := affRuin2_cnt_left (S := fun n => B.Tdown n ω) hmd hd t
    have hev : affRuin2_g B P x ω (B.NupBefore t ω) (B.NdownBefore t ω) =ᶠ[𝓝[<] t]
        (fun s => B.X P x s ω) := by
      filter_upwards [Ioo_mem_nhdsLT (max_lt hl1 hl2)] with s hs
      have e1 : B.Nup s ω = B.NupBefore t ω :=
        h1 s ⟨lt_of_le_of_lt (le_max_left _ _) hs.1, hs.2⟩
      have e2 : B.Ndown s ω = B.NdownBefore t ω :=
        h2 s ⟨lt_of_le_of_lt (le_max_right _ _) hs.1, hs.2⟩
      rw [affRuin2_X_eq, e1, e2]
    rw [affRuin2_Xminus_eq]
    exact (((affRuin2_g_cont B P x ω _ _).tendsto t).mono_left nhdsWithin_le_nhds).congr' hev
  · -- jumps up
    intro n
    have e1 : B.Nup (B.Tup n ω) ω = n + 1 := affRuin2_cnt_at (S := fun n => B.Tup n ω) hmu n
    have e2 : B.NupBefore (B.Tup n ω) ω = n := affRuin2_cntb_at (S := fun n => B.Tup n ω) hmu n
    have e3 : B.Ndown (B.Tup n ω) ω = B.NdownBefore (B.Tup n ω) ω :=
      affRuin2_cnt_eq_cntb (S := fun n => B.Tdown n ω) _ fun m => (hne n m).symm
    rw [affRuin2_X_eq, affRuin2_Xminus_eq, e1, e2, e3]
    simp only [affRuin2_g, Finset.sum_range_succ, sub_self, mul_zero, Real.exp_zero, one_mul]
    ring
  · -- jumps down
    intro n
    have e1 : B.Ndown (B.Tdown n ω) ω = n + 1 := affRuin2_cnt_at (S := fun n => B.Tdown n ω) hmd n
    have e2 : B.NdownBefore (B.Tdown n ω) ω = n :=
      affRuin2_cntb_at (S := fun n => B.Tdown n ω) hmd n
    have e3 : B.Nup (B.Tdown n ω) ω = B.NupBefore (B.Tdown n ω) ω :=
      affRuin2_cnt_eq_cntb (S := fun n => B.Tup n ω) _ fun m => hne m n
    rw [affRuin2_X_eq, affRuin2_Xminus_eq, e1, e2, e3]
    simp only [affRuin2_g, Finset.sum_range_succ, sub_self, mul_zero, Real.exp_zero, one_mul]
    ring

end Path

/-! ### Facts about the exponential law -/

lemma affRuin2_exp_apply (c : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    expMeasure c s = ∫⁻ y in s, exponentialPDF c y := by
  show (volume.withDensity (gammaPDF 1 c)) s = _
  rw [withDensity_apply _ hs]
  rfl

lemma affRuin2_exp_Iic_zero (c : ℝ) (hc : 0 < c) : expMeasure c (Set.Iic 0) = 0 := by
  rw [affRuin2_exp_apply c measurableSet_Iic, lintegral_exponentialPDF_eq_antiDeriv hc]
  simp

lemma affRuin2_exp_Ioi_one_pos (c : ℝ) (hc : 0 < c) : expMeasure c (Set.Ioi 1) ≠ 0 := by
  have := isProbabilityMeasure_expMeasure hc
  have h1 : expMeasure c (Set.Iic 1) = ENNReal.ofReal (1 - Real.exp (-c)) := by
    rw [affRuin2_exp_apply c measurableSet_Iic, lintegral_exponentialPDF_eq_antiDeriv hc]
    simp
  rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic, h1]
  refine (tsub_pos_iff_lt.mpr ?_).ne'
  exact ENNReal.ofReal_lt_one.mpr (by linarith [Real.exp_pos (-c)])

lemma affRuin2_exp_singleton (c a : ℝ) : expMeasure c {a} = 0 := by
  rw [affRuin2_exp_apply c (measurableSet_singleton a)]
  exact setLIntegral_measure_zero _ _ (Real.volume_singleton)

/-! ### Almost-sure properties of the primitives -/

section AS
variable {Ω : Type*} [MeasurableSpace Ω]

lemma affRuin2_pos (B : Basis Ω) (hm : ∀ k, Measurable (B.Z k)) (c : ℝ) (hc : 0 < c)
    (i : Fin 4) (hlaw : ∀ n, B.P.map (B.Z (i, n)) = expMeasure c) :
    ∀ᵐ ω ∂B.P, ∀ k, 0 < B.Z (i, k) ω := by
  rw [ae_all_iff]
  intro k
  rw [ae_iff]
  have : {ω | ¬ 0 < B.Z (i, k) ω} = B.Z (i, k) ⁻¹' Set.Iic 0 := by
    ext ω; simp
  rw [this, ← Measure.map_apply (hm _) measurableSet_Iic, hlaw k, affRuin2_exp_Iic_zero c hc]

lemma affRuin2_tendsto (B : Basis Ω) (hprob : IsProbabilityMeasure B.P)
    (hm : ∀ k, Measurable (B.Z k)) (hind : iIndepFun B.Z B.P) (c : ℝ) (hc : 0 < c)
    (i : Fin 4) (hlaw : ∀ n, B.P.map (B.Z (i, n)) = expMeasure c) :
    ∀ᵐ ω ∂B.P, ∀ b : ℝ, ∃ n, b < ∑ k ∈ Finset.range (n + 1), B.Z (i, k) ω := by
  set E : ℕ → Set Ω := fun k => B.Z (i, k) ⁻¹' Set.Ioi 1 with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k => hm _ measurableSet_Ioi
  have hEind : iIndepSet E B.P := by
    rw [iIndepSet_iff_meas_biInter hEm]
    intro s
    have hi := (hind.precomp (g := fun k : ℕ => (i, k))
      (fun a b h => by simpa using h)).measure_inter_preimage_eq_mul s
      (sets := fun _ => Set.Ioi (1:ℝ)) (fun _ _ => measurableSet_Ioi)
    simpa [hE] using hi
  have hEμ : ∀ k, B.P (E k) = expMeasure c (Set.Ioi 1) := by
    intro k
    rw [hE, ← Measure.map_apply (hm _) measurableSet_Ioi, hlaw k]
  have hsum : (∑' k, B.P (E k)) = ⊤ := by
    simp only [hEμ]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (affRuin2_exp_Ioi_one_pos c hc)
  have hlim := measure_limsup_eq_one hEm hEind hsum
  have hae : ∀ᵐ ω ∂B.P, ω ∈ limsup E atTop := by
    rw [ae_iff]
    have hL : MeasurableSet (limsup E atTop) := MeasurableSet.measurableSet_limsup hEm
    have : {ω | ¬ ω ∈ limsup E atTop} = (limsup E atTop)ᶜ := rfl
    rw [this, measure_compl hL (measure_ne_top _ _), hlim, measure_univ, tsub_self]
  filter_upwards [hae, affRuin2_pos B hm c hc i hlaw] with ω hω hpos
  rw [mem_limsup_iff_frequently_mem] at hω
  set S : ℕ → ℝ := fun n => ∑ k ∈ Finset.range (n + 1), B.Z (i, k) ω
  have hS0 : ∀ n, 0 ≤ S n := fun n => Finset.sum_nonneg fun k _ => (hpos k).le
  have key : ∀ m : ℕ, ∃ n, (m : ℝ) ≤ S n := by
    intro m
    induction m with
    | zero => exact ⟨0, by simpa using hS0 0⟩
    | succ m ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨n', hn'1, hn'2⟩ := (Filter.frequently_atTop.mp hω) (n + 1)
      refine ⟨n', ?_⟩
      have hnot : n' ∉ Finset.range (n + 1) := by simp; omega
      have hsub : insert n' (Finset.range (n + 1)) ⊆ Finset.range (n' + 1) := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_range] at hk ⊢
        omega
      have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (f := fun k => B.Z (i, k) ω) (fun k _ _ => (hpos k).le)
      rw [Finset.sum_insert hnot] at h1
      have h2 : (1:ℝ) < B.Z (i, n') ω := hn'2
      push_cast
      simp only [S] at hn ⊢
      linarith
  intro b
  obtain ⟨n, hn⟩ := key (⌈b⌉₊ + 1)
  refine ⟨n, ?_⟩
  have := Nat.le_ceil b
  push_cast at hn
  simp only [S] at hn
  linarith

/-- If `X` is independent of `W` and the law of `X` has no atoms, then `X ≠ W` a.s. -/
lemma affRuin2_ne {X W : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : Measurable X) (hW : Measurable W) (hind : IndepFun X W μ)
    (hatom : ∀ a, μ.map X {a} = 0) : μ {ω | X ω = W ω} = 0 := by
  have hD : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} := measurableSet_eq_fun measurable_fst measurable_snd
  have : {ω | X ω = W ω} = (fun ω => (X ω, W ω)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} := rfl
  rw [this, ← Measure.map_apply (hX.prodMk hW) hD,
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hW.aemeasurable).mp hind]
  have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have : IsProbabilityMeasure (μ.map W) := Measure.isProbabilityMeasure_map hW.aemeasurable
  rw [Measure.prod_apply_symm hD]
  have : ∀ y : ℝ, (fun x => (x, y)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {y} := by
    intro y; ext x; simp
  simp only [this, hatom, lintegral_zero]

end AS

section Final
variable {Ω : Type*} [MeasurableSpace Ω]

lemma affRuin2_neq (P : Params) (hS : P.Standing) (B : Basis Ω) (hB : B.IsValid P) (n m : ℕ) :
    B.P {ω | B.Tup n ω = B.Tdown m ω} = 0 := by
  obtain ⟨hprob, hm, hind, h0, -, -, -⟩ := hB
  have hlp : 0 < P.lamPlus := hS.2.2.1
  set S : Finset (Fin 4 × ℕ) := {((0 : Fin 4), 0)} with hSdef
  set T : Finset (Fin 4 × ℕ) := (Finset.range n).image (fun k => ((0 : Fin 4), k + 1)) ∪
    (Finset.range (m + 1)).image (fun k => ((1 : Fin 4), k)) with hTdef
  have hST : Disjoint S T := by
    rw [hSdef, Finset.disjoint_singleton_left, hTdef]
    simp
  have hI := hind.indepFun_finset S T hST hm
  set φ : (S → ℝ) → ℝ := fun v => v ⟨((0 : Fin 4), 0), Finset.mem_singleton_self _⟩
  set ψ : (T → ℝ) → ℝ := fun v =>
    (∑ k ∈ Finset.range (m + 1),
      (if h : ((1 : Fin 4), k) ∈ T then v ⟨((1 : Fin 4), k), h⟩ else 0))
    - ∑ k ∈ Finset.range n,
      (if h : ((0 : Fin 4), k + 1) ∈ T then v ⟨((0 : Fin 4), k + 1), h⟩ else 0) with hψdef
  have hφm : Measurable φ := measurable_pi_apply _
  have hψm : Measurable ψ := by
    refine (Finset.measurable_sum _ fun k _ => ?_).sub (Finset.measurable_sum _ fun k _ => ?_)
    · by_cases h : ((1 : Fin 4), k) ∈ T
      · simp only [dif_pos h]; exact measurable_pi_apply _
      · simp only [dif_neg h]; exact measurable_const
    · by_cases h : ((0 : Fin 4), k + 1) ∈ T
      · simp only [dif_pos h]; exact measurable_pi_apply _
      · simp only [dif_neg h]; exact measurable_const
  have hI2 := hI.comp hφm hψm
  have hX : (φ ∘ fun a (i : S) => B.Z (↑i) a) = fun ω => B.Z ((0 : Fin 4), 0) ω := rfl
  have hW : (ψ ∘ fun a (i : T) => B.Z (↑i) a) =
      fun ω => B.Tdown m ω - (B.Tup n ω - B.Z ((0 : Fin 4), 0) ω) := by
    funext ω
    have m1 : ∀ k ∈ Finset.range (m + 1), ((1 : Fin 4), k) ∈ T := by
      intro k hk
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)
    have m0 : ∀ k ∈ Finset.range n, ((0 : Fin 4), k + 1) ∈ T := by
      intro k hk
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem (fun k => ((0 : Fin 4), k + 1)) hk)
    simp only [Function.comp, hψdef]
    rw [Finset.sum_congr rfl (fun k hk => dif_pos (m1 k hk)),
      Finset.sum_congr rfl (fun k hk => dif_pos (m0 k hk))]
    simp only [Basis.Tup, Basis.Tdown, Finset.sum_range_succ' _ n]
    ring
  rw [hX, hW] at hI2
  have hset : {ω | B.Tup n ω = B.Tdown m ω} =
      {ω | B.Z ((0 : Fin 4), 0) ω = B.Tdown m ω - (B.Tup n ω - B.Z ((0 : Fin 4), 0) ω)} := by
    ext ω; simp only [Set.mem_setOf_eq]; constructor <;> intro h <;> linarith
  rw [hset]
  have hWm : Measurable fun ω => B.Tdown m ω - (B.Tup n ω - B.Z ((0 : Fin 4), 0) ω) := by
    refine (Finset.measurable_sum _ fun k _ => hm _).sub
      ((Finset.measurable_sum _ fun k _ => hm _).sub (hm _))
  exact affRuin2_ne (hm _) hWm hI2 (fun a => by rw [h0 0]; exact affRuin2_exp_singleton _ a)

theorem solution (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (x : ℝ) :
    (∀ (ω : Ω) (tm tp : ℝ), tm < tp →
        (∀ n, B.Tup n ω ∉ Set.Ioo tm tp ∧ B.Tdown n ω ∉ Set.Ioo tm tp) →
        ∀ t ∈ Set.Ioo tm tp, B.X P x t ω =
          B.X P x tm ω * Real.exp (P.r * (t - tm))
            + P.p / P.r * (Real.exp (P.r * (t - tm)) - 1)) ∧
    (∀ᵐ ω ∂B.P,
      B.X P x 0 ω = x ∧
      (∀ t, ContinuousWithinAt (fun s => B.X P x s ω) (Set.Ici t) t) ∧
      (∀ t, Tendsto (fun s => B.X P x s ω) (𝓝[<] t) (𝓝 (B.Xminus P x t ω))) ∧
      (∀ n, B.X P x (B.Tup n ω) ω - B.Xminus P x (B.Tup n ω) ω = B.Z (2, n) ω) ∧
      (∀ n, B.X P x (B.Tdown n ω) ω - B.Xminus P x (B.Tdown n ω) ω = -B.Z (3, n) ω)) := by
  constructor
  · intro ω tm tp _ hno t ht
    have hsets : ∀ T : ℕ → ℝ, (∀ n, T n ∉ Set.Ioo tm tp) →
        sInf {n | t < T n} = sInf {n | tm < T n} := by
      intro T hT
      congr 1
      ext n
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h; linarith [ht.1]
      · intro h
        by_contra hc
        push Not at hc
        exact hT n ⟨h, lt_of_le_of_lt hc ht.2⟩
    have e1 : B.Nup t ω = B.Nup tm ω := hsets (fun n => B.Tup n ω) fun n => (hno n).1
    have e2 : B.Ndown t ω = B.Ndown tm ω := hsets (fun n => B.Tdown n ω) fun n => (hno n).2
    rw [affRuin2_X_eq, affRuin2_X_eq, e1, e2]
    simp only [affRuin2_g]
    have hexp : ∀ a : ℝ, Real.exp (P.r * (t - a)) = Real.exp (P.r * (tm - a)) *
        Real.exp (P.r * (t - tm)) := by
      intro a; rw [← Real.exp_add]; ring_nf
    have hexp0 : Real.exp (P.r * t) = Real.exp (P.r * tm) * Real.exp (P.r * (t - tm)) := by
      rw [← Real.exp_add]; ring_nf
    have hs1 : ∑ i ∈ Finset.range (B.Nup tm ω), Real.exp (P.r * (t - B.Tup i ω)) * B.Z (2, i) ω
        = (∑ i ∈ Finset.range (B.Nup tm ω), Real.exp (P.r * (tm - B.Tup i ω)) * B.Z (2, i) ω)
          * Real.exp (P.r * (t - tm)) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by rw [hexp]; ring
    have hs2 : ∑ i ∈ Finset.range (B.Ndown tm ω), Real.exp (P.r * (t - B.Tdown i ω)) * B.Z (3, i) ω
        = (∑ i ∈ Finset.range (B.Ndown tm ω), Real.exp (P.r * (tm - B.Tdown i ω)) * B.Z (3, i) ω)
          * Real.exp (P.r * (t - tm)) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by rw [hexp]; ring
    rw [hs1, hs2, hexp0]
    ring
  · obtain ⟨hprob, hm, hind, h0, h1, h2, h3⟩ := hB
    have hlp : 0 < P.lamPlus := hS.2.2.1
    have hlm : 0 < P.lamMinus := hS.2.2.2.1
    have hneq : ∀ᵐ ω ∂B.P, ∀ n m, B.Tup n ω ≠ B.Tdown m ω := by
      rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro m
      rw [ae_iff]
      simpa using affRuin2_neq P hS B ⟨hprob, hm, hind, h0, h1, h2, h3⟩ n m
    filter_upwards [affRuin2_pos B hm _ hlp 0 h0, affRuin2_pos B hm _ hlm 1 h1,
      affRuin2_tendsto B hprob hm hind _ hlp 0 h0, affRuin2_tendsto B hprob hm hind _ hlm 1 h1,
      hneq] with ω hz0 hz1 hu hd hne
    exact affRuin2_path P B x ω hz0 hz1 hu hd hne

end Final
