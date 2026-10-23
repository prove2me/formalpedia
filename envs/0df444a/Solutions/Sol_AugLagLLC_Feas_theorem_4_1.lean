-- Prove2me | solution 1 for AugLagLLC.Feas.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T04:59:46.401382+00:00
-- url     : https://prove2.me/submissions/de8b4c72-5983-41a6-b61d-ec9d9f84f285

import Mathlib
import Definitions.Def_AugLagLLC_Feas_Setting

open Filter
open scoped Topology

set_option autoImplicit false

namespace AugLagFeasAux

open InnerProductSpace

section Grad

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma hg_add {f g : E → ℝ} {a b x : E} (hf : HasGradientAt f a x) (hg : HasGradientAt g b x) :
    HasGradientAt (fun y => f y + g y) (a + b) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  rw [map_add]; exact hf.add hg

lemma hg_const_mul {f : E → ℝ} {a x : E} (c : ℝ) (hf : HasGradientAt f a x) :
    HasGradientAt (fun y => c * f y) (c • a) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  rw [map_smulₛₗ, conj_trivial]; exact hf.const_mul c

lemma hg_sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} {a : ι → E} {x : E}
    (hf : ∀ i ∈ s, HasGradientAt (f i) (a i) x) :
    HasGradientAt (fun y => ∑ i ∈ s, f i y) (∑ i ∈ s, a i) x := by
  simp only [hasGradientAt_iff_hasFDerivAt] at *
  rw [map_sum]; exact HasFDerivAt.fun_sum hf

lemma hg_comp {f : E → ℝ} {a x : E} {q : ℝ → ℝ} {q' : ℝ} (hq : HasDerivAt q q' (f x))
    (hf : HasGradientAt f a x) : HasGradientAt (fun y => q (f y)) (q' • a) x := by
  rw [hasGradientAt_iff_hasFDerivAt] at *
  rw [map_smulₛₗ, conj_trivial]; exact hq.comp_hasFDerivAt x hf

lemma hasDerivAt_maxsq (t : ℝ) :
    HasDerivAt (fun s : ℝ => (max s 0) ^ 2) (2 * max t 0) t := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · have hev : (fun s : ℝ => (max s 0) ^ 2) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with s hs
      simp [max_eq_right (le_of_lt (show s < 0 from hs))]
    rw [max_eq_right h.le, mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  · rw [max_self, mul_zero, hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero, smul_zero]
    refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : ℝ => h ^ 2) ?_
      (Asymptotics.isLittleO_pow_id (by norm_num))
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun h => ?_)
    rcases le_total h 0 with hh | hh
    · simp [max_eq_right hh]; positivity
    · simp [max_eq_left hh]
  · have hev : (fun s : ℝ => (max s 0) ^ 2) =ᶠ[𝓝 t] fun s => s ^ 2 := by
      filter_upwards [Ioi_mem_nhds h] with s hs
      simp [max_eq_left (le_of_lt (show 0 < s from hs))]
    rw [max_eq_left h.le]
    have h2 := hasDerivAt_pow 2 t
    have h3 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := h2.congr_deriv (by simp)
    exact h3.congr_of_eventuallyEq hev

lemma hg_sq {s : E → ℝ} {a x : E} (hs : HasGradientAt s a x) :
    HasGradientAt (fun y => (s y) ^ 2) ((2 * s x) • a) x := by
  have hq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s x) (s x) :=
    (hasDerivAt_pow 2 (s x)).congr_deriv (by simp)
  exact hg_comp hq hs

lemma hg_sq_shift {s : E → ℝ} {a x : E} (c : ℝ) (hs : HasGradientAt s a x) :
    HasGradientAt (fun y => (s y + c) ^ 2) ((2 * (s x + c)) • a) x := by
  have hq : HasDerivAt (fun t : ℝ => (t + c) ^ 2) (2 * (s x + c)) (s x) := by
    have := ((hasDerivAt_id (s x)).add_const c).pow 2
    exact this.congr_deriv (by simp)
  exact hg_comp hq hs

lemma hg_maxsq_shift {s : E → ℝ} {a x : E} (c : ℝ) (hs : HasGradientAt s a x) :
    HasGradientAt (fun y => (max (s y + c) 0) ^ 2) ((2 * max (s x + c) 0) • a) x := by
  have hq : HasDerivAt (fun t : ℝ => (max (t + c) 0) ^ 2) (2 * max (s x + c) 0) (s x) := by
    have := (hasDerivAt_maxsq (s x + c)).comp (s x) ((hasDerivAt_id (s x)).add_const c)
    exact this.congr_deriv (by simp)
  exact hg_comp hq hs

lemma hg_max0sq {s : E → ℝ} {a x : E} (hs : HasGradientAt s a x) :
    HasGradientAt (fun y => (max 0 (s y)) ^ 2) ((2 * max (s x) 0) • a) x := by
  have hq : HasDerivAt (fun t : ℝ => (max 0 t) ^ 2) (2 * max (s x) 0) (s x) := by
    have e : (fun t : ℝ => (max 0 t) ^ 2) = fun t => (max t 0) ^ 2 :=
      funext fun t => by rw [max_comm]
    rw [e]; exact hasDerivAt_maxsq _
  exact hg_comp hq hs

lemma hgC1 {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x : E) : HasGradientAt f (gradient f x) x :=
  (hf.differentiable one_ne_zero x).hasGradientAt

lemma hgcont {f : E → ℝ} (hf : ContDiff ℝ 1 f) : Continuous (gradient f) :=
  (toDual ℝ E).symm.continuous.comp (hf.continuous_fderiv one_ne_zero)

end Grad

section Cara

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cara {T : Type*} [Fintype T] [DecidableEq T] (w : T → E) :
    ∀ (n : ℕ) (c : T → ℝ), (Finset.univ.filter (fun t => c t ≠ 0)).card ≤ n →
    ∃ c' : T → ℝ, (∀ t, ∃ s : ℝ, 0 ≤ s ∧ c' t = s * c t) ∧
      ∑ t, c' t • w t = ∑ t, c t • w t ∧
      LinearIndependent ℝ (fun t : {t // c' t ≠ 0} => w t) := by
  intro n
  induction n with
  | zero =>
    intro c hc
    have hz : ∀ t, c t = 0 := by
      intro t
      by_contra h
      have hm : t ∈ Finset.univ.filter (fun t => c t ≠ 0) := by simp [h]
      have := Finset.card_pos.2 ⟨t, hm⟩
      omega
    have : IsEmpty {t // c t ≠ 0} := ⟨fun ⟨t, ht⟩ => ht (hz t)⟩
    exact ⟨c, fun t => ⟨1, zero_le_one, (one_mul _).symm⟩, rfl, linearIndependent_empty_type⟩
  | succ n ih =>
    intro c hc
    by_cases hli : LinearIndependent ℝ (fun t : {t // c t ≠ 0} => w t)
    · exact ⟨c, fun t => ⟨1, zero_le_one, (one_mul _).symm⟩, rfl, hli⟩
    rw [Fintype.not_linearIndependent_iff] at hli
    obtain ⟨g, hg, i0, hi0⟩ := hli
    let d : T → ℝ := fun t => if h : c t ≠ 0 then g ⟨t, h⟩ else 0
    have hd0 : ∀ t, c t = 0 → d t = 0 := fun t ht => by simp [d, ht]
    have hdsum : ∑ t, d t • w t = 0 := by
      rw [← hg]
      rw [← Finset.sum_filter_of_ne (p := fun t => c t ≠ 0)
        (fun t _ h hct => h (by rw [hd0 t hct, zero_smul]))]
      rw [Finset.sum_subtype (Finset.univ.filter (fun t => c t ≠ 0)) (p := fun t => c t ≠ 0)
        (fun t => by simp)]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      simp [d, t.2]
    have hne : (Finset.univ : Finset T).Nonempty := ⟨i0.1, Finset.mem_univ _⟩
    obtain ⟨t0, -, ht0⟩ := Finset.exists_max_image Finset.univ (fun t => |d t / c t|) hne
    have hdi0 : d i0.1 = g i0 := by simp [d, i0.2]
    have hq0 : d t0 / c t0 ≠ 0 := by
      have h1 : 0 < |d i0.1 / c i0.1| :=
        abs_pos.2 (div_ne_zero (by rw [hdi0]; exact hi0) i0.2)
      have h2 := ht0 i0.1 (Finset.mem_univ _)
      exact abs_pos.1 (lt_of_lt_of_le h1 h2)
    have hct0 : c t0 ≠ 0 := fun h => hq0 (by simp [h])
    have hdt0 : d t0 ≠ 0 := fun h => hq0 (by simp [h])
    have key : ∀ t, ∃ s : ℝ, 0 ≤ s ∧ c t - c t0 / d t0 * d t = s * c t := by
      intro t
      by_cases hct : c t = 0
      · exact ⟨0, le_rfl, by simp [hct, hd0 t hct]⟩
      · refine ⟨1 - (d t / c t) / (d t0 / c t0), ?_, ?_⟩
        · have h3 := ht0 t (Finset.mem_univ _)
          have h4 : (d t / c t) / (d t0 / c t0) ≤ 1 := by
            calc (d t / c t) / (d t0 / c t0) ≤ |(d t / c t) / (d t0 / c t0)| := le_abs_self _
              _ = |d t / c t| / |d t0 / c t0| := abs_div _ _
              _ ≤ 1 := (div_le_one (abs_pos.2 hq0)).2 h3
          linarith
        · field_simp
    have hc2t0 : c t0 - c t0 / d t0 * d t0 = 0 := by
      rw [div_mul_cancel₀ _ hdt0, sub_self]
    have hsub : Finset.univ.filter (fun t => c t - c t0 / d t0 * d t ≠ 0) ⊆
        (Finset.univ.filter (fun t => c t ≠ 0)).erase t0 := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at ht ⊢
      refine ⟨fun h => ht (by rw [h]; exact hc2t0), fun hct => ht ?_⟩
      obtain ⟨s, -, hs⟩ := key t
      rw [hs, hct, mul_zero]
    have hmem : t0 ∈ Finset.univ.filter (fun t => c t ≠ 0) := by simp [hct0]
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hmem] at hcard
    obtain ⟨c', h1, h2, h3⟩ := ih (fun t => c t - c t0 / d t0 * d t) (by omega)
    refine ⟨c', fun t => ?_, ?_, h3⟩
    · obtain ⟨s1, hs1, e1⟩ := h1 t
      obtain ⟨s2, hs2, e2⟩ := key t
      exact ⟨s1 * s2, mul_nonneg hs1 hs2, by rw [e1, e2]; ring⟩
    · rw [h2]
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, hdsum,
        smul_zero, sub_zero]

end Cara

section AKKT

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem akkt {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {F : E → ℝ} {H : ι → E → ℝ} {G : κ → E → ℝ} {xs : E}
    (hH : ∀ i, ContinuousAt (gradient (H i)) xs) (hG : ∀ j, ContinuousAt (gradient (G j)) xs)
    (hfH : ∀ i, H i xs = 0) (hfG : ∀ j, G j xs ≤ 0)
    {y : ℕ → E} (hy : Tendsto y atTop (𝓝 xs)) {r : ℕ → E}
    (hr : Tendsto r atTop (𝓝 (gradient F xs)))
    {a : ℕ → ι → ℝ} {b : ℕ → κ → ℝ} (hb : ∀ k j, 0 ≤ b k j)
    (hcompl : ∀ j, G j xs < 0 → ∀ᶠ k in atTop, b k j = 0)
    (hres : Tendsto (fun k => r k + ∑ i, a k i • gradient (H i) (y k)
        + ∑ j, b k j • gradient (G j) (y k)) atTop (𝓝 0)) :
    AugLagLLC.Feas.IsKKT F H G xs ∨ ¬ AugLagLLC.Feas.CPLDAt H G xs := by
  classical
  let W : E → ι ⊕ κ → E := fun z => Sum.elim (fun i => gradient (H i) z) (fun j => gradient (G j) z)
  let C : ℕ → ι ⊕ κ → ℝ := fun k => Sum.elim (a k) (b k)
  have hCW : ∀ k, ∑ t, C k t • W (y k) t =
      ∑ i, a k i • gradient (H i) (y k) + ∑ j, b k j • gradient (G j) (y k) := by
    intro k; simp [C, W, Fintype.sum_sum_type]
  have hcar := fun k => cara (W (y k)) _ (C k) le_rfl
  choose C' hC'1 hC'2 hC'3 using hcar
  have hC'b : ∀ k j, 0 ≤ C' k (Sum.inr j) := by
    intro k j
    obtain ⟨s, hs, e⟩ := hC'1 k (Sum.inr j)
    rw [e]; exact mul_nonneg hs (hb k j)
  have hC'supp : ∀ k t, C' k t ≠ 0 → C k t ≠ 0 := by
    intro k t h hc
    obtain ⟨s, -, e⟩ := hC'1 k t
    exact h (by rw [e, hc, mul_zero])
  let Sf : ℕ → Finset (ι ⊕ κ) := fun k => Finset.univ.filter (fun t => C' k t ≠ 0)
  obtain ⟨S, hS⟩ : ∃ S, ∃ᶠ k in atTop, Sf k = S := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨k, hk⟩ := (Filter.eventually_all.2 hcon).exists
    exact hk (Sf k) rfl
  obtain ⟨φ1, hφ1, hφ1S⟩ := Filter.extraction_of_frequently_atTop hS
  let N : ℕ → ℝ := fun k => max 1 ‖C' k‖
  have hN1 : ∀ k, 1 ≤ N k := fun k => le_max_left _ _
  have hNpos : ∀ k, 0 < N k := fun k => lt_of_lt_of_le one_pos (hN1 k)
  let z : ℕ → (ι ⊕ κ → ℝ) × ℝ := fun m => ((N (φ1 m))⁻¹ • C' (φ1 m), (N (φ1 m))⁻¹)
  have hzb : ∀ m, z m ∈ Metric.closedBall (0 : (ι ⊕ κ → ℝ) × ℝ) 1 := by
    intro m
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    refine max_le ?_ ?_
    · show ‖(N (φ1 m))⁻¹ • C' (φ1 m)‖ ≤ 1
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (hNpos _).le,
        inv_mul_le_iff₀ (hNpos _), mul_one]
      exact le_max_right _ _
    · show ‖(N (φ1 m))⁻¹‖ ≤ 1
      rw [norm_inv, Real.norm_of_nonneg (hNpos _).le]
      exact inv_le_one_of_one_le₀ (hN1 _)
  obtain ⟨⟨α, β⟩, -, φ2, hφ2, hz⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hzb
  let p : ℕ → ℕ := fun m => φ1 (φ2 m)
  have hpt : Tendsto p atTop atTop := (hφ1.comp hφ2).tendsto_atTop
  have hαfull : Tendsto (fun m => (N (p m))⁻¹ • C' (p m)) atTop (𝓝 α) :=
    (continuous_fst.tendsto _).comp hz
  have hβ : Tendsto (fun m => (N (p m))⁻¹) atTop (𝓝 β) :=
    (continuous_snd.tendsto _).comp hz
  have hα : ∀ t, Tendsto (fun m => (N (p m))⁻¹ * C' (p m) t) atTop (𝓝 (α t)) :=
    fun t => hαfull.apply_nhds t
  have hyp : Tendsto (fun m => y (p m)) atTop (𝓝 xs) := hy.comp hpt
  have hWt : ∀ t, Tendsto (fun m => W (y (p m)) t) atTop (𝓝 (W xs t)) := by
    intro t
    cases t with
    | inl i => exact (hH i).tendsto.comp hyp
    | inr j => exact (hG j).tendsto.comp hyp
  have hlim1 : Tendsto (fun m => (N (p m))⁻¹ • r (p m)
      + ∑ t, ((N (p m))⁻¹ * C' (p m) t) • W (y (p m)) t) atTop
      (𝓝 (β • gradient F xs + ∑ t, α t • W xs t)) :=
    (hβ.smul (hr.comp hpt)).add (tendsto_finsetSum _ fun t _ => (hα t).smul (hWt t))
  have hlim2 : Tendsto (fun m => (N (p m))⁻¹ • r (p m)
      + ∑ t, ((N (p m))⁻¹ * C' (p m) t) • W (y (p m)) t) atTop (𝓝 0) := by
    have h0 : Tendsto (fun m => (N (p m))⁻¹ • (r (p m) + ∑ i, a (p m) i • gradient (H i) (y (p m))
        + ∑ j, b (p m) j • gradient (G j) (y (p m)))) atTop (𝓝 (β • (0 : E))) :=
      hβ.smul (hres.comp hpt)
    rw [smul_zero] at h0
    refine h0.congr (fun m => ?_)
    rw [add_assoc, ← hCW, ← hC'2, smul_add, Finset.smul_sum]
    simp only [smul_smul]
  have heq : β • gradient F xs + ∑ t, α t • W xs t = 0 := tendsto_nhds_unique hlim1 hlim2
  have hβnn : 0 ≤ β := ge_of_tendsto' hβ (fun m => (inv_pos.2 (hNpos _)).le)
  have hαb : ∀ j, 0 ≤ α (Sum.inr j) :=
    fun j => ge_of_tendsto' (hα (Sum.inr j))
      (fun m => mul_nonneg (inv_pos.2 (hNpos _)).le (hC'b _ j))
  have hSp : ∀ m, Sf (p m) = S := fun m => hφ1S (φ2 m)
  have hαS : ∀ t, t ∉ S → α t = 0 := by
    intro t ht
    have h0 : ∀ m, (N (p m))⁻¹ * C' (p m) t = 0 := by
      intro m
      have : C' (p m) t = 0 := by
        by_contra hne
        apply ht
        rw [← hSp m]
        simp [Sf, hne]
      rw [this, mul_zero]
    have := hα t
    simp only [h0] at this
    exact (tendsto_nhds_unique this tendsto_const_nhds)
  have hact : ∀ j, Sum.inr j ∈ S → G j xs = 0 := by
    intro j hj
    refine le_antisymm (hfG j) ?_
    by_contra hlt
    push_neg at hlt
    have hev := hφ1.tendsto_atTop.eventually (hcompl j hlt)
    obtain ⟨m, hm⟩ := hev.exists
    have hmem : Sum.inr j ∈ Sf (φ1 m) := by rw [hφ1S m]; exact hj
    have hne : C' (φ1 m) (Sum.inr j) ≠ 0 := by simpa [Sf] using hmem
    exact hC'supp _ _ hne (by simpa [C] using hm)
  have hαcompl : ∀ j, G j xs < 0 → α (Sum.inr j) = 0 := by
    intro j hj
    exact hαS _ (fun hS' => by have := hact j hS'; linarith)
  rcases eq_or_lt_of_le hβnn with hβ0 | hβpos
  · -- β = 0 : CPLD fails
    right
    intro hcpld
    have hev : ∀ᶠ m in atTop, (N (p m))⁻¹ < 1 := by
      rw [← hβ0] at hβ
      exact Filter.Tendsto.eventually_lt_const one_pos hβ
    have hαnorm : ∀ᶠ m in atTop, ‖(N (p m))⁻¹ • C' (p m)‖ = 1 := by
      filter_upwards [hev] with m hm
      have hN : 1 < N (p m) := lt_of_le_of_ne (hN1 _)
        (fun h => by rw [← h, inv_one] at hm; exact lt_irrefl _ hm)
      have hNe : N (p m) = ‖C' (p m)‖ := by
        rcases le_total 1 ‖C' (p m)‖ with h | h
        · exact max_eq_right h
        · exfalso
          have : N (p m) = 1 := max_eq_left h
          linarith
      rw [norm_smul, norm_inv, Real.norm_of_nonneg (hNpos _).le, ← hNe,
        inv_mul_cancel₀ (hNpos _).ne']
    have hαn1 : ‖α‖ = 1 :=
      tendsto_nhds_unique hαfull.norm
        (tendsto_const_nhds.congr' (hαnorm.mono fun m h => h.symm))
    have hαne : α ≠ 0 := by
      intro h; rw [h, norm_zero] at hαn1; exact zero_ne_one hαn1
    obtain ⟨t1, ht1⟩ : ∃ t, α t ≠ 0 := by
      by_contra h; push_neg at h; exact hαne (funext h)
    have ht1S : t1 ∈ S := by
      by_contra h; exact ht1 (hαS t1 h)
    let I : Finset ι := Finset.univ.filter (fun i => Sum.inl i ∈ S)
    let J : Finset κ := Finset.univ.filter (fun j => Sum.inr j ∈ S)
    have hJ : ∀ j ∈ J, G j xs = 0 := fun j hj => hact j (Finset.mem_filter.1 hj).2
    have hnt : (∃ i ∈ I, α (Sum.inl i) ≠ 0) ∨ (∃ j ∈ J, α (Sum.inr j) ≠ 0) := by
      cases t1 with
      | inl i => exact Or.inl ⟨i, by simp [I, ht1S], ht1⟩
      | inr j => exact Or.inr ⟨j, by simp [J, ht1S], ht1⟩
    have hsum0 : ∑ i ∈ I, α (Sum.inl i) • gradient (H i) xs
        + ∑ j ∈ J, α (Sum.inr j) • gradient (G j) xs = 0 := by
      rw [← hβ0, zero_smul, zero_add, Fintype.sum_sum_type] at heq
      rw [← heq]
      simp only [W, Sum.elim_inl, Sum.elim_inr, I, J, Finset.sum_filter]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs with h
        · rfl
        · rw [hαS _ h, zero_smul]
      · refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with h
        · rfl
        · rw [hαS _ h, zero_smul]
    have hev2 := hcpld I J hJ (fun i => α (Sum.inl i)) (fun j => α (Sum.inr j))
      (fun j _ => hαb j) hnt hsum0
    obtain ⟨m, hm⟩ := (hyp.eventually hev2).exists
    apply hm
    have hli := hC'3 (p m)
    have hmemS : ∀ t, t ∈ S → C' (p m) t ≠ 0 := by
      intro t ht
      rw [← hSp m] at ht
      simpa [Sf] using ht
    let f : I ⊕ J → {t // C' (p m) t ≠ 0} :=
      Sum.elim (fun i => ⟨Sum.inl i.1, hmemS _ (Finset.mem_filter.1 i.2).2⟩)
        (fun j => ⟨Sum.inr j.1, hmemS _ (Finset.mem_filter.1 j.2).2⟩)
    have hf : Function.Injective f := by
      rintro (⟨i, hi⟩ | ⟨j, hj⟩) (⟨i', hi'⟩ | ⟨j', hj'⟩) h <;> simp [f] at h ⊢ <;> exact h
    have := hli.comp f hf
    convert this using 1
    funext s
    rcases s with i | j <;> rfl
  · -- β > 0 : KKT
    left
    refine ⟨hfH, hfG, fun i => α (Sum.inl i) / β, fun j => α (Sum.inr j) / β,
      fun j => div_nonneg (hαb j) hβpos.le,
      fun j hj => by show α (Sum.inr j) / β = 0; rw [hαcompl j hj, zero_div], ?_⟩
    have e : gradient F xs + ∑ i, (α (Sum.inl i) / β) • gradient (H i) xs
        + ∑ j, (α (Sum.inr j) / β) • gradient (G j) xs
        = β⁻¹ • (β • gradient F xs + ∑ t, α t • W xs t) := by
      rw [Fintype.sum_sum_type]
      simp only [W, Sum.elim_inl, Sum.elim_inr, smul_add, Finset.smul_sum, smul_smul,
        inv_mul_cancel₀ hβpos.ne', one_smul, div_eq_inv_mul, add_assoc]
    rw [e, heq, smul_zero]

end AKKT

section Problem

open AugLagLLC.Feas

lemma grad_augLag {n m1 p1 m2 p2 : ℕ} (P : Problem n m1 p1 m2 p2) (hP : P.IsC1)
    (x : EuclideanSpace ℝ (Fin n)) (lam : Fin m1 → ℝ) (mu : Fin p1 → ℝ) (ρ : ℝ) :
    gradient (fun y => augLag P y lam mu ρ) x =
      gradient P.f x + (ρ / 2) • ∑ i, (2 * (P.h1 i x + lam i / ρ)) • gradient (P.h1 i) x
        + (ρ / 2) • ∑ i, (2 * max (P.g1 i x + mu i / ρ) 0) • gradient (P.g1 i) x := by
  obtain ⟨hf, hh1, hg1, -, -⟩ := hP
  refine HasGradientAt.gradient ?_
  unfold augLag
  exact hg_add (hg_add (hgC1 hf x) (hg_const_mul _ (hg_sum _ fun i _ =>
    hg_sq_shift _ (hgC1 (hh1 i) x)))) (hg_const_mul _ (hg_sum _ fun i _ =>
    hg_maxsq_shift _ (hgC1 (hg1 i) x)))

lemma grad_infeas {n m1 p1 m2 p2 : ℕ} (P : Problem n m1 p1 m2 p2) (hP : P.IsC1)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (infeas P) x = (1 / 2 : ℝ) • (∑ i, (2 * P.h1 i x) • gradient (P.h1 i) x
      + ∑ i, (2 * max (P.g1 i x) 0) • gradient (P.g1 i) x) := by
  obtain ⟨-, hh1, hg1, -, -⟩ := hP
  refine HasGradientAt.gradient ?_
  unfold infeas
  exact hg_const_mul _ (hg_add (hg_sum _ fun i _ => hg_sq (hgC1 (hh1 i) x))
    (hg_sum _ fun i _ => hg_max0sq (hgC1 (hg1 i) x)))

lemma bdd_div_tendsto {f g : ℕ → ℝ} (C : ℝ) (hf : ∀ m, |f m| ≤ C)
    (hg : Tendsto g atTop atTop) (hgpos : ∀ m, 0 < g m) :
    Tendsto (fun m => f m / g m) atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun m => ?_) (a := fun m => C * (g m)⁻¹) ?_
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos (hgpos m), div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hf m) (inv_nonneg.2 (hgpos m).le)
  · simpa using (tendsto_inv_atTop_zero.comp hg).const_mul C

end Problem

end AugLagFeasAux

open Filter Topology AugLagLLC.Feas in
theorem solution {n m1 p1 m2 p2 : ℕ} (P : Problem n m1 p1 m2 p2) (hP : P.IsC1)
    {τ γ ρ1 : ℝ} {lamMin lamMax : Fin m1 → ℝ} {muMax : Fin p1 → ℝ} {ε : ℕ → ℝ}
    (hpar : ValidParams τ γ ρ1 lamMin lamMax muMax ε)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {ρ : ℕ → ℝ} {lamBar : ℕ → Fin m1 → ℝ}
    {muBar : ℕ → Fin p1 → ℝ} {v : ℕ → Fin m2 → ℝ} {u : ℕ → Fin p2 → ℝ}
    (hrun : IsRun P τ γ ρ1 lamMin lamMax muMax ε x ρ lamBar muBar v u)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : MapClusterPt xs atTop x) :
    (BddAbove (Set.range ρ) → xs ∈ P.Omega1 ∩ P.Omega2) ∧
    (¬ BddAbove (Set.range ρ) → IsKKT (infeas P) P.h2 P.g2 xs ∨ ¬ CPLDAt P.h2 P.g2 xs) := by
  classical
  obtain ⟨hτ0, hτ1, hγ, hρ1, -, -, hε0, hεt⟩ := hpar
  obtain ⟨hρ1eq, hlam1, hmu1, hstep⟩ := hrun
  have hρpos : ∀ k, 1 ≤ k → 0 < ρ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rw [hρ1eq]; exact hρ1
    | succ k hk ih =>
      rw [(hstep k hk).2.2.2]
      split_ifs
      · exact ih
      · exact mul_pos (by linarith) ih
  have hρstep : ∀ k, 1 ≤ k → ρ k ≤ ρ (k + 1) := by
    intro k hk
    have hp := hρpos k hk
    rw [(hstep k hk).2.2.2]
    split_ifs
    · exact le_rfl
    · nlinarith
  have hρmono : ∀ k, 1 ≤ k → ∀ j, ρ k ≤ ρ (k + j) := by
    intro k hk j
    induction j with
    | zero => simp
    | succ j ih => exact ih.trans (hρstep (k + j) (by omega))
  have hρge : ∀ k, 1 ≤ k → ρ1 ≤ ρ k := by
    intro k hk
    have := hρmono 1 le_rfl (k - 1)
    rw [hρ1eq, show 1 + (k - 1) = k by omega] at this
    exact this
  have hlamB : ∀ k, 1 ≤ k → ∀ i, lamMin i ≤ lamBar k i ∧ lamBar k i ≤ lamMax i := by
    intro k hk
    rcases Nat.lt_or_ge k 2 with h | h
    · obtain rfl : k = 1 := by omega
      exact hlam1
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact (hstep j (by omega)).2.1
  have hmuB : ∀ k, 1 ≤ k → ∀ i, 0 ≤ muBar k i ∧ muBar k i ≤ muMax i := by
    intro k hk
    rcases Nat.lt_or_ge k 2 with h | h
    · obtain rfl : k = 1 := by omega
      exact hmu1
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      exact (hstep j (by omega)).2.2.1
  -- Step 2 facts
  have F1 : ∀ k, 1 ≤ k → ‖gradient (fun y => augLag P y (lamBar k) (muBar k) (ρ k)) (x k)
      + ∑ i, v k i • gradient (P.h2 i) (x k) + ∑ i, u k i • gradient (P.g2 i) (x k)‖ ≤ ε k := by
    intro k hk
    obtain ⟨e1, e2, e3, -, he1, -, -, -, -, h31, -, -, -⟩ := (hstep k hk).1
    linarith
  have F2 : ∀ k, 1 ≤ k → ∀ i, 0 ≤ u k i ∧ P.g2 i (x k) ≤ ε k := by
    intro k hk i
    obtain ⟨e1, e2, e3, -, -, -, he2, -, -, -, h32, -, -⟩ := (hstep k hk).1
    exact ⟨(h32 i).1, (h32 i).2.trans he2⟩
  have F3 : ∀ k, 1 ≤ k → ∀ i, P.g2 i (x k) < -ε k → u k i = 0 := by
    intro k hk i hi
    obtain ⟨e1, e2, e3, -, -, -, he2, -, -, -, -, h33, -⟩ := (hstep k hk).1
    exact h33 i (by linarith)
  have F4 : ∀ k, 1 ≤ k → ∀ i, |P.h2 i (x k)| ≤ ε k := by
    intro k hk i
    obtain ⟨e1, e2, e3, -, -, -, -, -, he3, -, -, -, h34⟩ := (hstep k hk).1
    have h := norm_le_pi_norm (h2vec P (x k)) i
    rw [Real.norm_eq_abs] at h
    exact h.trans (h34.trans he3)
  -- cluster subsequence
  obtain ⟨ψ, hψ, hψx⟩ := hxs.tendsto_subseq
  have hψ'1 : ∀ m, 1 ≤ ψ (m + 1) := fun m => le_trans (Nat.le_add_left 1 m) (hψ.id_le (m + 1))
  have hψ't : Tendsto (fun m => ψ (m + 1)) atTop atTop :=
    hψ.tendsto_atTop.comp (tendsto_add_atTop_nat 1)
  have hxψ : Tendsto (fun m => x (ψ (m + 1))) atTop (𝓝 xs) :=
    hψx.comp (tendsto_add_atTop_nat 1)
  have hεψ : Tendsto (fun m => ε (ψ (m + 1))) atTop (𝓝 0) := hεt.comp hψ't
  have hfH2 : ∀ i, P.h2 i xs = 0 := by
    intro i
    have h1 : Tendsto (fun m => P.h2 i (x (ψ (m + 1)))) atTop (𝓝 (P.h2 i xs)) :=
      ((hP.2.2.2.1 i).continuous.tendsto xs).comp hxψ
    have h2 : Tendsto (fun m => P.h2 i (x (ψ (m + 1)))) atTop (𝓝 0) :=
      squeeze_zero_norm (fun m => by rw [Real.norm_eq_abs]; exact F4 _ (hψ'1 m) i) hεψ
    exact tendsto_nhds_unique h1 h2
  have hfG2 : ∀ i, P.g2 i xs ≤ 0 := by
    intro i
    exact le_of_tendsto_of_tendsto' (((hP.2.2.2.2 i).continuous.tendsto xs).comp hxψ) hεψ
      (fun m => (F2 _ (hψ'1 m) i).2)
  constructor
  · -- bounded penalties
    intro hbdd
    obtain ⟨B, hB⟩ := hbdd
    obtain ⟨M, hM⟩ : ∃ M : ℕ → ℝ, ∀ k, M k = max ‖h1vec P (x k)‖ ‖sigma P x ρ muBar k‖ :=
      ⟨_, fun k => rfl⟩
    have hpass : ∃ K, 1 ≤ K ∧ ∀ k, K ≤ k → M k ≤ τ * M (k - 1) := by
      by_contra hcon
      push_neg at hcon
      have hgrow : ∀ N : ℕ, ∃ k, 1 ≤ k ∧ ρ1 * γ ^ N ≤ ρ k := by
        intro N
        induction N with
        | zero => exact ⟨1, le_rfl, by simp [hρ1eq]⟩
        | succ N ih =>
          obtain ⟨k, hk1, hk⟩ := ih
          obtain ⟨k', hkk', hk'⟩ := hcon k hk1
          refine ⟨k' + 1, by omega, ?_⟩
          have hcond : ¬ (max ‖h1vec P (x k')‖ ‖sigma P x ρ muBar k'‖
              ≤ τ * max ‖h1vec P (x (k' - 1))‖ ‖sigma P x ρ muBar (k' - 1)‖) := by
            rw [← hM, ← hM]; exact not_le.2 hk'
          have hr : ρ (k' + 1) = γ * ρ k' := by
            rw [(hstep k' (by omega)).2.2.2, if_neg hcond]
          have hmk := hρmono k hk1 (k' - k)
          rw [show k + (k' - k) = k' by omega] at hmk
          rw [hr, pow_succ]
          have := hρpos k hk1
          nlinarith
      obtain ⟨N, hN⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hγ).eventually_gt_atTop (B / ρ1)).exists
      obtain ⟨k, -, hk⟩ := hgrow N
      have hkB : ρ k ≤ B := hB ⟨k, rfl⟩
      rw [div_lt_iff₀ hρ1] at hN
      linarith
    obtain ⟨K, hK1, hK⟩ := hpass
    have hMnn : ∀ k, 0 ≤ M k := fun k => by rw [hM]; exact le_max_of_le_left (norm_nonneg _)
    have hgeom : ∀ j, M (K + j) ≤ τ ^ j * M K := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have h1 := hK (K + j + 1) (by omega)
        rw [show K + j + 1 - 1 = K + j by omega] at h1
        rw [show K + (j + 1) = K + j + 1 by ring, pow_succ]
        calc M (K + j + 1) ≤ τ * M (K + j) := h1
          _ ≤ τ * (τ ^ j * M K) := mul_le_mul_of_nonneg_left ih hτ0
          _ = τ ^ j * τ * M K := by ring
    have hMt : Tendsto M atTop (𝓝 0) := by
      rw [← Filter.tendsto_add_atTop_iff_nat K]
      have h0 : Tendsto (fun j => τ ^ j * M K) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hτ0 hτ1).mul_const (M K)
      refine squeeze_zero (fun j => hMnn _) (fun j => ?_) h0
      rw [add_comm]; exact hgeom j
    have hMψ : Tendsto (fun m => M (ψ (m + 1))) atTop (𝓝 0) := hMt.comp hψ't
    refine ⟨⟨fun i => ?_, fun i => ?_⟩, ⟨hfH2, hfG2⟩⟩
    · have h1 : Tendsto (fun m => P.h1 i (x (ψ (m + 1)))) atTop (𝓝 (P.h1 i xs)) :=
        ((hP.2.1 i).continuous.tendsto xs).comp hxψ
      have h2 : Tendsto (fun m => P.h1 i (x (ψ (m + 1)))) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun m => ?_) hMψ
        have h := norm_le_pi_norm (h1vec P (x (ψ (m + 1)))) i
        rw [hM]
        exact h.trans (le_max_left _ _)
      exact tendsto_nhds_unique h1 h2
    · refine le_of_tendsto_of_tendsto' (((hP.2.2.1 i).continuous.tendsto xs).comp hxψ) hMψ
        (fun m => ?_)
      have hk : ψ (m + 1) ≠ 0 := by have := hψ'1 m; omega
      have hs : P.g1 i (x (ψ (m + 1))) ≤ sigma P x ρ muBar (ψ (m + 1)) i := by
        simp only [sigma, hk, ↓reduceIte]
        exact le_max_left _ _
      have h := norm_le_pi_norm (sigma P x ρ muBar (ψ (m + 1))) i
      rw [Real.norm_eq_abs] at h
      calc P.g1 i (x (ψ (m + 1))) ≤ sigma P x ρ muBar (ψ (m + 1)) i := hs
        _ ≤ |sigma P x ρ muBar (ψ (m + 1)) i| := le_abs_self _
        _ ≤ ‖sigma P x ρ muBar (ψ (m + 1))‖ := h
        _ ≤ M (ψ (m + 1)) := by rw [hM]; exact le_max_right _ _
  · -- unbounded penalties
    intro hunb
    have hρt : Tendsto ρ atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro B
      rw [not_bddAbove_iff] at hunb
      obtain ⟨_, ⟨k, rfl⟩, hk⟩ := hunb (max B (ρ 0))
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; exact absurd hk (not_lt.2 (le_max_right _ _))
        · exact h
      refine ⟨k, fun k' hk' => ?_⟩
      have := hρmono k hk1 (k' - k)
      rw [show k + (k' - k) = k' by omega] at this
      linarith [le_max_left B (ρ 0)]
    have hρψ : Tendsto (fun m => ρ (ψ (m + 1))) atTop atTop := hρt.comp hψ't
    have hinvρ : Tendsto (fun m => (ρ (ψ (m + 1)))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hρψ
    have hρψpos : ∀ m, 0 < ρ (ψ (m + 1)) := fun m => hρpos _ (hψ'1 m)
    refine AugLagFeasAux.akkt (F := infeas P) (H := P.h2) (G := P.g2)
      (r := fun m => (ρ (ψ (m + 1)))⁻¹ • gradient (fun y => augLag P y (lamBar (ψ (m + 1)))
        (muBar (ψ (m + 1))) (ρ (ψ (m + 1)))) (x (ψ (m + 1))))
      (a := fun m i => (ρ (ψ (m + 1)))⁻¹ * v (ψ (m + 1)) i)
      (b := fun m j => (ρ (ψ (m + 1)))⁻¹ * u (ψ (m + 1)) j)
      (fun i => (AugLagFeasAux.hgcont (hP.2.2.2.1 i)).continuousAt)
      (fun j => (AugLagFeasAux.hgcont (hP.2.2.2.2 j)).continuousAt) hfH2 hfG2 hxψ ?_
      (fun m j => mul_nonneg (inv_nonneg.2 (hρψpos m).le) (F2 _ (hψ'1 m) j).1) ?_ ?_
    · -- r → ∇ infeas
      rw [AugLagFeasAux.grad_infeas P hP xs]
      have hlam : ∀ i, Tendsto (fun m => lamBar (ψ (m + 1)) i / ρ (ψ (m + 1))) atTop (𝓝 0) := by
        intro i
        refine AugLagFeasAux.bdd_div_tendsto (|lamMin i| + |lamMax i|) (fun m => ?_) hρψ hρψpos
        obtain ⟨h1, h2⟩ := hlamB _ (hψ'1 m) i
        exact abs_le.2 ⟨by linarith [neg_abs_le (lamMin i), abs_nonneg (lamMax i)],
          by linarith [le_abs_self (lamMax i), abs_nonneg (lamMin i)]⟩
      have hmu : ∀ i, Tendsto (fun m => muBar (ψ (m + 1)) i / ρ (ψ (m + 1))) atTop (𝓝 0) := by
        intro i
        refine AugLagFeasAux.bdd_div_tendsto (muMax i) (fun m => ?_) hρψ hρψpos
        obtain ⟨h1, h2⟩ := hmuB _ (hψ'1 m) i
        rw [abs_of_nonneg h1]; exact h2
      have hA : Tendsto (fun m => ∑ i, (2 * (P.h1 i (x (ψ (m + 1)))
          + lamBar (ψ (m + 1)) i / ρ (ψ (m + 1)))) • gradient (P.h1 i) (x (ψ (m + 1))))
          atTop (𝓝 (∑ i, (2 * P.h1 i xs) • gradient (P.h1 i) xs)) := by
        refine tendsto_finsetSum _ fun i _ => ?_
        have h := (tendsto_const_nhds (x := (2 : ℝ))).mul
          ((((hP.2.1 i).continuous.tendsto xs).comp hxψ).add (hlam i))
        rw [add_zero] at h
        exact h.smul (((AugLagFeasAux.hgcont (hP.2.1 i)).tendsto xs).comp hxψ)
      have hB : Tendsto (fun m => ∑ i, (2 * max (P.g1 i (x (ψ (m + 1)))
          + muBar (ψ (m + 1)) i / ρ (ψ (m + 1))) 0) • gradient (P.g1 i) (x (ψ (m + 1))))
          atTop (𝓝 (∑ i, (2 * max (P.g1 i xs) 0) • gradient (P.g1 i) xs)) := by
        refine tendsto_finsetSum _ fun i _ => ?_
        have h0 := ((((hP.2.2.1 i).continuous.tendsto xs).comp hxψ).add (hmu i))
        rw [add_zero] at h0
        have h := (tendsto_const_nhds (x := (2 : ℝ))).mul (h0.max (tendsto_const_nhds (x := (0 : ℝ))))
        exact h.smul (((AugLagFeasAux.hgcont (hP.2.2.1 i)).tendsto xs).comp hxψ)
      have hF : Tendsto (fun m => (ρ (ψ (m + 1)))⁻¹ • gradient P.f (x (ψ (m + 1)))) atTop
          (𝓝 ((0 : ℝ) • gradient P.f xs)) :=
        hinvρ.smul (((AugLagFeasAux.hgcont hP.1).tendsto xs).comp hxψ)
      have hlim := (hF.add (tendsto_const_nhds (x := (1 / 2 : ℝ)).smul hA)).add
        (tendsto_const_nhds (x := (1 / 2 : ℝ)).smul hB)
      rw [zero_smul, zero_add, ← smul_add] at hlim
      refine hlim.congr (fun m => ?_)
      have hρne : ρ (ψ (m + 1)) ≠ 0 := (hρψpos m).ne'
      have hh : (ρ (ψ (m + 1)))⁻¹ * (ρ (ψ (m + 1)) / 2) = 1 / 2 := by field_simp
      rw [AugLagFeasAux.grad_augLag P hP, smul_add, smul_add, smul_smul, smul_smul, hh]
    · -- complementarity
      intro j hj
      have h := (((hP.2.2.2.2 j).continuous.tendsto xs).comp hxψ).add hεψ
      rw [add_zero] at h
      filter_upwards [Filter.Tendsto.eventually_lt_const hj h] with m hm
      show (ρ (ψ (m + 1)))⁻¹ * u (ψ (m + 1)) j = 0
      rw [F3 _ (hψ'1 m) j (by simp only [Function.comp] at hm; linarith), mul_zero]
    · -- residual
      have hlim : Tendsto (fun m => ε (ψ (m + 1)) / ρ1) atTop (𝓝 0) := by
        simpa using hεψ.div_const ρ1
      refine squeeze_zero_norm (fun m => ?_) hlim
      have hk1 := hψ'1 m
      have hρk := hρψpos m
      have hρge' := hρge _ hk1
      have hε' := hε0 (ψ (m + 1))
      have e : (ρ (ψ (m + 1)))⁻¹ • gradient (fun y => augLag P y (lamBar (ψ (m + 1)))
            (muBar (ψ (m + 1))) (ρ (ψ (m + 1)))) (x (ψ (m + 1)))
          + ∑ i, ((ρ (ψ (m + 1)))⁻¹ * v (ψ (m + 1)) i) • gradient (P.h2 i) (x (ψ (m + 1)))
          + ∑ j, ((ρ (ψ (m + 1)))⁻¹ * u (ψ (m + 1)) j) • gradient (P.g2 j) (x (ψ (m + 1)))
          = (ρ (ψ (m + 1)))⁻¹ • (gradient (fun y => augLag P y (lamBar (ψ (m + 1)))
            (muBar (ψ (m + 1))) (ρ (ψ (m + 1)))) (x (ψ (m + 1)))
          + ∑ i, v (ψ (m + 1)) i • gradient (P.h2 i) (x (ψ (m + 1)))
          + ∑ j, u (ψ (m + 1)) j • gradient (P.g2 j) (x (ψ (m + 1)))) := by
        simp only [smul_add, Finset.smul_sum, smul_smul]
      rw [e, norm_smul, norm_inv, Real.norm_of_nonneg hρk.le]
      calc (ρ (ψ (m + 1)))⁻¹ * ‖_‖ ≤ (ρ (ψ (m + 1)))⁻¹ * ε (ψ (m + 1)) :=
            mul_le_mul_of_nonneg_left (F1 _ hk1) (inv_nonneg.2 hρk.le)
        _ = ε (ψ (m + 1)) / ρ (ψ (m + 1)) := by rw [inv_mul_eq_div]
        _ ≤ ε (ψ (m + 1)) / ρ1 := by gcongr
