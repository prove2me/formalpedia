-- Prove2me | solution 1 for ArmijoGrad.Conv.convergence_theorem
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T15:37:29.54076+00:00
-- url     : https://prove2.me/submissions/04f5ad55-f5f6-4bdc-8c1b-4d2e8bf8313f

import Mathlib
import Definitions.Def_ArmijoGrad_Conv_Setting

open Filter Topology


namespace ArmijoGrad.Conv

theorem gntz_core {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hbdd : BddBelow (Set.range f)) (x0 : EuclideanSpace ℝ (Fin n)) (δ : ℝ) (hδ : 0 < δ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx0 : x 0 = x0)
    (hseq : ∀ k, x (k + 1) ∈ sdSet f (x k) δ) :
    Tendsto (fun k => ‖gradient f (x k)‖) atTop (𝓝 0) := by
  obtain ⟨lb, hlb⟩ := hbdd
  have hstep : ∀ k, f (x (k+1)) ≤ f (x k) - δ * ‖gradient f (x k)‖ ^ 2 := by
    intro k
    obtain ⟨t, -, -, h⟩ := hseq k
    linarith
  have hsum : ∀ N, ∑ k ∈ Finset.range N, ‖gradient f (x k)‖ ^ 2 ≤ (f (x 0) - lb) / δ := by
    intro N
    have : δ * ∑ k ∈ Finset.range N, ‖gradient f (x k)‖ ^ 2 ≤ f (x 0) - f (x N) := by
      induction N with
      | zero => simp
      | succ N ih => rw [Finset.sum_range_succ, mul_add]; linarith [hstep N]
    have hl : lb ≤ f (x N) := hlb ⟨x N, rfl⟩
    rw [le_div_iff₀ hδ]; linarith
  have hs : Summable (fun k => ‖gradient f (x k)‖ ^ 2) :=
    summable_of_sum_range_le (fun k => by positivity) hsum
  have h2 := hs.tendsto_atTop_zero
  have h3 := h2.sqrt
  simpa [Real.sqrt_sq (norm_nonneg _)] using h3

/-- fencing lemma -/
theorem fence_core (φ : ℝ → ℝ) (c t : ℝ) (hφ : ContinuousOn φ (Set.Icc 0 t)) (h0 : φ 0 ≤ c)
    (hd : ∀ u ∈ Set.Ico 0 t, φ u = c → ∃ d < 0, HasDerivAt φ d u) :
    ∀ u ∈ Set.Icc 0 t, φ u ≤ c := by
  intro u hu
  by_cases ht : 0 ≤ t
  swap
  · exact absurd (hu.1.trans hu.2) ht
  change u ∈ {x | φ x ≤ c}
  revert u
  change Set.Icc 0 t ⊆ { x | φ x ≤ c }
  set s := { x | φ x ≤ c } ∩ Set.Icc 0 t
  have : IsClosed s := by
    simp only [s, Set.inter_comm]
    exact hφ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  apply this.Icc_subset_of_forall_exists_gt h0
  rintro x ⟨hxB : φ x ≤ c, xab⟩ y hy
  rcases hxB.lt_or_eq with hxB | hxB
  · refine Filter.nonempty_of_mem (Filter.inter_mem ?_ (Ioc_mem_nhdsGT hy))
    have : ∀ᶠ z in 𝓝[Set.Icc 0 t] x, φ z < c :=
      hφ x (Set.Ico_subset_Icc_self xab) (IsOpen.mem_nhds isOpen_Iio hxB)
    have : ∀ᶠ z in 𝓝[>] x, φ z < c := nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem xab) this
    exact this.mono fun y => le_of_lt
  · obtain ⟨d, hd0, hdd⟩ := hd x xab hxB
    have HB : ∀ᶠ z in 𝓝[>] x, slope φ x z < 0 :=
      (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).1 hdd.hasDerivWithinAt
        (Iio_mem_nhds hd0)
    have HB2 : ∀ᶠ z in 𝓝[>] x, z ∈ Set.Ioc x y := Ioc_mem_nhdsGT hy
    obtain ⟨z, hz1, hz2⟩ := (HB.and HB2).exists
    refine ⟨z, ?_, hz2⟩
    have hzx : 0 < z - x := sub_pos.2 hz2.1
    rw [slope_def_field, div_neg_iff] at hz1
    change φ z ≤ c
    rcases hz1 with h | h <;> linarith [h.1, h.2]


theorem line_deriv_core {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x g : EuclideanSpace ℝ (Fin n))
    (u : ℝ) (hd : DifferentiableAt ℝ f (x - u • g)) :
    HasDerivAt (fun u : ℝ => f (x - u • g)) (-(inner ℝ (gradient f (x - u • g)) g)) u := by
  have h1 : HasDerivAt (fun u : ℝ => x - u • g) (-g) u := by
    simpa using ((hasDerivAt_id u).smul_const g).const_sub x
  have h2 := hd.hasFDerivAt.comp_hasDerivAt u h1
  have h3 : (fderiv ℝ f (x - u • g)) (-g) = -(inner ℝ (gradient f (x - u • g)) g) := by
    rw [← toDual_gradient]
    simp [InnerProductSpace.toDual_apply_apply, inner_neg_right]
  rw [h3] at h2
  exact h2

theorem nonempty_core {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f)
    (x0 : EuclideanSpace ℝ (Fin n)) (K : ℝ)
    (hIII : ConditionIII f x0 K) (δ : ℝ) (hδK : δ ≤ 1 / (4 * K))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ levelSet f x0) : (sdSet f x δ).Nonempty := by
  obtain ⟨hK, ⟨hdiff, -⟩, hlip⟩ := hIII
  set g := gradient f x with hgdef
  by_cases hg : g = 0
  · refine ⟨x, 1, one_pos, ?_, ?_⟩ <;> rw [← hgdef, hg] <;> simp
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  set t := 1 / K with ht
  have htpos : 0 < t := by positivity
  have hKt : K * t = 1 := by rw [ht]; field_simp
  have hnorm : ∀ u : ℝ, 0 ≤ u → ‖(x - u • g) - x‖ = u * ‖g‖ := by
    intro u hu
    simp [norm_smul, abs_of_nonneg hu]
  -- inner product estimate
  have hinner : ∀ u : ℝ, 0 ≤ u → x - u • g ∈ levelSet f x0 →
      ‖g‖ ^ 2 - K * u * ‖g‖ ^ 2 ≤ inner ℝ (gradient f (x - u • g)) g := by
    intro u hu hy
    have hl := hlip x hx _ hy
    rw [hnorm u hu] at hl
    have h1 : inner ℝ (gradient f (x - u • g)) g
        = ‖g‖ ^ 2 + inner ℝ (gradient f (x - u • g) - g) g := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq]; ring
    have h2 := real_inner_le_norm (gradient f (x - u • g) - g) g
    have h3 : -(inner ℝ (gradient f (x - u • g) - g) g) ≤ ‖gradient f (x - u • g) - g‖ * ‖g‖ := by
      have h := abs_real_inner_le_norm (gradient f (x - u • g) - g) g
      linarith [neg_abs_le (inner ℝ (gradient f (x - u • g) - g) g)]
    have h4 : ‖gradient f (x - u • g) - g‖ * ‖g‖ ≤ K * (u * ‖g‖) * ‖g‖ :=
      mul_le_mul_of_nonneg_right hl (norm_nonneg _)
    nlinarith
  have hcont : ContinuousOn (fun u : ℝ => f (x - u • g)) (Set.Icc 0 t) :=
    (hf.comp (continuous_const.sub (continuous_id.smul continuous_const))).continuousOn
  have hfence := fence_core (fun u : ℝ => f (x - u • g)) (f x) t hcont (by simp) (by
    intro u hu hEq
    have hy : x - u • g ∈ levelSet f x0 := by
      show f (x - u • g) ≤ f x0
      have : f (x - u • g) = f x := hEq
      rw [this]; exact hx
    refine ⟨_, ?_, line_deriv_core f x g u (hdiff _ hy)⟩
    have := hinner u hu.1 hy
    have hKu : K * u < 1 := by
      have : K * u < K * t := mul_lt_mul_of_pos_left hu.2 hK
      linarith
    have : 0 < ‖g‖ ^ 2 - K * u * ‖g‖ ^ 2 := by
      have : 0 < ‖g‖ ^ 2 := by positivity
      nlinarith
    linarith)
  have hinL : ∀ u ∈ Set.Icc 0 t, x - u • g ∈ levelSet f x0 := by
    intro u hu
    show f (x - u • g) ≤ f x0
    exact (hfence u hu).trans hx
  have hdesc := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := t)
    (f := fun u : ℝ => f (x - u • g))
    (f' := fun u => -(inner ℝ (gradient f (x - u • g)) g)) hcont
    (fun u hu => (line_deriv_core f x g u
      (hdiff _ (hinL u (Set.Ico_subset_Icc_self hu)))).hasDerivWithinAt)
    (B := fun u => f x - u * ‖g‖ ^ 2 + K / 2 * u ^ 2 * ‖g‖ ^ 2)
    (B' := fun u => -‖g‖ ^ 2 + K * u * ‖g‖ ^ 2) (by simp)
    (by fun_prop)
    (fun u _ => by
      apply HasDerivAt.hasDerivWithinAt
      have := ((hasDerivAt_const u (f x)).sub ((hasDerivAt_id' u).mul_const (‖g‖ ^ 2))).add
        (((hasDerivAt_pow 2 u).const_mul (K / 2)).mul_const (‖g‖ ^ 2))
      exact this.congr_deriv (by push_cast; ring))
    (fun u hu => by
      have := hinner u hu.1 (hinL u (Set.Ico_subset_Icc_self hu))
      show _ ≤ _
      linarith)
  have hT := hdesc (Set.right_mem_Icc.2 htpos.le)
  refine ⟨x - t • g, t, htpos, rfl, ?_⟩
  have hδ' : δ * ‖g‖ ^ 2 ≤ 1 / (4 * K) * ‖g‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hδK (by positivity)
  have : t * ‖g‖ ^ 2 - K / 2 * t ^ 2 * ‖g‖ ^ 2 = 1 / (2 * K) * ‖g‖ ^ 2 := by
    rw [ht]; field_simp; ring
  have h4 : 1 / (4 * K) * ‖g‖ ^ 2 ≤ 1 / (2 * K) * ‖g‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply one_div_le_one_div_of_le (by positivity); linarith
  linarith

theorem conv_core {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f)
    (hbdd : BddBelow (Set.range f)) (x0 : EuclideanSpace ℝ (Fin n)) (K : ℝ)
    (hIII : ConditionIII f x0 K) (xstar : EuclideanSpace ℝ (Fin n))
    (hIV : ConditionIV f x0 xstar) (δ : ℝ) (hδ : 0 < δ) (hδK : δ ≤ 1 / (4 * K)) :
    (∀ x ∈ levelSet f x0, (sdSet f x δ).Nonempty ∧ sdSet f x δ ⊆ levelSet f x0) ∧
      ∀ x : ℕ → EuclideanSpace ℝ (Fin n), x 0 = x0 → (∀ k, x (k + 1) ∈ sdSet f (x k) δ) →
        Tendsto x atTop (𝓝 xstar) := by
  have hsub : ∀ x ∈ levelSet f x0, sdSet f x δ ⊆ levelSet f x0 := by
    intro x hx y hy
    obtain ⟨t, -, -, h⟩ := hy
    show f y ≤ f x0
    have : 0 ≤ δ * ‖gradient f x‖ ^ 2 := by positivity
    have hx' : f x ≤ f x0 := hx
    linarith
  refine ⟨fun x hx => ⟨nonempty_core f hf x0 K hIII δ hδK x hx, hsub x hx⟩, ?_⟩
  intro x hx0 hseq
  have hL : ∀ k, x k ∈ levelSet f x0 := by
    intro k
    induction k with
    | zero => rw [hx0]; show f x0 ≤ f x0; exact le_rfl
    | succ k ih => exact hsub _ ih (hseq k)
  have hg := gntz_core f hbdd x0 δ hδ x hx0 hseq
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm, hmb⟩ := hIV.2.2 ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hg) m hm
  refine ⟨N, fun k hk => ?_⟩
  have h1 := hN k hk
  simp only [Real.dist_eq, sub_zero, abs_norm] at h1
  rw [dist_eq_norm]
  by_contra hc
  push_neg at hc
  have := hmb (x k) (hL k) hc
  linarith

end ArmijoGrad.Conv

open ArmijoGrad.Conv


theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f)
    (hbdd : BddBelow (Set.range f)) (x0 : EuclideanSpace ℝ (Fin n)) (K : ℝ)
    (hIII : ConditionIII f x0 K) (xstar : EuclideanSpace ℝ (Fin n))
    (hIV : ConditionIV f x0 xstar) (δ : ℝ) (hδ : 0 < δ) (hδK : δ ≤ 1 / (4 * K)) :
    (∀ x ∈ levelSet f x0, (sdSet f x δ).Nonempty ∧ sdSet f x δ ⊆ levelSet f x0) ∧
      ∀ x : ℕ → EuclideanSpace ℝ (Fin n), x 0 = x0 → (∀ k, x (k + 1) ∈ sdSet f (x k) δ) →
        Tendsto x atTop (𝓝 xstar) := by
  exact conv_core f hf hbdd x0 K hIII xstar hIV δ hδ hδK
