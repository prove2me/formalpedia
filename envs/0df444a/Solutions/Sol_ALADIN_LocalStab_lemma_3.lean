-- Prove2me | solution 1 for ALADIN.LocalStab.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T20:27:24.773739+00:00
-- url     : https://prove2.me/submissions/b92e4d41-cbf2-4ea4-8472-12ac6031a512

import Mathlib
import Definitions.Def_ALADIN_LocalStab_Problem
import Definitions.Def_ALADIN_LocalStab_Decoupled

set_option autoImplicit false

open Matrix

namespace ALADIN.LocalStab.Aux

/-- fderiv along a line, read off a one-dimensional derivative. -/
lemma fderiv_apply_of_line {n : ℕ} {g : (Fin n → ℝ) → ℝ} {ξ v : Fin n → ℝ} {a : ℝ}
    (hd : DifferentiableAt ℝ g ξ) (h : HasDerivAt (fun t : ℝ => g (ξ + t • v)) a 0) :
    fderiv ℝ g ξ v = a := by
  have h1 : HasDerivAt (fun t : ℝ => ξ + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add ξ
  have h2 : HasDerivAt (fun t : ℝ => g (ξ + t • v)) (fderiv ℝ g ξ v) 0 := by
    have := hd.hasFDerivAt
    have h3 : HasFDerivAt g (fderiv ℝ g ξ) (ξ + (0:ℝ) • v) := by simpa using this
    exact h3.comp_hasDerivAt (0:ℝ) h1
  exact h2.unique h

set_option maxSynthPendingDepth 3 in
/-- Uniform second-order Taylor estimate for a `C²` function near a point. -/
lemma taylor2 {n : ℕ} (g : (Fin n → ℝ) → ℝ) (hg : ContDiff ℝ 2 g) (z₀ : Fin n → ℝ)
    (η : ℝ) (hη : 0 < η) :
    ∃ r > 0, ∀ ξ ∈ Metric.ball z₀ r, ∀ ζ ∈ Metric.ball z₀ r,
      |g ζ - g ξ - fderiv ℝ g ξ (ζ - ξ) - (1/2) * fderiv ℝ (fderiv ℝ g) z₀ (ζ - ξ) (ζ - ξ)|
        ≤ η * ‖ζ - ξ‖ ^ 2 := by
  have hD : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  have hDdiff : Differentiable ℝ (fderiv ℝ g) := hD.differentiable (by norm_num)
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ g)) := hD.continuous_fderiv (by norm_num)
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hopen : IsOpen {y | ‖fderiv ℝ (fderiv ℝ g) y - fderiv ℝ (fderiv ℝ g) z₀‖ < η} :=
    isOpen_lt ((hD2c.sub continuous_const).norm) continuous_const
  have hz : z₀ ∈ {y | ‖fderiv ℝ (fderiv ℝ g) y - fderiv ℝ (fderiv ℝ g) z₀‖ < η} := by
    simp [sub_self, hη]
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen z₀ hz
  refine ⟨r, hr, ?_⟩
  intro ξ hξ ζ hζ
  set D2 := fderiv ℝ (fderiv ℝ g) z₀ with hD2
  -- Step 1: ‖D w - D ξ - D2 (w - ξ)‖ ≤ η ‖w - ξ‖ on the ball
  have step1 : ∀ w ∈ Metric.ball z₀ r,
      ‖fderiv ℝ g w - fderiv ℝ g ξ - D2 (w - ξ)‖ ≤ η * ‖w - ξ‖ := by
    intro w hw
    let F : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ) := fun y => fderiv ℝ g y - D2 y
    have hFd : ∀ y, HasFDerivAt F (fderiv ℝ (fderiv ℝ g) y - D2) y := by
      intro y
      exact (hDdiff y).hasFDerivAt.sub D2.hasFDerivAt
    have hb : ∀ y ∈ Metric.ball z₀ r, ‖fderiv ℝ F y‖ ≤ η := by
      intro y hy
      rw [(hFd y).fderiv]
      exact (hball hy).le
    have := (convex_ball z₀ r).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => (hFd y).differentiableAt) hb hξ hw
    have e : F w - F ξ = fderiv ℝ g w - fderiv ℝ g ξ - D2 (w - ξ) := by
      simp only [F, map_sub]; abel
    rw [e] at this; exact this
  -- Step 2: one-dimensional estimate along the segment
  set v := ζ - ξ with hv
  let φ : ℝ → ℝ := fun t => g (ξ + t • v) - t * fderiv ℝ g ξ v - t ^ 2 / 2 * D2 v v
  let φ' : ℝ → ℝ := fun t => fderiv ℝ g (ξ + t • v) v - fderiv ℝ g ξ v - t * D2 v v
  have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, ξ + t • v ∈ Metric.ball z₀ r := by
    intro t ht
    have : ξ + t • v = (1 - t) • ξ + t • ζ := by
      simp only [hv, smul_sub, sub_smul, one_smul]; abel
    rw [this]
    exact (convex_ball z₀ r) hξ hζ (by linarith [ht.2]) ht.1 (by ring)
  have hderiv : ∀ t, HasDerivAt φ (φ' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => ξ + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add ξ
    have hg1 : HasDerivAt (fun t : ℝ => g (ξ + t • v)) (fderiv ℝ g (ξ + t • v) v) t :=
      (hgd (ξ + t • v)).hasFDerivAt.comp_hasDerivAt t h1
    have h2 : HasDerivAt (fun t : ℝ => t * fderiv ℝ g ξ v) (fderiv ℝ g ξ v) t := by
      simpa using (hasDerivAt_id t).mul_const (fderiv ℝ g ξ v)
    have h3 : HasDerivAt (fun t : ℝ => t ^ 2 / 2 * D2 v v) (t * D2 v v) t := by
      exact (((hasDerivAt_pow 2 t).div_const 2).mul_const (D2 v v)).congr_deriv
        (by rw [show (2:ℕ) - 1 = 1 from rfl]; push_cast; ring)
    exact (hg1.sub h2).sub h3
  have hbound : ∀ t ∈ Set.Ico (0:ℝ) 1, ‖φ' t‖ ≤ η * ‖v‖ ^ 2 := by
    intro t ht
    have hts : ξ + t • v ∈ Metric.ball z₀ r := hseg t ⟨ht.1, ht.2.le⟩
    have s1 := step1 _ hts
    have e1 : ξ + t • v - ξ = t • v := by abel
    rw [e1] at s1
    have e2 : φ' t = (fderiv ℝ g (ξ + t • v) - fderiv ℝ g ξ - D2 (t • v)) v := by
      simp only [φ', _root_.sub_apply, map_smul, _root_.smul_apply,
        smul_eq_mul]
    rw [e2]
    calc ‖(fderiv ℝ g (ξ + t • v) - fderiv ℝ g ξ - D2 (t • v)) v‖
        ≤ ‖fderiv ℝ g (ξ + t • v) - fderiv ℝ g ξ - D2 (t • v)‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (η * ‖t • v‖) * ‖v‖ := by gcongr
      _ ≤ η * ‖v‖ ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
          have : t * ‖v‖ ≤ ‖v‖ := by
            have := norm_nonneg v
            nlinarith [ht.2]
          have h5 := mul_le_mul_of_nonneg_right this (norm_nonneg v)
          have h6 := mul_le_mul_of_nonneg_left h5 hη.le
          calc η * (t * ‖v‖) * ‖v‖ = η * (t * ‖v‖ * ‖v‖) := by ring
            _ ≤ η * (‖v‖ * ‖v‖) := h6
            _ = η * ‖v‖ ^ 2 := by ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := φ) (f' := φ') (C := η * ‖v‖ ^ 2)
    (fun t _ => (hderiv t).hasDerivWithinAt) hbound 1 ⟨by norm_num, le_refl _⟩
  have e3 : φ 1 - φ 0 = g ζ - g ξ - fderiv ℝ g ξ (ζ - ξ) - (1/2) * D2 (ζ - ξ) (ζ - ξ) := by
    simp only [φ, hv, one_smul, zero_smul, add_zero]
    have : ξ + (ζ - ξ) = ζ := by abel
    rw [this]; ring
  rw [← e3, ← Real.norm_eq_abs]
  simpa using key


lemma quad_coercive {n : ℕ} (Q : (Fin n → ℝ) → ℝ) (hc : Continuous Q)
    (hhom : ∀ (t : ℝ) (d : Fin n → ℝ), Q (t • d) = t ^ 2 * Q d)
    (hpos : ∀ d, d ≠ 0 → 0 < Q d) : ∃ m > 0, ∀ d, m * ‖d‖ ^ 2 ≤ Q d := by
  have hQ0 : Q 0 = 0 := by
    have := hhom 0 0; simpa using this
  have hsph : ∀ d : Fin n → ℝ, d ≠ 0 → ‖d‖⁻¹ • d ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    intro d hd
    have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hdn.ne']
  by_cases hne : (Metric.sphere (0 : Fin n → ℝ) 1).Nonempty
  · obtain ⟨u, hu, hmin⟩ :=
      (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMinOn hne hc.continuousOn
    have hu1 : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
    have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu1; exact zero_ne_one hu1
    refine ⟨Q u, hpos u hu0, fun d => ?_⟩
    by_cases hd : d = 0
    · subst hd; simp [hQ0]
    · have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd
      have hQw : Q u ≤ Q (‖d‖⁻¹ • d) := hmin (hsph d hd)
      have e : Q d = ‖d‖ ^ 2 * Q (‖d‖⁻¹ • d) := by
        rw [← hhom, smul_smul, mul_inv_cancel₀ hdn.ne', one_smul]
      rw [e]
      have := sq_nonneg ‖d‖
      nlinarith
  · refine ⟨1, one_pos, fun d => ?_⟩
    by_cases hd : d = 0
    · subst hd; simp [hQ0]
    · exact absurd ⟨_, hsph d hd⟩ hne

lemma dot_mulVec_bound {n m : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) :
    ∃ C ≥ 0, ∀ (a : Fin m → ℝ) (v : Fin n → ℝ), |a ⬝ᵥ (M *ᵥ v)| ≤ C * ‖a‖ * ‖v‖ := by
  refine ⟨∑ k, ∑ l, |M k l|, by positivity, fun a v => ?_⟩
  have hk : ∀ k, |a k * ∑ l, M k l * v l| ≤ ‖a‖ * ((∑ l, |M k l|) * ‖v‖) := by
    intro k
    rw [abs_mul]
    apply mul_le_mul (by simpa [Real.norm_eq_abs] using norm_le_pi_norm a k) _ (abs_nonneg _)
      (norm_nonneg _)
    calc |∑ l, M k l * v l| ≤ ∑ l, |M k l * v l| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l, |M k l| * ‖v‖ := by
          gcongr with l
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v l) (abs_nonneg _)
      _ = (∑ l, |M k l|) * ‖v‖ := by rw [Finset.sum_mul]
  calc |a ⬝ᵥ (M *ᵥ v)| = |∑ k, a k * ∑ l, M k l * v l| := by simp [dotProduct, mulVec]
    _ ≤ ∑ k, |a k * ∑ l, M k l * v l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ‖a‖ * ((∑ l, |M k l|) * ‖v‖) := Finset.sum_le_sum fun k _ => hk k
    _ = (∑ k, ∑ l, |M k l|) * ‖a‖ * ‖v‖ := by rw [← Finset.mul_sum, ← Finset.sum_mul]; ring

lemma sym_dot {n : ℕ} {S : Matrix (Fin n) (Fin n) ℝ} (hS : Sᵀ = S) (v w : Fin n → ℝ) :
    v ⬝ᵥ (S *ᵥ w) = w ⬝ᵥ (S *ᵥ v) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS, dotProduct_comm]

lemma exists_pos_le_all {k : ℕ} (f : Fin k → ℝ) (hf : ∀ j, 0 < f j) :
    ∃ r > 0, ∀ j, r ≤ f j := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨1, one_pos, fun j => j.elim0⟩
  · obtain ⟨j0, -, hj0⟩ := Finset.exists_min_image Finset.univ f ⟨⟨0, hk⟩, Finset.mem_univ _⟩
    exact ⟨f j0, hf j0, fun j => hj0 j (Finset.mem_univ _)⟩

lemma hasFDerivAt_lagBlock {N n m nh : ℕ} (P : Problem N n m nh) (i : Fin N)
    (hf : ContDiff ℝ 2 (P.f i)) (hh : ContDiff ℝ 2 (P.h i)) (κi : Fin nh → ℝ) (ξ : Fin n → ℝ) :
    HasFDerivAt (P.lagBlock i κi)
      (fderiv ℝ (P.f i) ξ + ∑ j, κi j • fderiv ℝ (fun ξ' => P.h i ξ' j) ξ) ξ := by
  have hj : ∀ j, ContDiff ℝ 2 (fun ξ' => P.h i ξ' j) := fun j => contDiff_pi.mp hh j
  have h1 := ((hf.differentiable (by norm_num)) ξ).hasFDerivAt
  have h2 : HasFDerivAt (fun ξ' => ∑ j, κi j * P.h i ξ' j)
      (∑ j, κi j • fderiv ℝ (fun ξ' => P.h i ξ' j) ξ) ξ := by
    have := HasFDerivAt.sum (u := Finset.univ) (A := fun j ξ' => κi j * P.h i ξ' j)
      (fun j _ => (((hj j).differentiable (by norm_num)) ξ).hasFDerivAt.const_mul (κi j))
    have e : (fun ξ' => ∑ j, κi j * P.h i ξ' j) = ∑ j, (fun ξ' => κi j * P.h i ξ' j) := by
      ext ξ'; simp [Finset.sum_apply]
    rw [e]; exact this
  exact h1.add h2

lemma fderiv_lagBlock_apply {N n m nh : ℕ} (P : Problem N n m nh) (i : Fin N)
    (hf : ContDiff ℝ 2 (P.f i)) (hh : ContDiff ℝ 2 (P.h i)) (κi : Fin nh → ℝ) (ξ v : Fin n → ℝ) :
    fderiv ℝ (P.lagBlock i κi) ξ v
      = fderiv ℝ (P.f i) ξ v + ∑ j, κi j * fderiv ℝ (fun ξ' => P.h i ξ' j) ξ v := by
  rw [(hasFDerivAt_lagBlock P i hf hh κi ξ).fderiv]
  simp

lemma contDiff_lagBlock {N n m nh : ℕ} (P : Problem N n m nh) (i : Fin N)
    (hf : ContDiff ℝ 2 (P.f i)) (hh : ContDiff ℝ 2 (P.h i)) (κi : Fin nh → ℝ) :
    ContDiff ℝ 2 (P.lagBlock i κi) := by
  have hj : ∀ j, ContDiff ℝ 2 (fun ξ' => P.h i ξ' j) := fun j => contDiff_pi.mp hh j
  unfold Problem.lagBlock
  exact hf.add (ContDiff.sum fun j _ => contDiff_const.mul (hj j))


set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 1000000 in
/-- Uniform strong-convexity inequality for the decoupled Lagrangians near `z`. -/
lemma key_ineq {N n m nh : ℕ} (P : Problem N n m nh) (i : Fin N)
    (hf : ContDiff ℝ 2 (P.f i)) (hh : ContDiff ℝ 2 (P.h i))
    (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ) (hS : (Sig i)ᵀ = Sig i)
    (z : Fin n → ℝ) (κi : Fin nh → ℝ) (ρ : ℝ)
    (hHess : ∀ d : Fin n → ℝ, d ≠ 0 →
      0 < hessQuad (P.lagBlock i κi) z d + ρ * (d ⬝ᵥ (Sig i *ᵥ d))) :
    ∃ r > 0, ∃ μ > 0, ∃ δ > 0, ∀ (ν : Fin nh → ℝ), (∀ j, |ν j - κi j| ≤ δ) →
      ∀ (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ), ∀ ξ ∈ Metric.ball z r, ∀ ζ ∈ Metric.ball z r,
        decoupledObjective P ρ Sig x lam i ξ + ∑ j, ν j * P.h i ξ j
          + (fderiv ℝ (P.f i) ξ (ζ - ξ) + lam ⬝ᵥ (P.A i *ᵥ (ζ - ξ))
             + ρ * ((ξ - x i) ⬝ᵥ (Sig i *ᵥ (ζ - ξ)))
             + ∑ j, ν j * fderiv ℝ (fun ξ' => P.h i ξ' j) ξ (ζ - ξ))
          + μ * ‖ζ - ξ‖ ^ 2
        ≤ decoupledObjective P ρ Sig x lam i ζ + ∑ j, ν j * P.h i ζ j := by
  have hj : ∀ j, ContDiff ℝ 2 (fun ξ' => P.h i ξ' j) := fun j => contDiff_pi.mp hh j
  have hL := contDiff_lagBlock P i hf hh κi
  set D2L := fderiv ℝ (fderiv ℝ (P.lagBlock i κi)) z with hD2L
  obtain ⟨m₀, hm₀, hcoer⟩ := quad_coercive
    (fun d => D2L d d + ρ * (d ⬝ᵥ (Sig i *ᵥ d)))
    (by
      have h1 : Continuous fun d : Fin n → ℝ => D2L d d :=
        D2L.continuous₂.comp (continuous_id.prodMk continuous_id)
      have h2 : Continuous fun d : Fin n → ℝ => d ⬝ᵥ (Sig i *ᵥ d) := by
        simp only [dotProduct, mulVec]; fun_prop
      exact h1.add (continuous_const.mul h2))
    (by
      intro t d
      simp only [map_smul, _root_.smul_apply, smul_eq_mul, mulVec_smul,
        dotProduct_smul, smul_dotProduct]
      ring)
    (fun d hd => hHess d hd)
  obtain ⟨rL, hrL, hTL⟩ := taylor2 _ hL z (m₀ / 8) (by positivity)
  have hTj := fun j => taylor2 _ (hj j) z 1 one_pos
  choose rj hrj hTj using hTj
  obtain ⟨rH, hrH, hrHle⟩ := exists_pos_le_all rj hrj
  set Cj : Fin nh → ℝ := fun j => ‖fderiv ℝ (fderiv ℝ (fun ξ' => P.h i ξ' j)) z‖ / 2 + 1
    with hCj
  set C : ℝ := ∑ j, Cj j with hC
  have hCj0 : ∀ j, 0 ≤ Cj j := fun j => by simp only [hCj]; positivity
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => hCj0 j
  refine ⟨min rL rH, lt_min hrL hrH, m₀ / 4, by positivity, m₀ / 8 / (C + 1), by positivity, ?_⟩
  intro ν hν x lam ξ hξ ζ hζ
  set v := ζ - ξ with hv
  have hξL : ξ ∈ Metric.ball z rL := Metric.ball_subset_ball (min_le_left _ _) hξ
  have hζL : ζ ∈ Metric.ball z rL := Metric.ball_subset_ball (min_le_left _ _) hζ
  have hξj : ∀ j, ξ ∈ Metric.ball z (rj j) := fun j =>
    Metric.ball_subset_ball ((min_le_right _ _).trans (hrHle j)) hξ
  have hζj : ∀ j, ζ ∈ Metric.ball z (rj j) := fun j =>
    Metric.ball_subset_ball ((min_le_right _ _).trans (hrHle j)) hζ
  -- remainder of the h_j
  set R : Fin nh → ℝ := fun j => P.h i ζ j - P.h i ξ j - fderiv ℝ (fun ξ' => P.h i ξ' j) ξ v
    with hR
  have hRb : ∀ j, |R j| ≤ Cj j * ‖v‖ ^ 2 := by
    intro j
    have t1 := hTj j ξ (hξj j) ζ (hζj j)
    have t2 := ContinuousLinearMap.le_opNorm₂ (fderiv ℝ (fderiv ℝ (fun ξ' => P.h i ξ' j)) z) v v
    rw [← hv] at t1
    have t3 := abs_le.mp t1
    have t4 := abs_le.mp (le_trans (le_of_eq (Real.norm_eq_abs _).symm) t2)
    simp only [hR, hCj]
    rw [abs_le]
    constructor <;> nlinarith [norm_nonneg v, sq_nonneg ‖v‖]
  set Sd : ℝ := ∑ j, (ν j - κi j) * R j with hSd
  have hSdb : |Sd| ≤ m₀ / 8 * ‖v‖ ^ 2 := by
    calc |Sd| ≤ ∑ j, |(ν j - κi j) * R j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, m₀ / 8 / (C + 1) * (Cj j * ‖v‖ ^ 2) := by
          gcongr with j
          rw [abs_mul]
          exact mul_le_mul (hν j) (hRb j) (abs_nonneg _) (by positivity)
      _ = m₀ / 8 * (C / (C + 1)) * ‖v‖ ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.sum_mul]; field_simp; rfl
      _ ≤ m₀ / 8 * 1 * ‖v‖ ^ 2 := by
          gcongr
          rw [div_le_one (by positivity)]; linarith
      _ = m₀ / 8 * ‖v‖ ^ 2 := by ring
  -- Taylor for the block Lagrangian
  have tL := hTL ξ hξL ζ hζL
  rw [← hv, fderiv_lagBlock_apply P i hf hh κi ξ v] at tL
  have tL' := abs_le.mp tL
  have hco := hcoer v
  -- algebraic identities
  have hlin : lam ⬝ᵥ (P.A i *ᵥ ζ) = lam ⬝ᵥ (P.A i *ᵥ ξ) + lam ⬝ᵥ (P.A i *ᵥ v) := by
    rw [← dotProduct_add, ← mulVec_add, hv, add_sub_cancel]
  have hquad : (ζ - x i) ⬝ᵥ (Sig i *ᵥ (ζ - x i))
      = (ξ - x i) ⬝ᵥ (Sig i *ᵥ (ξ - x i)) + 2 * ((ξ - x i) ⬝ᵥ (Sig i *ᵥ v))
        + v ⬝ᵥ (Sig i *ᵥ v) := by
    have e : ζ - x i = (ξ - x i) + v := by rw [hv]; abel
    rw [e]
    simp only [mulVec_add, dotProduct_add, add_dotProduct]
    rw [sym_dot hS v (ξ - x i)]
    ring
  have hsum : ∑ j, ν j * P.h i ζ j = ∑ j, ν j * P.h i ξ j
      + ∑ j, ν j * fderiv ℝ (fun ξ' => P.h i ξ' j) ξ v
      + ∑ j, κi j * R j + Sd := by
    rw [hSd, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hR]; ring
  have hκsum : ∑ j, κi j * R j = ∑ j, κi j * P.h i ζ j - ∑ j, κi j * P.h i ξ j
      - ∑ j, κi j * fderiv ℝ (fun ξ' => P.h i ξ' j) ξ v := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hR]; ring
  have hSdl := (abs_le.mp hSdb).1
  simp only [decoupledObjective, Problem.lagBlock] at tL' ⊢
  rw [hlin, hquad, hsum]
  nlinarith [hco, tL'.1, hSdl, hκsum]


lemma obj_contDiff {N n m nh : ℕ} (P : Problem N n m nh) (i : Fin N) (hf : ContDiff ℝ 2 (P.f i))
    (ρ : ℝ) (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ) (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ) :
    ContDiff ℝ 2 (decoupledObjective P ρ Sig x lam i) := by
  unfold decoupledObjective
  simp only [dotProduct, mulVec]
  fun_prop

lemma feas_closed {N n m nh : ℕ} (P : Problem N n m nh) (i : Fin N) (hh : ContDiff ℝ 2 (P.h i)) :
    IsClosed (decoupledFeasibleSet P i) := by
  have : decoupledFeasibleSet P i = ⋂ j, {ξ | P.h i ξ j ≤ 0} := by
    ext ξ; simp [decoupledFeasibleSet]
  rw [this]
  exact isClosed_iInter fun j =>
    isClosed_le ((contDiff_pi.mp hh j).continuous) continuous_const

lemma exist_block {N n m nh : ℕ} (P : Problem N n m nh) (i : Fin N)
    (hf : ContDiff ℝ 2 (P.f i)) (hh : ContDiff ℝ 2 (P.h i))
    (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (z : Fin n → ℝ) (lamS : Fin m → ℝ) (κi : Fin nh → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hfeas : ∀ j, P.h i z j ≤ 0)
    (hstat : ∀ d, fderiv ℝ (P.f i) z d + lamS ⬝ᵥ (P.A i *ᵥ d)
      + ∑ j, κi j * fderiv ℝ (fun ξ => P.h i ξ j) z d = 0)
    (hκ : ∀ j, 0 ≤ κi j) (hcomp : ∀ j, κi j * P.h i z j = 0)
    (r μ : ℝ) (hr : 0 < r) (hμ : 0 < μ)
    (hkey : ∀ (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ), ∀ ξ ∈ Metric.ball z r,
      ∀ ζ ∈ Metric.ball z r,
        decoupledObjective P ρ Sig x lam i ξ + ∑ j, κi j * P.h i ξ j
          + (fderiv ℝ (P.f i) ξ (ζ - ξ) + lam ⬝ᵥ (P.A i *ᵥ (ζ - ξ))
             + ρ * ((ξ - x i) ⬝ᵥ (Sig i *ᵥ (ζ - ξ)))
             + ∑ j, κi j * fderiv ℝ (fun ξ' => P.h i ξ' j) ξ (ζ - ξ))
          + μ * ‖ζ - ξ‖ ^ 2
        ≤ decoupledObjective P ρ Sig x lam i ζ + ∑ j, κi j * P.h i ζ j) :
    ∃ K ≥ 0, ∃ β > 0, ∀ (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ),
      ‖x i - z‖ < β → ‖lam - lamS‖ < β →
      ∃ y, IsDecoupledLocalMin P ρ Sig x lam i y ∧ ‖y - z‖ ≤ K * (‖x i - z‖ + ‖lam - lamS‖) ∧
        ‖y - z‖ < r / 2 ∧
        ∀ η ∈ decoupledFeasibleSet P i, η ∈ Metric.closedBall z (r / 2) →
          decoupledObjective P ρ Sig x lam i y ≤ decoupledObjective P ρ Sig x lam i η := by
  obtain ⟨CA, hCA0, hCA⟩ := dot_mulVec_bound (P.A i)
  obtain ⟨CS, hCS0, hCSb⟩ := dot_mulVec_bound (Sig i)
  set K := (CA + ρ * CS) / μ with hK
  have hK0 : 0 ≤ K := by positivity
  have hbound : ∀ (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ) (y : Fin n → ℝ),
      y ∈ decoupledFeasibleSet P i → y ∈ Metric.ball z r →
      decoupledObjective P ρ Sig x lam i y ≤ decoupledObjective P ρ Sig x lam i z →
      ‖y - z‖ ≤ K * (‖x i - z‖ + ‖lam - lamS‖) := by
    intro x lam y hyf hyb hyle
    have hk := hkey x lam z (Metric.mem_ball_self hr) y hyb
    have hz0 : ∑ j, κi j * P.h i z j = 0 := Finset.sum_eq_zero fun j _ => hcomp j
    have hy0 : ∑ j, κi j * P.h i y j ≤ 0 :=
      Finset.sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (hκ j) (hyf j)
    have hst := hstat (y - z)
    have h1 := hCA (lam - lamS) (y - z)
    have h2 := hCSb (z - x i) (y - z)
    have e1 : lam ⬝ᵥ (P.A i *ᵥ (y - z))
        = lamS ⬝ᵥ (P.A i *ᵥ (y - z)) + (lam - lamS) ⬝ᵥ (P.A i *ᵥ (y - z)) := by
      rw [sub_dotProduct]; ring
    have hzx : ‖z - x i‖ = ‖x i - z‖ := norm_sub_rev _ _
    rw [hzx] at h2
    have hmain : μ * ‖y - z‖ ^ 2
        ≤ (CA * ‖lam - lamS‖ + ρ * (CS * ‖x i - z‖)) * ‖y - z‖ := by
      have a1 := (abs_le.mp h1).1
      have a2 := (abs_le.mp h2).1
      have hρa2 : -(ρ * (CS * ‖x i - z‖ * ‖y - z‖))
          ≤ ρ * ((z - x i) ⬝ᵥ (Sig i *ᵥ (y - z))) := by
        have := mul_le_mul_of_nonneg_left a2 hρ.le; linarith
      rw [e1] at hk
      linarith
    rcases (norm_nonneg (y - z)).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · have h3 : μ * ‖y - z‖ ≤ CA * ‖lam - lamS‖ + ρ * (CS * ‖x i - z‖) := by
        have := hmain; rw [pow_two, ← mul_assoc] at this
        exact le_of_mul_le_mul_right this hpos
      rw [hK, div_mul_eq_mul_div, le_div_iff₀ hμ]
      nlinarith [norm_nonneg (lam - lamS), norm_nonneg (x i - z),
        mul_nonneg hCA0 (norm_nonneg (x i - z)),
        mul_nonneg (mul_nonneg hρ.le hCS0) (norm_nonneg (lam - lamS))]
  refine ⟨K, hK0, r / (4 * (K + 1)), by positivity, ?_⟩
  intro x lam hx hlam
  have hcpt : IsCompact (decoupledFeasibleSet P i ∩ Metric.closedBall z (r / 2)) :=
    (isCompact_closedBall z (r / 2)).inter_left (feas_closed P i hh)
  have hzS : z ∈ decoupledFeasibleSet P i ∩ Metric.closedBall z (r / 2) :=
    ⟨hfeas, Metric.mem_closedBall_self (by positivity)⟩
  obtain ⟨y, hyS, hymin⟩ := hcpt.exists_isMinOn ⟨z, hzS⟩
    (obj_contDiff P i hf ρ Sig x lam).continuous.continuousOn
  have hmin' := isMinOn_iff.mp hymin
  have hyb : y ∈ Metric.ball z r := by
    have := hyS.2; rw [Metric.mem_closedBall] at this; rw [Metric.mem_ball]; linarith
  have hyB := hbound x lam y hyS.1 hyb (hmin' z hzS)
  have hlt : ‖y - z‖ < r / 2 := by
    have : K * (‖x i - z‖ + ‖lam - lamS‖) < r / 2 := by
      calc K * (‖x i - z‖ + ‖lam - lamS‖) ≤ K * (2 * (r / (4 * (K + 1)))) := by
            gcongr; linarith
        _ < r / 2 := by
            rw [show K * (2 * (r / (4 * (K + 1)))) = r / 2 * (K / (K + 1)) by
              field_simp; ring]
            have : K / (K + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
            nlinarith
    linarith
  refine ⟨y, ⟨hyS.1, ?_⟩, hyB, hlt, fun η hηf hηb => hmin' η ⟨hηf, hηb⟩⟩
  have hU : Metric.closedBall z (r / 2) ∈ nhdsWithin y (decoupledFeasibleSet P i) := by
    apply mem_nhdsWithin_of_mem_nhds
    apply Filter.mem_of_superset _ (Metric.ball_subset_closedBall)
    exact Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_eq_norm]; exact hlt)
  filter_upwards [hU, self_mem_nhdsWithin] with ξ h1 h2
  exact hmin' ξ ⟨h2, h1⟩


lemma fderiv_obj_apply {N n m nh : ℕ} (P : Problem N n m nh) (i : Fin N)
    (hf : ContDiff ℝ 2 (P.f i)) (ρ : ℝ) (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ)
    (hS : (Sig i)ᵀ = Sig i) (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ) (ξ v : Fin n → ℝ) :
    fderiv ℝ (decoupledObjective P ρ Sig x lam i) ξ v
      = fderiv ℝ (P.f i) ξ v + lam ⬝ᵥ (P.A i *ᵥ v) + ρ * ((ξ - x i) ⬝ᵥ (Sig i *ᵥ v)) := by
  apply fderiv_apply_of_line ((obj_contDiff P i hf ρ Sig x lam).differentiable (by norm_num) ξ)
  set w := ξ - x i with hw
  have hfun : (fun t : ℝ => decoupledObjective P ρ Sig x lam i (ξ + t • v))
      = fun t : ℝ => P.f i (ξ + t • v) + (lam ⬝ᵥ (P.A i *ᵥ ξ) + t * (lam ⬝ᵥ (P.A i *ᵥ v)))
        + ρ / 2 * (w ⬝ᵥ (Sig i *ᵥ w) + t * (w ⬝ᵥ (Sig i *ᵥ v) + v ⬝ᵥ (Sig i *ᵥ w))
          + t ^ 2 * (v ⬝ᵥ (Sig i *ᵥ v))) := by
    funext t
    have e : ξ + t • v - x i = w + t • v := by rw [hw]; abel
    simp only [decoupledObjective, e, mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  rw [hfun]
  have hline : HasDerivAt (fun t : ℝ => ξ + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add ξ
  have h1 : HasDerivAt (fun t : ℝ => P.f i (ξ + t • v)) (fderiv ℝ (P.f i) ξ v) 0 := by
    have hd := ((hf.differentiable (by norm_num)) ξ).hasFDerivAt
    have h3 : HasFDerivAt (P.f i) (fderiv ℝ (P.f i) ξ) (ξ + (0:ℝ) • v) := by simpa using hd
    exact h3.comp_hasDerivAt (0:ℝ) hline
  have h2 : HasDerivAt (fun t : ℝ => lam ⬝ᵥ (P.A i *ᵥ ξ) + t * (lam ⬝ᵥ (P.A i *ᵥ v)))
      (lam ⬝ᵥ (P.A i *ᵥ v)) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (lam ⬝ᵥ (P.A i *ᵥ v))).const_add
      (lam ⬝ᵥ (P.A i *ᵥ ξ))
  have h3 : HasDerivAt (fun t : ℝ => ρ / 2 * (w ⬝ᵥ (Sig i *ᵥ w)
        + t * (w ⬝ᵥ (Sig i *ᵥ v) + v ⬝ᵥ (Sig i *ᵥ w)) + t ^ 2 * (v ⬝ᵥ (Sig i *ᵥ v))))
      (ρ * (w ⬝ᵥ (Sig i *ᵥ v))) 0 := by
    have := (((((hasDerivAt_id (0:ℝ)).mul_const (w ⬝ᵥ (Sig i *ᵥ v) + v ⬝ᵥ (Sig i *ᵥ w))).const_add
      (w ⬝ᵥ (Sig i *ᵥ w))).add ((hasDerivAt_pow 2 (0:ℝ)).mul_const (v ⬝ᵥ (Sig i *ᵥ v)))).const_mul
      (ρ / 2))
    refine this.congr_deriv ?_
    rw [sym_dot hS v w]
    simp; ring
  exact (h1.add h2).add h3

lemma lin_coercive {k : ℕ} (Q : (Fin k → ℝ) → ℝ) (p : (Fin k → ℝ) → Prop) (hc : Continuous Q)
    (hp : IsClosed {d | p d}) (hps : ∀ (t : ℝ) d, p d → p (t • d))
    (hhom : ∀ (t : ℝ) d, Q (t • d) = |t| * Q d) (hpos : ∀ d, p d → d ≠ 0 → 0 < Q d) :
    ∃ c > 0, ∀ d, p d → c * ‖d‖ ≤ Q d := by
  have hQ0 : Q 0 = 0 := by
    have := hhom 0 0; simpa using this
  have hsph : ∀ d : Fin k → ℝ, p d → d ≠ 0 →
      ‖d‖⁻¹ • d ∈ Metric.sphere (0 : Fin k → ℝ) 1 ∩ {d | p d} := by
    intro d hpd hd
    have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd
    refine ⟨?_, hps _ _ hpd⟩
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hdn.ne']
  by_cases hne : (Metric.sphere (0 : Fin k → ℝ) 1 ∩ {d | p d}).Nonempty
  · obtain ⟨u, hu, hmin⟩ :=
      ((isCompact_sphere (0 : Fin k → ℝ) 1).inter_right hp).exists_isMinOn hne hc.continuousOn
    have hu1 : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu.1
    have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu1; exact zero_ne_one hu1
    refine ⟨Q u, hpos u hu.2 hu0, fun d hpd => ?_⟩
    by_cases hd : d = 0
    · subst hd; simp [hQ0]
    · have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd
      have hQw : Q u ≤ Q (‖d‖⁻¹ • d) := isMinOn_iff.mp hmin _ (hsph d hpd hd)
      have e : Q d = ‖d‖ * Q (‖d‖⁻¹ • d) := by
        rw [← abs_of_pos hdn, ← hhom, abs_of_pos hdn, smul_smul, mul_inv_cancel₀ hdn.ne',
          one_smul]
      rw [e]
      nlinarith
  · refine ⟨1, one_pos, fun d hpd => ?_⟩
    by_cases hd : d = 0
    · subst hd; simp [hQ0]
    · exact absurd ⟨_, hsph d hpd hd⟩ hne

set_option maxSynthPendingDepth 3 in
/-- Uniform LICQ for the active constraints of block `i` near `z`. -/
lemma licq_unif {N n m nh : ℕ} (P : Problem N n m nh) (i : Fin N)
    (hh : ContDiff ℝ 2 (P.h i)) (z : Fin n → ℝ)
    (hlicq : ∀ ν : Fin nh → ℝ, (∀ j, P.h i z j ≠ 0 → ν j = 0) →
      (∀ d, ∑ j, ν j * fderiv ℝ (fun ξ => P.h i ξ j) z d = 0) → ν = 0) :
    ∃ c > 0, ∃ rl > 0, ∀ ξ ∈ Metric.ball z rl, ∀ ν : Fin nh → ℝ,
      (∀ j, P.h i z j ≠ 0 → ν j = 0) →
      c * ‖ν‖ ≤ ‖∑ j, ν j • fderiv ℝ (fun ξ' => P.h i ξ' j) ξ‖ := by
  have hj : ∀ j, ContDiff ℝ 2 (fun ξ' => P.h i ξ' j) := fun j => contDiff_pi.mp hh j
  set D : Fin nh → (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] ℝ) :=
    fun j => fderiv ℝ (fun ξ' => P.h i ξ' j) with hD
  have hDc : ∀ j, Continuous (D j) := fun j => (hj j).continuous_fderiv (by norm_num)
  obtain ⟨c, hc, hcb⟩ := lin_coercive (fun ν => ‖∑ j, ν j • D j z‖)
    (fun ν => ∀ j, P.h i z j ≠ 0 → ν j = 0)
    (continuous_norm.comp (continuous_finsetSum _ fun j _ =>
      (continuous_apply j).smul continuous_const))
    (by
      have : {d : Fin nh → ℝ | ∀ j, P.h i z j ≠ 0 → d j = 0}
          = ⋂ j, {d : Fin nh → ℝ | P.h i z j ≠ 0 → d j = 0} := by
        ext d; simp only [Set.mem_setOf_eq, Set.mem_iInter]
      rw [this]
      refine isClosed_iInter fun j => ?_
      by_cases hz : P.h i z j ≠ 0
      · have e : {d : Fin nh → ℝ | P.h i z j ≠ 0 → d j = 0} = {d | d j = 0} := by
          ext d; exact ⟨fun h => h hz, fun h _ => h⟩
        rw [e]
        exact isClosed_eq (continuous_apply j) continuous_const
      · have e : {d : Fin nh → ℝ | P.h i z j ≠ 0 → d j = 0} = Set.univ := by
          ext d; exact ⟨fun _ => trivial, fun _ h => absurd h hz⟩
        rw [e]
        exact isClosed_univ)
    (fun t d hd j hj' => by simp [hd j hj'])
    (by
      intro t d
      simp only [Pi.smul_apply, smul_eq_mul, ← smul_smul, ← Finset.smul_sum, norm_smul,
        Real.norm_eq_abs])
    (by
      intro ν hν hne
      rcases (norm_nonneg (∑ j, ν j • D j z)).eq_or_lt with h0 | h0
      · exfalso; apply hne
        apply hlicq ν hν
        intro d
        have h1 : ∑ j, ν j • D j z = 0 := norm_eq_zero.mp h0.symm
        have h2 := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L d) h1
        simpa [hD] using h2
      · exact h0)
  set τ := c / (2 * (nh + 1)) with hτ
  have hτ0 : 0 < τ := by positivity
  have hcont : ∀ j, ∃ r > 0, ∀ ξ ∈ Metric.ball z r, ‖D j ξ - D j z‖ < τ := by
    intro j
    have hopen : IsOpen {y | ‖D j y - D j z‖ < τ} :=
      isOpen_lt ((hDc j).sub continuous_const).norm continuous_const
    have hz : z ∈ {y | ‖D j y - D j z‖ < τ} := by simp [hτ0]
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hopen z hz
    exact ⟨r, hr, fun ξ hξ => hb hξ⟩
  choose rj hrj hrjb using hcont
  obtain ⟨rl, hrl, hrlle⟩ := exists_pos_le_all rj hrj
  refine ⟨c / 2, by positivity, rl, hrl, fun ξ hξ ν hν => ?_⟩
  have hbase := hcb ν hν
  have hpert : ‖∑ j, ν j • (D j ξ - D j z)‖ ≤ nh * ‖ν‖ * τ := by
    calc ‖∑ j, ν j • (D j ξ - D j z)‖ ≤ ∑ j, ‖ν j • (D j ξ - D j z)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin nh, ‖ν‖ * τ := by
          gcongr with j
          rw [norm_smul]
          exact mul_le_mul (norm_le_pi_norm ν j)
            (hrjb j ξ (Metric.ball_subset_ball (hrlle j) hξ)).le (norm_nonneg _) (norm_nonneg _)
      _ = nh * ‖ν‖ * τ := by simp; ring
  have hsplit : ∑ j, ν j • D j ξ = ∑ j, ν j • D j z + ∑ j, ν j • (D j ξ - D j z) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_sub]; abel
  have htri := norm_sub_le (∑ j, ν j • D j z + ∑ j, ν j • (D j ξ - D j z))
    (∑ j, ν j • (D j ξ - D j z))
  rw [add_sub_cancel_right] at htri
  rw [hsplit]
  have hnτ : (nh : ℝ) * τ ≤ c / 2 := by
    rw [hτ]
    have : (nh : ℝ) / (nh + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc (nh : ℝ) * (c / (2 * (nh + 1))) = c / 2 * ((nh : ℝ) / (nh + 1)) := by
          field_simp
      _ ≤ c / 2 * 1 := by gcongr
      _ = c / 2 := by ring
  have : (nh : ℝ) * ‖ν‖ * τ ≤ c / 2 * ‖ν‖ := by
    have := mul_le_mul_of_nonneg_right hnτ (norm_nonneg ν); linarith
  linarith


set_option maxSynthPendingDepth 3 in
/-- Lagrange multipliers at a local minimizer on the active set, under LICQ. -/
lemma lagrange_ext {n nh : ℕ} (g : (Fin n → ℝ) → ℝ) (H : (Fin n → ℝ) → Fin nh → ℝ)
    (hg : ContDiff ℝ 2 g) (hH : ContDiff ℝ 2 H) (η : Fin n → ℝ)
    (hmin : IsLocalMinOn g {ξ | ∀ j, H η j = 0 → H ξ j = 0} η)
    (hlicq : ∀ ν : Fin nh → ℝ, (∀ j, H η j ≠ 0 → ν j = 0) →
      ∑ j, ν j • fderiv ℝ (fun ξ => H ξ j) η = 0 → ν = 0) :
    ∃ κt : Fin nh → ℝ, (∀ j, H η j ≠ 0 → κt j = 0) ∧
      ∀ v, fderiv ℝ g η v + ∑ j, κt j * fderiv ℝ (fun ξ => H ξ j) η v = 0 := by
  classical
  have hj : ∀ j, ContDiff ℝ 2 (fun ξ => H ξ j) := fun j => contDiff_pi.mp hH j
  set D : Fin nh → (Fin n → ℝ) →L[ℝ] ℝ := fun j => fderiv ℝ (fun ξ => H ξ j) η with hD
  have hset : {ξ | ∀ j, H η j = 0 → H ξ j = 0}
      = {ξ | ∀ k : {j : Fin nh // H η j = 0}, H ξ k.1 = H η k.1} := by
    ext ξ
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h k; rw [k.2]; exact h k.1 k.2
    · intro h j hj0; have := h ⟨j, hj0⟩; simpa [hj0] using this
  have hextr : IsLocalExtrOn g {ξ | ∀ k : {j : Fin nh // H η j = 0}, H ξ k.1 = H η k.1} η :=
    Or.inl (hset ▸ hmin)
  obtain ⟨Λ, Λ₀, hne, hsum⟩ := IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt
    (f := fun (k : {j : Fin nh // H η j = 0}) ξ => H ξ k.1) (f' := fun k => D k.1) hextr
    (fun k => ((hj k.1).contDiffAt).hasStrictFDerivAt (by norm_num))
    ((hg.contDiffAt).hasStrictFDerivAt (by norm_num))
  let ext : ({j : Fin nh // H η j = 0} → ℝ) → Fin nh → ℝ :=
    fun L j => if h : H η j = 0 then L ⟨j, h⟩ else 0
  have hext_sum : ∀ (L : {j : Fin nh // H η j = 0} → ℝ) (w : Fin nh → ℝ),
      ∑ j, ext L j * w j = ∑ k : {j : Fin nh // H η j = 0}, L k * w k.1 := by
    intro L w
    rw [← Fintype.sum_subtype_add_sum_subtype (fun j => H η j = 0)]
    have h2 : ∑ k : {j : Fin nh // ¬ H η j = 0}, ext L k.1 * w k.1 = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [ext, k.2]
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [ext, k.2]
  have hext_supp : ∀ L j, H η j ≠ 0 → ext L j = 0 := fun L j hj0 => by simp [ext, hj0]
  have h2 : ∀ v, ∑ k : {j : Fin nh // H η j = 0}, Λ k * D k.1 v + Λ₀ * fderiv ℝ g η v = 0 := by
    intro v
    have := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L v) hsum
    simpa [_root_.sum_apply] using this
  have hΛ₀ : Λ₀ ≠ 0 := by
    intro h0
    have hz : ext Λ = 0 := by
      apply hlicq (ext Λ) (hext_supp Λ)
      refine ContinuousLinearMap.ext fun v => ?_
      have q := h2 v
      rw [h0, zero_mul, add_zero] at q
      have q' : ∑ j, ext Λ j * (fderiv ℝ (fun ξ => H ξ j) η) v = 0 :=
        (hext_sum Λ (fun j => fderiv ℝ (fun ξ => H ξ j) η v)).trans (by simpa [hD] using q)
      simpa [_root_.sum_apply] using q'
    have hΛ : Λ = 0 := by
      funext k
      have := congrFun hz k.1
      simpa [ext, k.2] using this
    exact hne (by simp [hΛ, h0])
  refine ⟨ext (fun k => Λ k / Λ₀), hext_supp (fun k => Λ k / Λ₀), fun v => ?_⟩
  have e := hext_sum (fun k => Λ k / Λ₀) (fun j => D j v)
  simp only [hD] at e
  rw [e]
  have q := h2 v
  have e2 : ∑ k : {j : Fin nh // H η j = 0}, Λ k / Λ₀ * D k.1 v
      = (∑ k : {j : Fin nh // H η j = 0}, Λ k * D k.1 v) / Λ₀ := by
    rw [Finset.sum_div]; refine Finset.sum_congr rfl fun k _ => ?_; ring
  simp only [hD] at e2 q
  rw [e2, show ∑ k : {j : Fin nh // H η j = 0}, Λ k * fderiv ℝ (fun ξ => H ξ k.1) η v
      = -(Λ₀ * fderiv ℝ g η v) by linarith]
  field_simp
  ring

set_option maxSynthPendingDepth 3 in
set_option maxHeartbeats 1000000 in
/-- Existence, a priori bound and local uniqueness for one block. -/
lemma block_main {N n m nh : ℕ} (P : Problem N n m nh) (i : Fin N)
    (hf : ContDiff ℝ 2 (P.f i)) (hh : ContDiff ℝ 2 (P.h i))
    (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ) (hS : (Sig i)ᵀ = Sig i)
    (z : Fin n → ℝ) (lamS : Fin m → ℝ) (κi : Fin nh → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hfeas : ∀ j, P.h i z j ≤ 0)
    (hstat : ∀ d, fderiv ℝ (P.f i) z d + lamS ⬝ᵥ (P.A i *ᵥ d)
      + ∑ j, κi j * fderiv ℝ (fun ξ => P.h i ξ j) z d = 0)
    (hκ : ∀ j, 0 ≤ κi j) (hcomp : ∀ j, κi j * P.h i z j = 0)
    (hstrict : ∀ j, P.h i z j = 0 → 0 < κi j)
    (hlicq : ∀ ν : Fin nh → ℝ, (∀ j, P.h i z j ≠ 0 → ν j = 0) →
      (∀ d, ∑ j, ν j * fderiv ℝ (fun ξ => P.h i ξ j) z d = 0) → ν = 0)
    (hHess : ∀ d : Fin n → ℝ, d ≠ 0 →
      0 < hessQuad (P.lagBlock i κi) z d + ρ * (d ⬝ᵥ (Sig i *ᵥ d))) :
    ∃ K ≥ 0, ∃ β > 0, ∃ ru > 0, ∀ (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ),
      ‖x i - z‖ < β → ‖lam - lamS‖ < β →
      ∃ y, IsDecoupledLocalMin P ρ Sig x lam i y ∧ ‖y - z‖ ≤ K * (‖x i - z‖ + ‖lam - lamS‖) ∧
        ∀ η, IsDecoupledLocalMin P ρ Sig x lam i η → ‖η - z‖ < ru → η = y := by
  have hj : ∀ j, ContDiff ℝ 2 (fun ξ' => P.h i ξ' j) := fun j => contDiff_pi.mp hh j
  obtain ⟨r, hr, μ, hμ, δ, hδ, hkey⟩ := key_ineq P i hf hh Sig hS z κi ρ hHess
  obtain ⟨K, hK0, β1, hβ1, hex⟩ := exist_block P i hf hh Sig z lamS κi ρ hρ hfeas hstat hκ hcomp
    r μ hr hμ (hkey κi (fun j => by simp [hδ.le]))
  obtain ⟨c, hc, rl, hrl, hlic⟩ := licq_unif P i hh z hlicq
  have hin : ∃ rin > 0, ∀ ξ ∈ Metric.ball z rin, ∀ j, P.h i z j ≠ 0 → P.h i ξ j < 0 := by
    have hcj : ∀ j, ∃ r' > 0, ∀ ξ ∈ Metric.ball z r', P.h i z j ≠ 0 → P.h i ξ j < 0 := by
      intro j
      by_cases hz : P.h i z j = 0
      · exact ⟨1, one_pos, fun ξ _ h => absurd hz h⟩
      · have hneg : P.h i z j < 0 := lt_of_le_of_ne (hfeas j) hz
        have hopen : IsOpen {ξ | P.h i ξ j < 0} := isOpen_lt (hj j).continuous continuous_const
        obtain ⟨r', hr', hb⟩ := Metric.isOpen_iff.mp hopen z hneg
        exact ⟨r', hr', fun ξ hξ _ => hb hξ⟩
    choose rj hrj hrjb using hcj
    obtain ⟨rin, hrin, hle⟩ := exists_pos_le_all rj hrj
    exact ⟨rin, hrin, fun ξ hξ j hz => hrjb j ξ (Metric.ball_subset_ball (hle j) hξ) hz⟩
  obtain ⟨rin, hrin, hinb⟩ := hin
  obtain ⟨m0, hm0, hm0le⟩ := exists_pos_le_all (fun j => if P.h i z j = 0 then κi j else 1)
    (fun j => by
      by_cases hz : P.h i z j = 0
      · simp only [hz, if_true]; exact hstrict j hz
      · simp only [hz, if_false]; exact one_pos)
  set tol := min δ (m0 / 2) with htol
  have htol0 : 0 < tol := lt_min hδ (by positivity)
  set DL := fderiv ℝ (P.lagBlock i κi) with hDL
  have hDLc : Continuous DL := (contDiff_lagBlock P i hf hh κi).continuous_fderiv (by norm_num)
  obtain ⟨rD, hrD, hDb⟩ : ∃ rD > 0, ∀ ξ ∈ Metric.ball z rD, ‖DL ξ - DL z‖ < c * tol / 2 := by
    have hopen : IsOpen {y | ‖DL y - DL z‖ < c * tol / 2} :=
      isOpen_lt ((hDLc.sub continuous_const).norm) continuous_const
    have hz : z ∈ {y | ‖DL y - DL z‖ < c * tol / 2} := by
      simp only [Set.mem_setOf_eq, sub_self, norm_zero]; positivity
    obtain ⟨r', hr', hb⟩ := Metric.isOpen_iff.mp hopen z hz
    exact ⟨r', hr', fun ξ hξ => hb hξ⟩
  obtain ⟨CA, hCA0, hCA⟩ := dot_mulVec_bound (P.A i)
  obtain ⟨CS, hCS0, hCSb⟩ := dot_mulVec_bound (Sig i)
  set s := c * tol / (2 * (CA + 2 * ρ * CS + 1)) with hs
  have hs0 : 0 < s := by positivity
  have hsb : (CA + 2 * ρ * CS) * s ≤ c * tol / 2 := by
    have e : (CA + 2 * ρ * CS) * s = c * tol / 2 * ((CA + 2 * ρ * CS) / (CA + 2 * ρ * CS + 1)) := by
      rw [hs]; field_simp
    rw [e]
    have : (CA + 2 * ρ * CS) / (CA + 2 * ρ * CS + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hct : 0 ≤ c * tol / 2 := by positivity
    nlinarith
  refine ⟨K, hK0, min β1 s, lt_min hβ1 hs0, min (min (r / 2) rl) (min rin (min rD s)),
    lt_min (lt_min (by positivity) hrl) (lt_min hrin (lt_min hrD hs0)), ?_⟩
  intro x lam hx hlam
  obtain ⟨y, hyloc, hyK, hyr, hymin⟩ :=
    hex x lam (lt_of_lt_of_le hx (min_le_left _ _)) (lt_of_lt_of_le hlam (min_le_left _ _))
  refine ⟨y, hyloc, hyK, fun η hη hηr => ?_⟩
  have hηr2 : ‖η - z‖ < r / 2 := lt_of_lt_of_le hηr ((min_le_left _ _).trans (min_le_left _ _))
  have hηl : ‖η - z‖ < rl := lt_of_lt_of_le hηr ((min_le_left _ _).trans (min_le_right _ _))
  have hηin : ‖η - z‖ < rin := lt_of_lt_of_le hηr ((min_le_right _ _).trans (min_le_left _ _))
  have hηD : ‖η - z‖ < rD := lt_of_lt_of_le hηr
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hηs : ‖η - z‖ < s := lt_of_lt_of_le hηr
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hxs : ‖x i - z‖ < s := lt_of_lt_of_le hx (min_le_right _ _)
  have hls : ‖lam - lamS‖ < s := lt_of_lt_of_le hlam (min_le_right _ _)
  have mem : ∀ t, ‖η - z‖ < t → η ∈ Metric.ball z t := fun t h => by
    rw [Metric.mem_ball, dist_eq_norm]; exact h
  -- (a) local minimality on the active set at η
  have hloc : IsLocalMinOn (decoupledObjective P ρ Sig x lam i)
      {ξ | ∀ j, P.h i η j = 0 → P.h i ξ j = 0} η := by
    have hev : ∀ᶠ ξ in nhds η, ∀ j, P.h i η j ≠ 0 → P.h i ξ j < 0 := by
      rw [Filter.eventually_all]
      intro j
      by_cases hz : P.h i η j = 0
      · exact Filter.Eventually.of_forall fun ξ h => absurd hz h
      · have hneg : P.h i η j < 0 := lt_of_le_of_ne (hη.1 j) hz
        have hm : {ξ | P.h i ξ j < 0} ∈ nhds η :=
          (isOpen_lt (hj j).continuous continuous_const).mem_nhds hneg
        filter_upwards [hm] with ξ hξ _ using hξ
    have h2 : ∀ᶠ ξ in nhds η, ξ ∈ decoupledFeasibleSet P i →
        decoupledObjective P ρ Sig x lam i η ≤ decoupledObjective P ρ Sig x lam i ξ :=
      eventually_nhdsWithin_iff.mp hη.2
    refine eventually_nhdsWithin_iff.mpr ?_
    filter_upwards [h2, hev] with ξ h1 h3 hT
    apply h1
    intro j
    by_cases hz : P.h i η j = 0
    · exact (hT j hz).le
    · exact (h3 j hz).le
  -- (b) multipliers at η
  have hlicη : ∀ ν : Fin nh → ℝ, (∀ j, P.h i η j ≠ 0 → ν j = 0) →
      ∑ j, ν j • fderiv ℝ (fun ξ => P.h i ξ j) η = 0 → ν = 0 := by
    intro ν hν h0
    have hνz : ∀ j, P.h i z j ≠ 0 → ν j = 0 := fun j hz =>
      hν j (hinb η (mem _ hηin) j hz).ne
    have := hlic η (mem _ hηl) ν hνz
    rw [h0, norm_zero] at this
    have hn : ‖ν‖ ≤ 0 := by nlinarith [norm_nonneg ν]
    exact norm_le_zero_iff.mp hn
  obtain ⟨κt, hκts, hκteq⟩ := lagrange_ext (decoupledObjective P ρ Sig x lam i) (P.h i)
    (obj_contDiff P i hf ρ Sig x lam) hh η hloc hlicη
  -- (c) the multipliers are close to κi
  have hdsupp : ∀ j, P.h i z j ≠ 0 → (κt - κi) j = 0 := by
    intro j hz
    have h1 : κt j = 0 := hκts j (hinb η (mem _ hηin) j hz).ne
    have h2 : κi j = 0 := by
      rcases mul_eq_zero.mp (hcomp j) with h | h
      · exact h
      · exact absurd h hz
    simp [h1, h2]
  have hbnd := hlic η (mem _ hηl) (κt - κi) hdsupp
  have hop : ‖∑ j, (κt - κi) j • fderiv ℝ (fun ξ' => P.h i ξ' j) η‖ ≤ c * tol := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have q1 := hκteq v
    rw [fderiv_obj_apply P i hf ρ Sig hS x lam η v] at q1
    have q2 := hstat v
    have q3 := fderiv_lagBlock_apply P i hf hh κi η v
    have q4 := fderiv_lagBlock_apply P i hf hh κi z v
    have e1 : (∑ j, (κt - κi) j • fderiv ℝ (fun ξ' => P.h i ξ' j) η) v
        = -((DL η - DL z) v + (lam - lamS) ⬝ᵥ (P.A i *ᵥ v)
            + ρ * ((η - x i) ⬝ᵥ (Sig i *ᵥ v))) := by
      have e3 : (∑ j, (κt - κi) j • fderiv ℝ (fun ξ' => P.h i ξ' j) η) v
          = ∑ j, κt j * fderiv ℝ (fun ξ' => P.h i ξ' j) η v
            - ∑ j, κi j * fderiv ℝ (fun ξ' => P.h i ξ' j) η v := by
        rw [_root_.sum_apply, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [_root_.smul_apply, smul_eq_mul, Pi.sub_apply]
        ring
      rw [e3, _root_.sub_apply, hDL, q3, q4, sub_dotProduct]
      linarith
    rw [e1, norm_neg, Real.norm_eq_abs]
    have t1 : |(DL η - DL z) v| ≤ c * tol / 2 * ‖v‖ := by
      rw [← Real.norm_eq_abs]
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hDb η (mem _ hηD)).le (norm_nonneg _))
    have t2 := hCA (lam - lamS) v
    have t3 := hCSb (η - x i) v
    have hηx : ‖η - x i‖ ≤ 2 * s := by
      have := norm_sub_le_norm_sub_add_norm_sub η z (x i)
      rw [norm_sub_rev z] at this; linarith
    have hvn := norm_nonneg v
    have u2 : CA * ‖lam - lamS‖ * ‖v‖ ≤ CA * s * ‖v‖ := by gcongr
    have u3 : CS * ‖η - x i‖ * ‖v‖ ≤ CS * (2 * s) * ‖v‖ := by gcongr
    have u4 := mul_le_mul_of_nonneg_left u3 hρ.le
    have u5 := mul_le_mul_of_nonneg_right hsb hvn
    have habs : ∀ a b c' : ℝ, |a + b + ρ * c'| ≤ |a| + |b| + ρ * |c'| := by
      intro a b c'
      calc |a + b + ρ * c'| ≤ |a + b| + |ρ * c'| := abs_add_le _ _
        _ ≤ |a| + |b| + |ρ * c'| := by gcongr; exact abs_add_le _ _
        _ = |a| + |b| + ρ * |c'| := by rw [abs_mul, abs_of_pos hρ]
    have h5 := habs ((DL η - DL z) v) ((lam - lamS) ⬝ᵥ (P.A i *ᵥ v))
      ((η - x i) ⬝ᵥ (Sig i *ᵥ v))
    have t3' := mul_le_mul_of_nonneg_left t3 hρ.le
    nlinarith
  have hdn : ‖κt - κi‖ ≤ tol := le_of_mul_le_mul_left (hbnd.trans hop) hc
  have hdj : ∀ j, |κt j - κi j| ≤ tol := fun j => by
    have := (norm_le_pi_norm (κt - κi) j).trans hdn
    simpa [Real.norm_eq_abs] using this
  have hκt0 : ∀ j, 0 ≤ κt j := by
    intro j
    by_cases hz : P.h i z j = 0
    · have h1 := hm0le j
      simp only [hz, if_true] at h1
      have h2 := (abs_le.mp (hdj j)).1
      have h3 : tol ≤ m0 / 2 := min_le_right _ _
      linarith
    · rw [hκts j (hinb η (mem _ hηin) j hz).ne]
  -- (d) strong convexity of the multiplier-shifted objective
  have hηball : η ∈ Metric.ball z r := mem _ (by linarith)
  have hyball : y ∈ Metric.ball z r := by rw [Metric.mem_ball, dist_eq_norm]; linarith
  have hk := hkey κt (fun j => (hdj j).trans (min_le_left _ _)) x lam η hηball y hyball
  have hzero1 : ∑ j, κt j * P.h i η j = 0 := Finset.sum_eq_zero fun j _ => by
    by_cases hz : P.h i η j = 0
    · rw [hz, mul_zero]
    · rw [hκts j hz, zero_mul]
  have hlin0 := hκteq (y - η)
  rw [fderiv_obj_apply P i hf ρ Sig hS x lam η (y - η)] at hlin0
  have hneg : ∑ j, κt j * P.h i y j ≤ 0 := Finset.sum_nonpos fun j _ =>
    mul_nonpos_of_nonneg_of_nonpos (hκt0 j) (hyloc.1 j)
  have hyη : decoupledObjective P ρ Sig x lam i y ≤ decoupledObjective P ρ Sig x lam i η :=
    hymin η hη.1 (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hηr2.le))
  have hsq : μ * ‖y - η‖ ^ 2 ≤ 0 := by linarith
  have hsq0 : ‖y - η‖ ^ 2 = 0 :=
    le_antisymm (by nlinarith [sq_nonneg ‖y - η‖]) (sq_nonneg _)
  have := (pow_eq_zero_iff two_ne_zero).mp hsq0
  exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm

end ALADIN.LocalStab.Aux

open Matrix ALADIN.LocalStab in
theorem solution {N n m nh : ℕ} (P : Problem N n m nh)
    (hf : ∀ i, ContDiff ℝ 2 (P.f i)) (hh : ∀ i, ContDiff ℝ 2 (P.h i))
    (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ) (hSig : ∀ i, (Sig i).PosSemidef)
    (xs : Fin N → Fin n → ℝ) (lamS : Fin m → ℝ) (κ : Fin N → Fin nh → ℝ)
    (hmin : P.IsLocalMinimizer xs)
    (hreg : P.IsRegularKKTPoint xs lamS κ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ i (d : Fin n → ℝ), d ≠ 0 →
      0 < hessQuad (P.lagBlock i (κ i)) (xs i) d + ρ * (d ⬝ᵥ (Sig i *ᵥ d))) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Ioc 0 ε₀, ∃ χ χ₁ χ₂ : ℝ, 0 < χ ∧ 0 ≤ χ₁ ∧ 0 ≤ χ₂ ∧
      ∀ (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ), ‖x - xs‖ < ε → ‖lam - lamS‖ < ε →
        ∃ y : Fin N → Fin n → ℝ,
          (∀ i, IsDecoupledLocalMin P ρ Sig x lam i (y i)) ∧
          ‖y - xs‖ < χ * ε ∧
          (∀ i (η : Fin n → ℝ), IsDecoupledLocalMin P ρ Sig x lam i η →
            ‖η - xs i‖ < χ * ε → η = y i) ∧
          ‖y - xs‖ ≤ χ₁ * ‖x - xs‖ + χ₂ * ‖lam - lamS‖ := by
  obtain ⟨⟨hfeasS, hstatS, hκS, hcompS⟩, hLICQ, hstrS, -⟩ := hreg
  have hblk : ∀ i, ∃ K ≥ 0, ∃ β > 0, ∃ ru > 0, ∀ (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ),
      ‖x i - xs i‖ < β → ‖lam - lamS‖ < β →
      ∃ y, IsDecoupledLocalMin P ρ Sig x lam i y ∧
        ‖y - xs i‖ ≤ K * (‖x i - xs i‖ + ‖lam - lamS‖) ∧
        ∀ η, IsDecoupledLocalMin P ρ Sig x lam i η → ‖η - xs i‖ < ru → η = y := by
    intro i
    have hS : (Sig i)ᵀ = Sig i := by
      have h : (Sig i)ᴴ = Sig i := (hSig i).isHermitian
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
    refine Aux.block_main P i (hf i) (hh i) Sig hS (xs i) lamS (κ i) ρ hρ (hfeasS.2 i) (hstatS i)
      (hκS i) (hcompS i) (hstrS i) ?_ (hHess i)
    intro ν hν hzero
    have hL := hLICQ 0 (Pi.single i ν) ?_ ?_
    · have h2 := congrFun hL.2 i
      simpa using h2
    · intro i' j hj
      by_cases hi : i' = i
      · subst hi; simp [hν j hj]
      · simp [Pi.single_eq_of_ne hi]
    · intro d
      simp only [zero_dotProduct, zero_add]
      rw [Finset.sum_eq_single i]
      · simp only [Pi.single_eq_same]; exact hzero (d i)
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · intro h; exact absurd (Finset.mem_univ i) h
  choose K hK0 β hβ ru hru hP using hblk
  obtain ⟨Kmax, hKmax0, hKle⟩ : ∃ Kmax ≥ (0:ℝ), ∀ i, K i ≤ Kmax :=
    ⟨∑ i, K i, Finset.sum_nonneg (fun i _ => hK0 i),
      fun i => Finset.single_le_sum (fun i _ => hK0 i) (Finset.mem_univ i)⟩
  obtain ⟨βm, hβm, hβle⟩ := Aux.exists_pos_le_all β hβ
  obtain ⟨rum, hrum, hrule⟩ := Aux.exists_pos_le_all ru hru
  have hχ : (0:ℝ) < 2 * Kmax + 1 := by positivity
  refine ⟨min βm (rum / (2 * Kmax + 1)), lt_min hβm (by positivity), fun ε hε =>
    ⟨2 * Kmax + 1, Kmax, Kmax, hχ, hKmax0, hKmax0, ?_⟩⟩
  intro x lam hx hlam
  have hε0 := hε.1
  have hεβ : ε ≤ βm := hε.2.trans (min_le_left _ _)
  have hεr : (2 * Kmax + 1) * ε ≤ rum := by
    have := hε.2.trans (min_le_right _ _)
    rw [le_div_iff₀ hχ] at this; linarith
  have hxi : ∀ i, ‖x i - xs i‖ ≤ ‖x - xs‖ := fun i => by
    have := norm_le_pi_norm (x - xs) i; rwa [Pi.sub_apply] at this
  have hxb : ∀ i, ‖x i - xs i‖ < β i := fun i =>
    lt_of_le_of_lt (hxi i) (hx.trans_le (hεβ.trans (hβle i)))
  have hlb : ∀ i, ‖lam - lamS‖ < β i := fun i => hlam.trans_le (hεβ.trans (hβle i))
  choose y hyloc hyK hyuniq using fun i => hP i x lam (hxb i) (hlb i)
  have hyb : ∀ i, ‖y i - xs i‖ ≤ Kmax * (‖x - xs‖ + ‖lam - lamS‖) := fun i =>
    (hyK i).trans (mul_le_mul (hKle i) (by linarith [hxi i]) (by positivity) hKmax0)
  refine ⟨y, hyloc, ?_, fun i η hη hηr => hyuniq i η hη (lt_of_lt_of_le hηr (hεr.trans (hrule i))), ?_⟩
  · rw [pi_norm_lt_iff (by positivity)]
    intro i
    rw [Pi.sub_apply]
    have h1 : Kmax * (‖x - xs‖ + ‖lam - lamS‖) ≤ Kmax * (2 * ε) := by
      apply mul_le_mul_of_nonneg_left _ hKmax0; linarith
    nlinarith [hyb i]
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [Pi.sub_apply]
    linarith [hyb i]
