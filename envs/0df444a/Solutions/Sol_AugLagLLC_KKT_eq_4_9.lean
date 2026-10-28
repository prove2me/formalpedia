-- Prove2me | solution 1 for AugLagLLC.KKT.eq_4_9
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:52:05.133723+00:00
-- url     : https://prove2.me/submissions/dfcc7d5c-1788-464b-b4c1-37f3a3d7778f

import Mathlib
import Definitions.Def_AugLagLLC_KKT_Setting

open Filter Topology

namespace Aux_AugLagLLC_KKT_eq_4_9
open AugLagLLC.KKT Asymptotics

theorem hd_maxsq (t : ℝ) : HasDerivAt (fun t : ℝ => (max t 0) ^ 2) (2 * max t 0) t := by
  rcases lt_trichotomy t 0 with h | h | h
  · have hev : (fun t : ℝ => (max t 0) ^ 2) =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with y hy
      rw [max_eq_right (le_of_lt hy)]; ring
    rw [max_eq_right h.le, mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq hev
  · subst h
    rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have hO : (fun h : ℝ => (max h 0) ^ 2) =O[𝓝 0] (fun h : ℝ => h ^ 2) := by
      refine IsBigO.of_bound 1 (Eventually.of_forall fun h => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (sq_nonneg _), one_mul]
      rcases le_or_gt h 0 with hh | hh
      · rw [max_eq_right hh]; nlinarith
      · rw [max_eq_left hh.le]
    have := hO.trans_isLittleO (isLittleO_pow_id (𝕜 := ℝ) (n := 2) one_lt_two)
    refine this.congr_left fun h => ?_
    simp
  · have hev : (fun t : ℝ => (max t 0) ^ 2) =ᶠ[𝓝 t] fun t => t ^ 2 := by
      filter_upwards [Ioi_mem_nhds h] with y hy
      rw [max_eq_left hy.le]
    rw [max_eq_left h.le]
    exact ((hasDerivAt_pow 2 t).congr_deriv (by push_cast; ring)).congr_of_eventuallyEq hev

theorem hd_sq (c t : ℝ) : HasDerivAt (fun t : ℝ => (t + c) ^ 2) (2 * (t + c)) t := by
  have := ((hasDerivAt_id t).add_const c).pow 2
  exact this.congr_deriv (by simp)

end Aux_AugLagLLC_KKT_eq_4_9

open AugLagLLC.KKT Aux_AugLagLLC_KKT_eq_4_9 InnerProductSpace in
theorem solution {n m1 p1 m2 p2 : ℕ} (P : Problem n m1 p1 m2 p2) (hP : P.IsC1)
    {τ γ ρ1 : ℝ} {lamMin lamMax : Fin m1 → ℝ} {muMax : Fin p1 → ℝ} {ε : ℕ → ℝ}
    (hpar : Problem.IsParams τ γ ρ1 lamMin lamMax muMax ε)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {ρ : ℕ → ℝ} {lamBar : ℕ → Fin m1 → ℝ}
    {muBar : ℕ → Fin p1 → ℝ} {v : ℕ → Fin m2 → ℝ} {u : ℕ → Fin p2 → ℝ}
    (hrun : P.IsRun τ γ ρ1 lamMin lamMax muMax ε x ρ lamBar muBar v u)
    (k : ℕ) (hk : 1 ≤ k) :
    ‖gradient P.f (x k)
        + ∑ i, P.lamNext x ρ lamBar k i • gradient (P.h1 i) (x k)
        + ∑ i, P.muNext x ρ muBar k i • gradient (P.g1 i) (x k)
        + ∑ i, v k i • gradient (P.h2 i) (x k)
        + ∑ j, u k j • gradient (P.g2 j) (x k)‖ ≤ ε k ∧
      (∀ j, 0 ≤ u k j) ∧ (∀ i, 0 ≤ P.muNext x ρ muBar k i) := by
  -- positivity of ρ
  have hρpos : ∀ k, 1 ≤ k → 0 < ρ k := by
    intro k hk
    induction k with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0; rw [hrun.1]; exact hpar.2.2.2.1
      · have hpk := ih h0
        rw [(hrun.2.2.2 k h0).2.2.2]
        split_ifs
        · exact hpk
        · exact mul_pos (by linarith [hpar.2.2.1]) hpk
  have hρ := hρpos k hk
  obtain ⟨ε1, ε2, ε3, h1, h2, h3, h4, h5, h6, hnorm, hu, -, -⟩ := (hrun.2.2.2 k hk).1
  set z := x k with hz
  obtain ⟨hf, hh1, hg1, -, -⟩ := hP
  have hD : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 φ →
      HasFDerivAt φ (fderiv ℝ φ z) z := fun φ hφ =>
    (hφ.differentiable one_ne_zero z).hasFDerivAt
  -- derivative of the augmented Lagrangian
  set c1 : Fin m1 → ℝ := fun i => 2 * (P.h1 i z + lamBar k i / ρ k) with hc1
  set c2 : Fin p1 → ℝ := fun i => 2 * max (P.g1 i z + muBar k i / ρ k) 0 with hc2
  have hAL : HasFDerivAt (fun y => P.augLag y (lamBar k) (muBar k) (ρ k))
      (fderiv ℝ P.f z + (ρ k / 2) • ∑ i, c1 i • fderiv ℝ (P.h1 i) z
        + (ρ k / 2) • ∑ i, c2 i • fderiv ℝ (P.g1 i) z) z := by
    unfold Problem.augLag
    refine ((hD _ hf).add ?_).add ?_
    · refine HasFDerivAt.const_mul ?_ (ρ k / 2)
      refine HasFDerivAt.fun_sum fun i _ => ?_
      exact (hd_sq (lamBar k i / ρ k) (P.h1 i z)).comp_hasFDerivAt z (hD _ (hh1 i))
    · refine HasFDerivAt.const_mul ?_ (ρ k / 2)
      refine HasFDerivAt.fun_sum fun i _ => ?_
      have := (hd_maxsq (P.g1 i z + muBar k i / ρ k)).comp_hasFDerivAt z
        ((hD _ (hg1 i)).add_const (muBar k i / ρ k))
      exact this
  have hgrad : gradient (fun y => P.augLag y (lamBar k) (muBar k) (ρ k)) z =
      gradient P.f z + ∑ i, P.lamNext x ρ lamBar k i • gradient (P.h1 i) z
        + ∑ i, P.muNext x ρ muBar k i • gradient (P.g1 i) z := by
    apply HasGradientAt.gradient
    rw [hasGradientAt_iff_hasFDerivAt]
    refine hAL.congr_fderiv ?_
    rw [map_add, map_add, map_sum, map_sum]
    simp only [map_smulₛₗ, toDual_gradient, starRingEnd_apply, star_trivial, Finset.smul_sum,
      smul_smul]
    have e1 : ∑ i, (ρ k / 2 * c1 i) • fderiv ℝ (P.h1 i) z =
        ∑ i, P.lamNext x ρ lamBar k i • fderiv ℝ (P.h1 i) z := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      simp only [hc1, Problem.lamNext]
      field_simp
      ring
    have e2 : ∑ i, (ρ k / 2 * c2 i) • fderiv ℝ (P.g1 i) z =
        ∑ i, P.muNext x ρ muBar k i • fderiv ℝ (P.g1 i) z := by
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      simp only [hc2, Problem.muNext]
      rw [show ρ k / 2 * (2 * max (P.g1 i z + muBar k i / ρ k) 0) =
        max (ρ k * (P.g1 i z + muBar k i / ρ k)) (ρ k * 0) by
          rw [← mul_max_of_nonneg _ _ hρ.le]; ring]
      rw [mul_zero, max_comm]
      congr 1
      field_simp
      ring
    rw [e1, e2]
  refine ⟨?_, fun j => (hu j).1, fun i => le_max_left _ _⟩
  rw [hgrad] at hnorm
  linarith
