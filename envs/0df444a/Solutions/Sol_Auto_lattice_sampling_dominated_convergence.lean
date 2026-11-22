-- Prove2me | solution 1 for Auto.lattice_sampling_dominated_convergence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:05:06.908152+00:00
-- url     : https://prove2.me/submissions/b5193926-184e-40b1-b957-e12e949d8638

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_mem_latticeCube
public import Theorems.Thm_Auto_volume_latticeCube
public import Theorems.Thm_Auto_abs_sub_latticeFloor_le
public import Theorems.Thm_Auto_tendsto_latticeFloor
public import Theorems.Thm_Auto_volume_coord_hyperplane

set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal symmDiff
noncomputable section
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
namespace Auto
theorem _root_.solution (H : (Fin d → ℝ) → E) (hHb : ∃ M, ∀ x, ‖H x‖ ≤ M)
    (hHs : ∃ R, ∀ x, R < ‖x‖ → H x = 0) (S : Finset (Fin d × ℝ))
    (hHc : ∀ x, (∀ p ∈ S, x p.1 ≠ p.2) → ContinuousAt H x) :
    Tendsto (fun N : ℕ => ((N : ℝ)⁻¹) ^ d • ∑' k : Fin d → ℤ, H (fun i => (k i : ℝ) / N)) atTop
      (𝓝 (∫ x, H x)) := by
  classical
  obtain ⟨M, hM⟩ := hHb
  obtain ⟨R0, hR0⟩ := hHs
  set R := max R0 0
  have hR : ∀ x, R < ‖x‖ → H x = 0 := fun x hx => hR0 x (lt_of_le_of_lt (le_max_left _ _) hx)
  set O : Set (Fin d → ℝ) := {x | ∀ p ∈ S, x p.1 ≠ p.2}
  have hO : ∀ᵐ x, x ∈ O := by
    have : (Oᶜ) ⊆ ⋃ p ∈ S, {x : Fin d → ℝ | x p.1 = p.2} := by
      intro x hx
      simp only [O, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not] at hx
      obtain ⟨p, hp, hxp⟩ := hx
      exact Set.mem_biUnion hp hxp
    rw [ae_iff]
    refine measure_mono_null (fun x hx => this hx) ?_
    exact (measure_biUnion_null_iff (Finset.countable_toSet S)).2
      fun p _ => volume_coord_hyperplane p.1 p.2
  set F : ℕ → Finset (Fin d → ℤ) := fun N =>
    Fintype.piFinset fun _ => Finset.Icc (-(⌈R * N⌉ + 1)) (⌈R * N⌉ + 1)
  have hF : ∀ N : ℕ, 0 < N → ∀ k : Fin d → ℤ, k ∉ F N → H (fun i => (k i : ℝ) / N) = 0 := by
    intro N hN k hk
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [F, Fintype.mem_piFinset, Finset.mem_Icc, not_forall] at hk
    obtain ⟨i, hi⟩ := hk
    apply hR
    have hki : R * N < |(k i : ℝ)| := by
      have h1 := Int.le_ceil (R * N)
      rcases not_and_or.1 hi with h | h
      · push Not at h
        have : (k i : ℝ) < -(⌈R * N⌉ + 1) := by exact_mod_cast h
        rw [abs_of_neg (by linarith [mul_nonneg (le_max_right R0 0) hN'.le])]
        linarith
      · push Not at h
        have : (⌈R * N⌉ + 1 : ℝ) < (k i : ℝ) := by exact_mod_cast h
        rw [abs_of_pos (by linarith [mul_nonneg (le_max_right R0 0) hN'.le])]
        linarith
    calc R < |(k i : ℝ) / N| := by
          rw [abs_div, Nat.abs_cast, lt_div_iff₀ hN']; exact hki
      _ = ‖(fun i => (k i : ℝ) / N) i‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖fun i => (k i : ℝ) / N‖ := norm_le_pi_norm (fun i => (k i : ℝ) / N) i
  have hrep : ∀ N : ℕ, 0 < N → ∀ x, H (latticeFloor N x) =
      ∑ k ∈ F N, (latticeCube N k).indicator (fun _ => H (fun i => (k i : ℝ) / N)) x := by
    intro N hN x
    set k0 : Fin d → ℤ := fun i => ⌊(N : ℝ) * x i⌋
    have hmem : ∀ k, x ∈ latticeCube N k ↔ k = k0 := by
      intro k
      rw [mem_latticeCube hN]
      constructor
      · intro h; funext i; exact (h i).symm
      · rintro rfl i; rfl
    have hk0 : latticeFloor N x = fun i => (k0 i : ℝ) / N := rfl
    by_cases hk : k0 ∈ F N
    · rw [Finset.sum_eq_single k0]
      · rw [Set.indicator_of_mem ((hmem k0).2 rfl), hk0]
      · intro k _ hkk
        exact Set.indicator_of_notMem (fun h => hkk ((hmem k).1 h)) _
      · intro h; exact absurd hk h
    · rw [hk0, hF N hN k0 hk]
      refine (Finset.sum_eq_zero fun k hkF => ?_).symm
      exact Set.indicator_of_notMem (fun h => hk ((hmem k).1 h ▸ hkF)) _
  have hcube_meas : ∀ N k, MeasurableSet (latticeCube (d := d) N k) := fun N k =>
    MeasurableSet.univ_pi fun _ => measurableSet_Ico
  have hsum : ∀ N : ℕ, 0 < N → ((N : ℝ)⁻¹) ^ d • ∑' k : Fin d → ℤ, H (fun i => (k i : ℝ) / N) =
      ∫ x, H (latticeFloor N x) := by
    intro N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [tsum_eq_sum (s := F N) (fun k hk => hF N hN k hk)]
    simp_rw [hrep N hN]
    rw [integral_finsetSum]
    · rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_indicator_const _ (hcube_meas N k), measureReal_def, volume_latticeCube hN,
        ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
    · intro k _
      refine IntegrableOn.integrable_indicator (integrableOn_const ?_) (hcube_meas N k)
      rw [volume_latticeCube hN]; exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hlim : Tendsto (fun N : ℕ => ∫ x, H (latticeFloor N x)) atTop (𝓝 (∫ x, H x)) := by
    refine tendsto_integral_filter_of_dominated_convergence ((Metric.closedBall (0 : Fin d → ℝ) (R +
        1)).indicator fun _ => M) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with N hN
      rw [show (fun x => H (latticeFloor N x)) = fun x => ∑ k ∈ F N, (latticeCube N k).indicator
          (fun _ => H (fun i => (k i : ℝ) / N)) x from
        funext (hrep N hN)]
      exact Finset.aestronglyMeasurable_fun_sum _ fun k _ =>
        aestronglyMeasurable_const.indicator (hcube_meas N k)
    · filter_upwards [eventually_gt_atTop 0] with N hN
      refine Filter.Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ Metric.closedBall (0 : Fin d → ℝ) (R + 1)
      · rw [Set.indicator_of_mem hx]; exact hM _
      · rw [Set.indicator_of_notMem hx, hR, norm_zero]
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
        have hd : ‖x - latticeFloor N x‖ ≤ 1 := by
          refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
          rw [Pi.sub_apply, Real.norm_eq_abs]
          refine (abs_sub_latticeFloor_le hN x i).trans ?_
          exact inv_le_one_of_one_le₀ (by exact_mod_cast hN)
        have := norm_sub_norm_le x (latticeFloor N x)
        linarith
    · exact IntegrableOn.integrable_indicator (integrableOn_const measure_closedBall_lt_top.ne)
        Metric.isClosed_closedBall.measurableSet
    · filter_upwards [hO] with x hx
      exact (hHc x hx).tendsto.comp (tendsto_latticeFloor x)
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (hsum N hN).symm
end Auto
