-- Prove2me | solution 1 for AdaptiveEM.Infinite.eq_45
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:41:55.750297+00:00
-- url     : https://prove2.me/submissions/9e3a327d-3ce3-4743-a5d6-13a815426ef3

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Scheme
import Definitions.Def_AdaptiveEM_Infinite_Assumptions

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

open EthierKurtz SabanisEuler.Shared

namespace Aux_AdaptiveEM_eq_45

theorem mulVec_norm_sq_le {m d : ℕ} (A : Diffusion m d) (w : SDEState d) :
    ‖AdaptiveEM.Finite.mulVec A w‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖w‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  simp only [AdaptiveEM.Finite.mulVec, PiLp.toLp_apply]
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

end Aux_AdaptiveEM_eq_45

open AdaptiveEM.Infinite in
theorem solution {m d : ℕ} {Ω : Type*}
    (f : SDEState m → SDEState m) (g : SDEState m → Diffusion m d) (h : SDEState m → ℝ)
    (x0 : SDEState m) (W : ℝ≥0 → Ω → SDEState d) (hmax α β : ℝ)
    (hA8 : Assumption8 f h hmax α β) (h18 : ∀ x : SDEState m, ‖g x‖ ^ 2 ≤ β)
    (n : ℕ) (ω : Ω) :
    Real.exp (2 * α * ((AdaptiveEM.Finite.grid f g h x0 W (n + 1) ω).1 : ℝ)) * ‖(AdaptiveEM.Finite.grid f g h x0 W (n + 1) ω).2‖ ^ 2
      ≤ Real.exp (2 * α * ((AdaptiveEM.Finite.grid f g h x0 W n ω).1 : ℝ)) * ‖(AdaptiveEM.Finite.grid f g h x0 W n ω).2‖ ^ 2
        + 2 * Real.exp (2 * α * (((AdaptiveEM.Finite.grid f g h x0 W n ω).1 : ℝ) + hmax)) * β
            * h (AdaptiveEM.Finite.grid f g h x0 W n ω).2
        + Real.exp (2 * α * (((AdaptiveEM.Finite.grid f g h x0 W n ω).1 : ℝ) + hmax)) * β
            * ‖W (AdaptiveEM.Finite.grid f g h x0 W (n + 1) ω).1 ω - W (AdaptiveEM.Finite.grid f g h x0 W n ω).1 ω‖ ^ 2
        + 2 * Real.exp (2 * α * ((AdaptiveEM.Finite.grid f g h x0 W (n + 1) ω).1 : ℝ))
            * inner ℝ ((AdaptiveEM.Finite.grid f g h x0 W n ω).2
                + h (AdaptiveEM.Finite.grid f g h x0 W n ω).2 • f (AdaptiveEM.Finite.grid f g h x0 W n ω).2)
              (AdaptiveEM.Finite.mulVec (g (AdaptiveEM.Finite.grid f g h x0 W n ω).2)
                (W (AdaptiveEM.Finite.grid f g h x0 W (n + 1) ω).1 ω - W (AdaptiveEM.Finite.grid f g h x0 W n ω).1 ω)) := by
  obtain ⟨hcont, hmax0, hhb, hα, hβ, hdiss⟩ := hA8
  have hg : AdaptiveEM.Finite.grid f g h x0 W (n + 1) ω =
      ((AdaptiveEM.Finite.grid f g h x0 W n ω).1 + (h (AdaptiveEM.Finite.grid f g h x0 W n ω).2).toNNReal,
        (AdaptiveEM.Finite.grid f g h x0 W n ω).2 + h (AdaptiveEM.Finite.grid f g h x0 W n ω).2 •
          f (AdaptiveEM.Finite.grid f g h x0 W n ω).2 +
          AdaptiveEM.Finite.mulVec (g (AdaptiveEM.Finite.grid f g h x0 W n ω).2)
            (W ((AdaptiveEM.Finite.grid f g h x0 W n ω).1 +
              (h (AdaptiveEM.Finite.grid f g h x0 W n ω).2).toNNReal) ω -
              W (AdaptiveEM.Finite.grid f g h x0 W n ω).1 ω)) := rfl
  rw [hg]
  generalize AdaptiveEM.Finite.grid f g h x0 W n ω = q
  obtain ⟨t, x⟩ := q
  dsimp only
  obtain ⟨hx0, hxmax⟩ := hhb x
  set ΔW := W (t + (h x).toNNReal) ω - W t ω with hΔW
  set G := AdaptiveEM.Finite.mulVec (g x) ΔW with hG
  set φ := x + h x • f x with hφ
  have hcoe : ((t + (h x).toNNReal : ℝ≥0) : ℝ) = (t : ℝ) + h x := by
    rw [NNReal.coe_add, Real.coe_toNNReal _ hx0.le]
  rw [hcoe]
  have hGb : ‖G‖ ^ 2 ≤ β * ‖ΔW‖ ^ 2 := by
    have := Aux_AdaptiveEM_eq_45.mulVec_norm_sq_le (g x) ΔW
    have h2 := h18 x
    nlinarith [sq_nonneg ‖ΔW‖]
  have hφb : ‖φ‖ ^ 2 ≤ (1 - 2 * α * h x) * ‖x‖ ^ 2 + 2 * h x * β := by
    have e : ‖φ‖ ^ 2 = ‖x‖ ^ 2 + 2 * h x * (inner ℝ x (f x) + 1 / 2 * h x * ‖f x‖ ^ 2) := by
      rw [hφ, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      ring
    rw [e]
    have := hdiss x
    nlinarith
  have hsplit : ‖φ + G‖ ^ 2 = ‖φ‖ ^ 2 + 2 * inner ℝ φ G + ‖G‖ ^ 2 := norm_add_sq_real φ G
  rw [hsplit]
  set E := Real.exp (2 * α * (t : ℝ)) with hE
  set E' := Real.exp (2 * α * ((t : ℝ) + h x)) with hE'
  set Em := Real.exp (2 * α * ((t : ℝ) + hmax)) with hEm
  have hE'E : E' = E * Real.exp (2 * α * h x) := by
    rw [hE', hE, ← Real.exp_add]; ring_nf
  have hkey : Real.exp (2 * α * h x) * (1 - 2 * α * h x) ≤ 1 := by
    have h1 := Real.add_one_le_exp (-(2 * α * h x))
    have h2 : Real.exp (2 * α * h x) * Real.exp (-(2 * α * h x)) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos (2 * α * h x)
    nlinarith
  have hE'Em : E' ≤ Em := by
    rw [hE', hEm]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hEpos : 0 < E := Real.exp_pos _
  have hE'pos : 0 < E' := Real.exp_pos _
  have hx2 : 0 ≤ ‖x‖ ^ 2 := sq_nonneg _
  have hW2 : 0 ≤ ‖ΔW‖ ^ 2 := sq_nonneg _
  have t1 : E' * ((1 - 2 * α * h x) * ‖x‖ ^ 2) ≤ E * ‖x‖ ^ 2 := by
    rw [hE'E]
    have : E * Real.exp (2 * α * h x) * ((1 - 2 * α * h x) * ‖x‖ ^ 2) =
        E * ‖x‖ ^ 2 * (Real.exp (2 * α * h x) * (1 - 2 * α * h x)) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hkey (mul_nonneg hEpos.le hx2)
    linarith
  have t2 : E' * (2 * h x * β) ≤ 2 * Em * β * h x := by
    have := mul_le_mul_of_nonneg_right hE'Em (by positivity : (0:ℝ) ≤ 2 * h x * β)
    linarith
  have t3 : E' * ‖G‖ ^ 2 ≤ Em * β * ‖ΔW‖ ^ 2 := by
    have a1 := mul_le_mul_of_nonneg_left hGb hE'pos.le
    have a2 := mul_le_mul_of_nonneg_right hE'Em (by positivity : (0:ℝ) ≤ β * ‖ΔW‖ ^ 2)
    nlinarith
  have t0 := mul_le_mul_of_nonneg_left hφb hE'pos.le
  nlinarith
