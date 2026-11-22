-- Prove2me | solution 1 for ApproxInfiniteCase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:35:10.805789+00:00
-- url     : https://prove2.me/submissions/27edfd37-d2d1-44d5-b5a6-ba04546cc14b

import Definitions.Def_PHigherOrder_IMRegularityInput
import Definitions.Def_PHigherOrder_PHarmRestrict
import Definitions.Def_PHigherOrder_PHarmWeakGradClassical
import Definitions.Def_PHigherOrder_Rigidity
import Definitions.Def_PHigherOrder_TaylorPoly
import Definitions.Def_PHigherOrder_ApproxInfiniteCase
import Theorems.Thm_PHarmRestrict
import Theorems.Thm_PHarmWeakGradClassical
import Theorems.Thm_Rigidity


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hLR : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p)
    (θ : ℝ) (hθ0 : 0 < θ)
    (v : Plane → ℝ) (g : Plane → Plane) (hph : IsPHarm p (Metric.ball 0 1) v g)
    (hv0 : v 0 = 0) (hcrit : gradient v 0 = 0)
    (R : ℕ → ℝ) (hR0 : R 0 = 1) (hRpos : ∀ l : ℕ, 0 < R l)
    (hGood : ∀ (l : ℕ) (y : Plane), ‖y‖ < R l → |v y| ≤ R l ^ ((k : ℝ) + β))
    (hleft : ∀ l : ℕ, θ * R l ≤ R (l + 1))
    (hlim : Filter.Tendsto R Filter.atTop (nhds 0)) :
    (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ w : Plane, iteratedFDeriv ℝ j v 0 (fun _ => w) = 0)
      ∧ TaylorPoly k v 0 = 0
      ∧ ∀ y : Plane, ‖y‖ < 1 → |v y| ≤ θ ^ (-((k : ℝ) + β)) * ‖y‖ ^ ((k : ℝ) + β) := by
  classical
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hσ : (0 : ℝ) < (k : ℝ) + β := by linarith
  -- STEP 1:  conclusion (1), the vanishing jets.
  have h0mem : (0 : Plane) ∈ Metric.ball (0 : Plane) 1 := Metric.mem_ball_self one_pos
  obtain ⟨r, hr, C', hC', hrsub, hvCk, -⟩ :=
    hIM.reg (Metric.ball 0 1) v g hph k β hβ0 hβ1 hks 0 h0mem
  have hphr : IsPHarm p (Metric.ball 0 r) v g :=
    (PHarmRestrict p hp hp2 (Metric.ball 0 1) v g hph).1 _ Metric.isOpen_ball hrsub
  have hvC1 : ContDiffOn ℝ 1 v (Metric.ball 0 r) :=
    hvCk.of_le (by exact_mod_cast (by omega : 1 ≤ k))
  have hphr' : IsPHarm p (Metric.ball 0 r) v (gradient v) :=
    (PHarmWeakGradClassical p hp (Metric.ball 0 r) v g hphr hvC1).1
  have hrig := Rigidity p hp hp2 hLR F (Metric.ball 0 r) v 0 (Metric.mem_ball_self hr) k hk
    hvCk hphr' hcrit
  have hjet : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ w : Plane,
      iteratedFDeriv ℝ j v 0 (fun _ => w) = 0 := by
    intro j hj1 hjk w
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have hj1' : j = 1 := by omega
      subst hj1'
      rw [iteratedFDeriv_one_apply]
      show fderiv ℝ v 0 w = 0
      rw [← toDual_gradient, hcrit]
      simp
    · exact hrig j hj2 hjk w
  -- STEP 2:  conclusion (2), the Taylor polynomial vanishes.
  have hTP : TaylorPoly k v 0 = 0 := by
    funext z
    show (∑ j ∈ Finset.range (k + 1),
        (1 / (Nat.factorial j : ℝ)) * iteratedFDeriv ℝ j v 0 (fun _ => z - 0)) = 0
    refine Finset.sum_eq_zero ?_
    intro j hj
    have hjk : j ≤ k := by
      have := Finset.mem_range.mp hj
      omega
    rcases Nat.eq_zero_or_pos j with hj0 | hj1
    · subst hj0
      rw [iteratedFDeriv_zero_apply, hv0, mul_zero]
    · rw [hjet j hj1 hjk (z - 0), mul_zero]
  -- STEP 3:  conclusion (3), the pointwise decay.
  refine ⟨hjet, hTP, ?_⟩
  intro y hy
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [hv0, abs_zero, norm_zero, Real.zero_rpow (ne_of_gt hσ), mul_zero]
  · obtain ⟨t, htdef⟩ : ∃ s : ℝ, s = ‖y‖ := ⟨_, rfl⟩
    have ht0 : 0 < t := by rw [htdef]; exact norm_pos_iff.mpr hy0
    -- bracket `t` between consecutive radii:  the chain tends to `0`, so the set of indices
    -- with `t < R l` is bounded, and nonempty because `R 0 = 1 > t`.
    have hev : ∀ᶠ l in Filter.atTop, R l < t := hlim.eventually_lt_const ht0
    obtain ⟨Nn, hNn⟩ := Filter.eventually_atTop.mp hev
    obtain ⟨ℓ, hℓdef⟩ : ∃ m : ℕ, m = Nat.findGreatest (fun l => t < R l) Nn := ⟨_, rfl⟩
    have hP0 : t < R 0 := by rw [hR0, htdef]; exact hy
    have hℓP : t < R ℓ := by
      rw [hℓdef]
      exact Nat.findGreatest_spec (P := fun l => t < R l) (Nat.zero_le Nn) hP0
    have hℓle : ℓ ≤ Nn := by rw [hℓdef]; exact Nat.findGreatest_le Nn
    have hnext : R (ℓ + 1) ≤ t := by
      by_cases hle : ℓ + 1 ≤ Nn
      · have hgr := Nat.findGreatest_is_greatest (k := ℓ + 1) (P := fun l => t < R l) (n := Nn)
          (by rw [← hℓdef]; omega) hle
        exact not_lt.mp hgr
      · exact le_of_lt (hNn (ℓ + 1) (by omega))
    -- the estimate
    have hgood : |v y| ≤ R ℓ ^ ((k : ℝ) + β) := hGood ℓ y (by rw [← htdef]; exact hℓP)
    have hRle : R ℓ ≤ θ⁻¹ * t := by
      have h2 : θ * R ℓ ≤ t := le_trans (hleft ℓ) hnext
      rw [inv_mul_eq_div]
      exact (le_div_iff₀' hθ0).mpr h2
    refine le_trans hgood (le_trans
      (Real.rpow_le_rpow (le_of_lt (hRpos ℓ)) hRle (le_of_lt hσ)) ?_)
    rw [Real.mul_rpow (le_of_lt (inv_pos.mpr hθ0)) (le_of_lt ht0),
      Real.inv_rpow (le_of_lt hθ0), ← Real.rpow_neg (le_of_lt hθ0), htdef]
