-- Prove2me | solution 1 for Approximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:54:34.200785+00:00
-- url     : https://prove2.me/submissions/6986421d-3b11-4e00-a2c7-d2ce07db2d7b

import Definitions.Def_PHigherOrder_ApproxFiniteCase
import Definitions.Def_PHigherOrder_ApproxInfiniteCase
import Definitions.Def_PHigherOrder_IterationDichotomy
import Definitions.Def_PHigherOrder_IterationSequence
import Definitions.Def_PHigherOrder_IterationStep
import Definitions.Def_PHigherOrder_Approximation
import Theorems.Thm_ApproxFiniteCase
import Theorems.Thm_ApproxInfiniteCase
import Theorems.Thm_IterationDichotomy
import Theorems.Thm_IterationSequence
import Theorems.Thm_IterationStep


set_option autoImplicit false

theorem _root_.solution (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (hLR : LewisRigidityInput p) (F : FirstOrderEstimateInput p) (hIM : IMRegularityInput p)
    (hsm : SmoothAwayFromCriticalInput p) (hS : DivFormSchauderInput)
    (k : ℕ) (hk : 2 ≤ k) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hks : (k : ℝ) + β < SOpt p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (v : Plane → ℝ) (g : Plane → Plane), IsPHarm p (Metric.ball 0 1) v g →
        (∀ y ∈ Metric.ball (0 : Plane) 1, |v y| ≤ 1) → v 0 = 0 →
        (∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ w : Plane,
            |iteratedFDeriv ℝ j v 0 (fun _ => w)| ≤ C * ‖w‖ ^ j)
          ∧ (∀ y : Plane, ‖y‖ < 1 →
              |v y - TaylorPoly k v 0 y| ≤ C * ‖y‖ ^ ((k : ℝ) + β)) := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hσ1 : (1 : ℝ) < (k : ℝ) + β := by linarith
  -- STEP 0:  the constants, fixed before `v`.
  obtain ⟨δ, hδ, θ, hθ0, hθ4, hstep⟩ := IterationStep p hp hp2 hLR F hIM k hk β hβ0 hβ1 hks
  have hθ1 : θ ≤ 1 := by linarith
  obtain ⟨Cfin, hCfin, hAFC⟩ :=
    ApproxFiniteCase p hp hp2 F hsm hS hIM k hk β hβ0 hβ1 hks δ hδ θ hθ0 hθ1
  obtain ⟨C, hCdef⟩ : ∃ t : ℝ, t = max (θ ^ (-((k : ℝ) + β))) Cfin := ⟨_, rfl⟩
  have hθp : (0 : ℝ) < θ ^ (-((k : ℝ) + β)) := Real.rpow_pos_of_pos hθ0 _
  have hθC : θ ^ (-((k : ℝ) + β)) ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hfinC : Cfin ≤ C := by rw [hCdef]; exact le_max_right _ _
  have hC0 : 0 < C := lt_of_lt_of_le hθp hθC
  refine ⟨C, hC0, ?_⟩
  intro v g hph hbd hv0
  -- STEP 1:  the chain of radii, built once.
  obtain ⟨Good, hGoodDef⟩ : ∃ P : ℝ → Prop, P = fun R => 0 < R ∧ R ≤ 1 ∧
      ∀ y : Plane, ‖y‖ < R → |v y| ≤ R ^ ((k : ℝ) + β) := ⟨_, rfl⟩
  obtain ⟨Cont, hContDef⟩ : ∃ P : ℝ → Prop, P = fun R =>
      R ^ (1 - ((k : ℝ) + β)) * ‖gradient v 0‖ ≤ δ := ⟨_, rfl⟩
  have hGood1 : Good 1 := by
    rw [hGoodDef]
    refine ⟨one_pos, le_refl 1, ?_⟩
    intro y hy
    rw [Real.one_rpow]
    exact hbd y (by simpa [Metric.mem_ball, dist_zero_right] using hy)
  have hstepseq : ∀ r : ℝ, Good r → Cont r → ∃ r' : ℝ, Good r' ∧ θ * r ≤ r' ∧ r' ≤ r / 4 := by
    intro r hG hC
    rw [hGoodDef] at hG
    rw [hContDef] at hC
    obtain ⟨hr0, hr1, hnorm⟩ := hG
    obtain ⟨r', hr'0, hr'1, hr'norm, hleft, hright⟩ :=
      hstep v g hph hbd hv0 r hr0 hr1 hnorm hC
    exact ⟨r', by rw [hGoodDef]; exact ⟨hr'0, hr'1, hr'norm⟩, hleft, hright⟩
  obtain ⟨R, hR0, hRgood, hRsand⟩ := IterationSequence Good Cont θ hGood1 hstepseq
  have hRpos : ∀ l : ℕ, 0 < R l := by
    intro l
    have h := hRgood l
    rw [hGoodDef] at h
    exact h.1
  have hRle1 : ∀ l : ℕ, R l ≤ 1 := by
    intro l
    have h := hRgood l
    rw [hGoodDef] at h
    exact h.2.1
  have hRnorm : ∀ (l : ℕ) (y : Plane), ‖y‖ < R l → |v y| ≤ R l ^ ((k : ℝ) + β) := by
    intro l
    have h := hRgood l
    rw [hGoodDef] at h
    exact h.2.2
  have hsand : ∀ l : ℕ, R l ^ (1 - ((k : ℝ) + β)) * ‖gradient v 0‖ ≤ δ →
      (θ * R l ≤ R (l + 1) ∧ R (l + 1) ≤ R l / 4) := by
    intro l h
    exact hRsand l (by rw [hContDef]; exact h)
  obtain ⟨hD1, hD2, hD3⟩ :=
    IterationDichotomy ((k : ℝ) + β) δ θ hσ1 hδ hθ0 v R hR0 hRpos hRnorm hsand
  rcases eq_or_ne (gradient v 0) 0 with hcrit | hcrit
  · -- STEP 2:  the case `Dv(0) = 0`.
    have hcontall := hD1.mpr hcrit
    have hleftall : ∀ l : ℕ, θ * R l ≤ R (l + 1) := fun l => (hsand l (hcontall l)).1
    have hlim := (hD2 hcontall).1
    obtain ⟨hjets, hTP, hdecay⟩ :=
      ApproxInfiniteCase p hp hp2 hLR F hIM k hk β hβ0 hβ1 hks θ hθ0 v g hph hv0 hcrit
        R hR0 hRpos hRnorm hleftall hlim
    refine ⟨?_, ?_⟩
    · intro j hj1 hjk w
      rw [hjets j hj1 hjk w, abs_zero]
      positivity
    · intro y hy
      have hTPy : TaylorPoly k v 0 y = 0 := by rw [hTP]; rfl
      rw [hTPy, sub_zero]
      refine le_trans (hdecay y hy) ?_
      exact mul_le_mul_of_nonneg_right hθC (Real.rpow_nonneg (norm_nonneg y) _)
  · -- STEP 3:  the case `Dv(0) ≠ 0`.
    obtain ⟨L, hnotL, hcontlt⟩ := hD3 hcrit
    have hsandL : ∀ l < L, θ * R l ≤ R (l + 1) ∧ R (l + 1) ≤ R l / 4 :=
      fun l hl => hsand l (hcontlt l hl)
    have hbigL : δ < R L ^ (1 - ((k : ℝ) + β)) * ‖gradient v 0‖ := not_le.mp hnotL
    obtain ⟨hc1, hc2⟩ := hAFC v g hph hv0 R L hR0 hRpos hRle1 hRnorm hsandL hbigL
    refine ⟨?_, ?_⟩
    · intro j hj1 hjk w
      exact le_trans (hc1 j hj1 hjk w)
        (mul_le_mul_of_nonneg_right hfinC (by positivity))
    · intro y hy
      exact le_trans (hc2 y hy)
        (mul_le_mul_of_nonneg_right hfinC (Real.rpow_nonneg (norm_nonneg y) _))
