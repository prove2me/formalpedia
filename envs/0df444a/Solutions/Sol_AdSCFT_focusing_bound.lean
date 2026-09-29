-- Prove2me | solution 1 for AdSCFT.focusing_bound
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-24T08:01:21.866741+00:00
-- url     : https://prove2.me/submissions/e301cc04-2d39-4ef1-89d3-78960bfeb66a

import Definitions.Def_AdSCFTFocusingProfiles

set_option autoImplicit false

open Set
open AdSCFT

-- AdSCFT.focusing_bound: integration of the focusing inequality.
-- From FocusingProfileAH (phi' ≥ r·phi²/n on [0,L], phi differentiable) and
-- phi 0 > 0, conclude L² ≤ 2n/phi 0.
-- Comparison argument: psi r = 1/phi r + r²/(2n) satisfies
-- psi' r = -phi' r/phi r² + r/n ≤ 0, so psi is antitone; psi L ≤ psi 0 gives
-- 1/phi L + L²/(2n) ≤ 1/phi 0, and 1/phi L > 0 yields the bound.
theorem solution (n : ℕ) (hn : 0 < n) (L : ℝ) (hL : 0 ≤ L) (phi phi' : ℝ → ℝ)
    (hpos : 0 < phi 0) (hprofile : FocusingProfileAH n L phi phi') :
    L ^ 2 ≤ 2 * n / phi 0 := by
  obtain ⟨hder, hineq⟩ := hprofile
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hnR' : (n:ℝ) ≠ 0 := ne_of_gt hnR
  -- Step 0: phi' ≥ 0 on [0, L], since r·(phi r)²/n ≥ 0 there.
  have hnn : ∀ r ∈ Icc (0:ℝ) L, 0 ≤ phi' r := by
    intro r hr
    have h := hineq r hr
    have h1 : (0:ℝ) ≤ r * (phi r) ^ 2 / n := by
      apply div_nonneg _ (le_of_lt hnR)
      exact mul_nonneg hr.1 (sq_nonneg _)
    linarith
  -- Step 1: phi is monotone on [0, L], hence phi r ≥ phi 0 > 0.
  have hmono : MonotoneOn phi (Icc (0:ℝ) L) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 L)
    · intro r hr
      exact (hder r hr).continuousAt.continuousWithinAt
    · intro r hr
      exact (hder r (interior_subset hr)).hasDerivWithinAt
    · intro r hr
      exact hnn r (interior_subset hr)
  have hphi_pos : ∀ r ∈ Icc (0:ℝ) L, 0 < phi r := by
    intro r hr
    have h0 : (0:ℝ) ∈ Icc (0:ℝ) L := ⟨le_refl _, hL⟩
    have hle := hmono h0 hr hr.1
    linarith
  -- Step 2: derivative of psi r = 1/phi r + r²/(2n).
  have hψder : ∀ r ∈ Icc (0:ℝ) L, HasDerivAt (fun r => 1 / phi r + r ^ 2 / (2 * (n:ℝ)))
      ((fun r => -phi' r / (phi r) ^ 2 + r / (n:ℝ)) r) r := by
    intro r hr
    have hne : phi r ≠ 0 := ne_of_gt (hphi_pos r hr)
    have h1 : HasDerivAt (fun r => (phi r)⁻¹) (-phi' r / (phi r) ^ 2) r :=
      (hder r hr).inv hne
    have h1' : HasDerivAt (fun r => 1 / phi r) (-phi' r / (phi r) ^ 2) r := by
      simpa [one_div] using h1
    have h2 : HasDerivAt (fun r : ℝ => r ^ 2 / (2 * (n:ℝ))) (r / (n:ℝ)) r := by
      have h := (hasDerivAt_pow 2 r).div_const (2 * (n:ℝ))
      rw [show ((2:ℕ):ℝ) * r ^ ((2:ℕ) - 1) / (2 * (n:ℝ)) = r / (n:ℝ) from ?_] at h
      · exact h
      · rw [show ((2:ℕ) - 1) = 1 from rfl, pow_one]
        push_cast
        have hne2 : (2:ℝ) * (n:ℝ) ≠ 0 := mul_ne_zero (by norm_num) hnR'
        field_simp
    exact h1'.add h2
  -- Step 3: psi is antitone on [0, L] since psi' ≤ 0.
  have hψanti : AntitoneOn (fun r => 1 / phi r + r ^ 2 / (2 * (n:ℝ))) (Icc (0:ℝ) L) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 L)
    · intro r hr
      exact (hψder r hr).continuousAt.continuousWithinAt
    · intro r hr
      exact (hψder r (interior_subset hr)).hasDerivWithinAt
    · intro r hr
      show -phi' r / (phi r) ^ 2 + r / (n:ℝ) ≤ 0
      have hrI : r ∈ Icc (0:ℝ) L := interior_subset hr
      have hpr : (0:ℝ) < phi r := hphi_pos r hrI
      have hpr2 : (0:ℝ) < (phi r) ^ 2 := by positivity
      have hpr2ne : (phi r) ^ 2 ≠ 0 := ne_of_gt hpr2
      have hden : (n:ℝ) * (phi r) ^ 2 ≠ 0 := mul_ne_zero hnR' hpr2ne
      have h1 : r / (n:ℝ) ≤ phi' r / (phi r) ^ 2 := by
        have h2 : r * (phi r) ^ 2 ≤ phi' r * (n:ℝ) := by
          have h := hineq r hrI
          rwa [div_le_iff₀ hnR] at h
        have e : phi' r / (phi r) ^ 2 - r / (n:ℝ)
            = (phi' r * (n:ℝ) - r * (phi r) ^ 2) / ((n:ℝ) * (phi r) ^ 2) := by
          field_simp
        have hnn' : (0:ℝ) ≤ (phi' r * (n:ℝ) - r * (phi r) ^ 2) / ((n:ℝ) * (phi r) ^ 2) :=
          div_nonneg (by linarith) (by positivity)
        linarith
      -- Goal `-phi'/phi^2 + r/↑n ≤ 0` follows from h1 by hand: linarith
      -- chokes on the negated division atom, so rewrite explicitly.
      have hkey : -phi' r / (phi r) ^ 2 + r / (n:ℝ)
          = -(phi' r / (phi r) ^ 2 - r / (n:ℝ)) := by ring
      rw [hkey]
      exact neg_nonpos.mpr (sub_nonneg.mpr h1)
  -- Step 4: psi L ≤ psi 0 gives the bound.
  have hmem0 : (0:ℝ) ∈ Icc (0:ℝ) L := ⟨le_refl _, hL⟩
  have hmemL : L ∈ Icc (0:ℝ) L := ⟨hL, le_refl _⟩
  have hψ := hψanti hmem0 hmemL hL
  simp only [] at hψ
  rw [show (0:ℝ) ^ 2 / (2 * (n:ℝ)) = 0 by simp, add_zero] at hψ
  have hphiL : (0:ℝ) < phi L := hphi_pos L hmemL
  have h1L : (0:ℝ) < 1 / phi L := by positivity
  have hstep : L ^ 2 / (2 * (n:ℝ)) < 1 / phi 0 := by linarith
  have h2n : (0:ℝ) < 2 * (n:ℝ) := by positivity
  have hfin : L ^ 2 < 2 * (n:ℝ) / phi 0 := by
    have e : L ^ 2 / (2 * (n:ℝ)) * (2 * (n:ℝ)) < (1 / phi 0) * (2 * (n:ℝ)) :=
      mul_lt_mul_of_pos_right hstep h2n
    rw [div_mul_cancel₀ _ (ne_of_gt h2n)] at e
    have e2 : (1:ℝ) / phi 0 * (2 * (n:ℝ)) = 2 * (n:ℝ) / phi 0 := by ring
    rwa [e2] at e
  linarith
