-- Prove2me | solution 1 for AdSCFT.focusing_of_riccati
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-24T07:50:05.503734+00:00
-- url     : https://prove2.me/submissions/9b0ac52b-137f-4edc-b926-084e9a09b061

import Definitions.Def_AdSCFTFocusingProfiles

set_option autoImplicit false

open AdSCFT

-- AdSCFT.focusing_of_riccati: the Riccati equation (4.3), the trace
-- Cauchy–Schwarz bound |K|² ≥ H²/n (4.5) and the energy hypothesis S ≥ 0 (4.1)
-- imply the focusing inequality φ' ≥ r·φ²/n for φ(r) = -H(r)/r on (0, L).
--
-- Proof: differentiate the quotient,
--   φ'(r) = (-H'(r)·r + H(r))/r²,
-- then use the Riccati equation H' = -Ksq + H/r - S/r² to rewrite
--   -H'(r)·r + H(r) = Ksq(r)·r + S(r)/r,
-- so φ'(r) = Ksq(r)/r + S(r)/r³ ≥ (H(r)²/n)/r + 0 = r·φ(r)²/n,
-- using Cauchy–Schwarz and S ≥ 0 with r > 0.
theorem solution (n : ℕ) (hn : 0 < n) (L : ℝ) (D : RiccatiData n L)
    (phi phi' : ℝ → ℝ) (hphi : ∀ r, phi r = -D.H r / r)
    (hphi' : ∀ r ∈ Set.Ioo (0 : ℝ) L, HasDerivAt phi (phi' r) r) :
    ∀ r ∈ Set.Ioo (0 : ℝ) L, r * (phi r) ^ 2 / n ≤ phi' r := by
  intro r hr
  have hr0 : (0 : ℝ) < r := hr.1
  have hne : (r : ℝ) ≠ 0 := ne_of_gt hr0
  have hn_ne : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  -- derivative of the quotient -H/r
  have hg : HasDerivAt (fun s => -D.H s) (-D.H' r) r := (D.hasDeriv r hr).neg
  have hid : HasDerivAt (fun s => s) (1 : ℝ) r := hasDerivAt_id' r
  have hdiv := hg.div hid hne
  -- phi agrees with the quotient, so it has the same derivative
  have heq : phi =ᶠ[nhds r] (fun s => -D.H s / s) := by
    filter_upwards with s
    show phi s = -D.H s / s
    rw [hphi s]
  have hphi_q := hdiv.congr_of_eventuallyEq heq
  have huniq := (hphi' r hr).unique hphi_q
  -- clear denominators in the Riccati equation
  have hric := D.riccati r hr
  have hric2 : (D.H' r + D.Ksq r) * r ^ 2 - D.H r * r + D.S r = 0 := by
    have h := hric
    field_simp at h
    linear_combination h
  -- closed form of the derivative via the Riccati equation
  have hform : (-D.H' r * r - -D.H r * 1) / r ^ 2
      = D.Ksq r / r + D.S r / r ^ 3 := by
    field_simp
    linear_combination -hric2
  -- left-hand side in the same normal form
  have hLHS : r * (-D.H r / r) ^ 2 / (n : ℝ) = (D.H r) ^ 2 / n / r := by
    field_simp
  rw [huniq, hphi r, hform, hLHS]
  have hcs := D.cauchySchwarz r hr
  have hen := D.energy r hr
  have h1 : (D.H r) ^ 2 / (n : ℝ) / r ≤ D.Ksq r / r :=
    (div_le_div_iff_of_pos_right hr0).mpr hcs
  have h2 : (0 : ℝ) ≤ D.S r / r ^ 3 := div_nonneg hen (pow_nonneg hr0.le 3)
  linarith
