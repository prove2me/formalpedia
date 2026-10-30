-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P03
-- name    : QAlgorithms_Papers_Independent_Bridge50_P03
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T11:51:07.543853+00:00
-- url     : https://prove2.me/theorems/75b3ca46-b243-40cf-9342-a638c88479d9
-- title:
--   Definitions for Secret key capacity of the thermal-loss channel: Improving the lower bound
-- statement:
--   The objects the formalized statements of *Secret key capacity of the thermal-loss channel: Improving the lower bound* (arXiv:1609.02169) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `thermalVarianceEntropy`: PDF p.2, (3): single-mode thermal entropy in bits as a function of variance x >= 1 (vacuum variance one, hbar=2). At x=1 the zero-log term is zero.
--   - `signedDetectorRate`: PDF p.5, (23): signed asymptotic detector expression. Its physical domain is 0 <= eta < 1, omega >= 1, d in [0,1], gamma >= 1, all finite. The disconnected detector d=0 has rate zero directly. On that branch (23) also gives zero, without using the singular expansions (29),(34),(36). Negative values remain signed values and are not positive achievable yields.
--   - `reverseInformationCurve`: PDF pp.2,7, (2) and the no-trusted-noise specialization: the signed reverse-coherent-information comparison curve; this scalar is not capacity.
--   - `balancedVacuumCurve`: PDF p.8: balanced detector, vacuum trusted noise. The printed residual gamma in the square-root denominator is replaced by 1, matching (23). The channel transmissivity eta is distinct from the detector setting d=1/2.
--   - `detectorRateImage`: PDF pp.5,7, (22): the image of every admissible detector setting. All gamma are finite reals; the range includes d=0 and d=1.
--   - `optimizedDetectorRate`: PDF pp.5,7, (22): optimized scalar rate. The theorem below supplies IsGreatest, so the source's maximum includes attainment and is not merely a totalized, possibly empty or unbounded real supremum.
-- source:
--   Secret key capacity of the thermal-loss channel: Improving the lower bound, arXiv:1609.02169v1, https://arxiv.org/abs/1609.02169v1

import Mathlib

/-!
# Noise-assisted thermal-loss lower bound: scalar results

Ottaviani et al., arXiv:1609.02169v1, PDF pp.2,5--8.
The operational capacity bound and the actual finite-energy protocol rate limit
are explicitly deferred in the unit HARD.md and GAPS.json. The expressions here
are scalar signed rates, not definitions of capacities or quantum information.
The physical domain of all real-valued formulas is 0 <= eta < 1, omega >= 1.
The identity-channel endpoint eta=1 requires an extended operational interface
and is part of the deferral; no assertion evaluates its real logarithm.

Source correction (independent moderation required): PDF p.8 retains gamma in
its denominator even though the specialization sets gamma=1. The curve below
substitutes 1, as uniquely fixed by (23) and the displayed left-hand side.
Compilation is pending the separate batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P03

/-- PDF p.2, (3): single-mode thermal entropy in bits as a function of variance
x >= 1 (vacuum variance one, hbar=2). At x=1 the zero-log term is zero. -/
def thermalVarianceEntropy (x : ℝ) : ℝ :=
  ((x + 1) / 2) * Real.logb 2 ((x + 1) / 2) -
    ((x - 1) / 2) * Real.logb 2 ((x - 1) / 2)

/-- PDF p.5, (23): signed asymptotic detector expression. Its physical domain
is 0 <= eta < 1, omega >= 1, d in [0,1], gamma >= 1, all finite.
The disconnected detector d=0 has rate zero directly. On that branch (23)
also gives zero, without using the singular expansions (29),(34),(36).
Negative values remain signed values and are not positive achievable yields. -/
def signedDetectorRate (eta omega d gamma : ℝ) : ℝ :=
  if d = 0 then 0 else
    (1 / 2 : ℝ) * Real.logb 2
      ((d * omega + (1 - d) * (1 - eta) * gamma) /
        ((1 - eta) * (d * (1 - eta) * omega + (1 - d) * gamma))) +
    thermalVarianceEntropy
      (Real.sqrt ((omega * (d + (1 - eta) * (1 - d) * omega * gamma)) /
        (d * omega + (1 - eta) * (1 - d) * gamma))) -
    thermalVarianceEntropy omega

/-- PDF pp.2,7, (2) and the no-trusted-noise specialization: the signed
reverse-coherent-information comparison curve; this scalar is not capacity. -/
def reverseInformationCurve (eta omega : ℝ) : ℝ :=
  -Real.logb 2 (1 - eta) - thermalVarianceEntropy omega

/-- PDF p.8: balanced detector, vacuum trusted noise. The printed residual
gamma in the square-root denominator is replaced by 1, matching (23).
The channel transmissivity eta is distinct from the detector setting d=1/2. -/
def balancedVacuumCurve (eta omega : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.logb 2
    ((omega + 1 - eta) / ((1 - eta) * ((1 - eta) * omega + 1))) +
  thermalVarianceEntropy
    (Real.sqrt ((omega * (1 + (1 - eta) * omega)) / (omega + 1 - eta))) -
  thermalVarianceEntropy omega

/-- PDF pp.5,7, (22): the image of every admissible detector setting.
All gamma are finite reals; the range includes d=0 and d=1. -/
def detectorRateImage (eta omega : ℝ) : Set ℝ :=
  {r | ∃ d : ℝ, d ∈ Set.Icc 0 1 ∧
    ∃ gamma : ℝ, 1 ≤ gamma ∧ signedDetectorRate eta omega d gamma = r}

/-- PDF pp.5,7, (22): optimized scalar rate. The theorem below supplies
IsGreatest, so the source's maximum includes attainment and is not merely
a totalized, possibly empty or unbounded real supremum. -/
def optimizedDetectorRate (eta omega : ℝ) : ℝ :=
  sSup (detectorRateImage eta omega)

/-- Vacuum has zero entropy, including the 0 log 0 convention. -/
example : thermalVarianceEntropy 1 = 0 := by
  norm_num [thermalVarianceEntropy, Real.logb]

/-- A disconnected detector has zero signed rate for every finite parameter. -/
example (eta omega gamma : ℝ) : signedDetectorRate eta omega 0 gamma = 0 := by
  simp [signedDetectorRate]

/-- The signed no-noise comparator at a replacer need not be positive. -/
example (omega : ℝ) : reverseInformationCurve 0 omega = -thermalVarianceEntropy omega := by
  simp [reverseInformationCurve]

/-- At a vacuum replacer the balanced comparison curve is zero. -/
example : balancedVacuumCurve 0 1 = 0 := by
  norm_num [balancedVacuumCurve, thermalVarianceEntropy, Real.logb]

/-- The detector image is nonempty, including at zero channel transmissivity. -/
example (eta omega : ℝ) : 0 ∈ detectorRateImage eta omega := by
  refine ⟨0, ⟨le_rfl, zero_le_one⟩, 1, le_rfl, ?_⟩
  simp [signedDetectorRate]

end QAlgorithms.Papers.Independent.Bridge50.P03


