-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P11
-- name    : QAlgorithms_Papers_Independent_Claimed50_P11
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T09:22:31.281688+00:00
-- url     : https://prove2.me/theorems/6f7e071d-50e5-4282-88f9-f6bfe2a5bbd1
-- title:
--   Definitions for A generalization of the Entropy Power Inequality to Bosonic Quantum Systems
-- statement:
--   The objects the formalized statements of *A generalization of the Entropy Power Inequality to Bosonic Quantum Systems* (arXiv:1402.0404) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `thermalEntropyInverse`: PDF pp.9,23: inverse of the thermal entropy g on nonnegative occupations. For s > 0 the set is nonempty and bounded below: g is continuous, strictly increasing and unbounded on [0,infinity), with g(0)=0. Thus this infimum is the unique nonnegative solution of g(N)=s, rather than a divergent-sum default. The total extension at nonpositive s is zero; source uses have s >= 0.
--   - `entropyPowerPhoton`: PDF pp.9,23: f(x)=g^{-1}(ln x), used only for x >= 1.
--   - `entropyPowerDelta`: PDF p.23, Eq.(105): the correction to x/e-1/2, on x >= 1.
--   - `vacuumLossSummand`: PDF p.10, Eq.(37): Kraus summand for the fixed-vacuum pure-loss channel. The accepted attenuator coefficients use amplitude k=sqrt(lambda), so the intensity transmissivity is lambda. Only input indices i+ell,j+ell contribute. The discarded-port phase cancels between the Kraus coefficient and its adjoint. No finite occupation cutoff or input-dependent environment is used.
--   - `vacuumLossOutput`: PDF p.10, Eq.(37): actual full-Fock vacuum-loss output coefficients. For normalized trace-class inputs and lambda in [0,1], the theorem below concludes summability and normalization; they are not hypotheses.
-- source:
--   A generalization of the Entropy Power Inequality to Bosonic Quantum Systems, arXiv:1402.0404v2, https://arxiv.org/abs/1402.0404v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P49
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

/-!
Statements from De Palma, Mari and Giovannetti, arXiv:1402.0404v2.
The thermal entropy in nats is reused from the pinned accepted library.
The single-mode vacuum-loss bound is stated on full Fock densities.
The remaining bosonic nodes, including the unrestricted qEPI, are deferred in HARD.md.
No scalar statement below stands in for a deferred bosonic theorem.
Compilation is pending the authorized batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P11

open Filter
open scoped Topology
open QAlgorithms.Papers.Independent.Information100.P49 (thermalEntropy)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)
open QAlgorithms.Papers.Independent.Dependency50.P39 (attenuatorMatrix)

/-- PDF pp.9,23: inverse of the thermal entropy g on nonnegative occupations.
For s > 0 the set is nonempty and bounded below: g is continuous, strictly
increasing and unbounded on [0,infinity), with g(0)=0. Thus this infimum is
the unique nonnegative solution of g(N)=s, rather than a divergent-sum default.
The total extension at nonpositive s is zero; source uses have s >= 0. -/
def thermalEntropyInverse (s : ℝ) : ℝ :=
  if s ≤ 0 then 0 else sInf {N : ℝ | 0 ≤ N ∧ s ≤ thermalEntropy N}

/-- PDF pp.9,23: f(x)=g^{-1}(ln x), used only for x >= 1. -/
def entropyPowerPhoton (x : ℝ) : ℝ :=
  thermalEntropyInverse (Real.log x)

/-- PDF p.23, Eq.(105): the correction to x/e-1/2, on x >= 1. -/
def entropyPowerDelta (x : ℝ) : ℝ :=
  entropyPowerPhoton x - x / Real.exp 1 + 1 / 2

example : thermalEntropyInverse 0 = 0 := by
  simp [thermalEntropyInverse]

example : entropyPowerPhoton 1 = 0 := by
  simp [entropyPowerPhoton, thermalEntropyInverse]

example : entropyPowerDelta 1 = 1 / 2 - 1 / Real.exp 1 := by
  simp [entropyPowerDelta, entropyPowerPhoton, thermalEntropyInverse]
  <;> ring

/-- PDF p.10, Eq.(37): Kraus summand for the fixed-vacuum pure-loss channel.
The accepted attenuator coefficients use amplitude k=sqrt(lambda), so the
intensity transmissivity is lambda. Only input indices i+ell,j+ell contribute.
The discarded-port phase cancels between the Kraus coefficient and its adjoint.
No finite occupation cutoff or input-dependent environment is used. -/
def vacuumLossSummand (lambda : ℝ) (rho : Matrix ℕ ℕ ℂ)
    (i j ell : ℕ) : ℂ :=
  attenuatorMatrix (Real.sqrt lambda) ell i (i + ell) *
    rho (i + ell) (j + ell) *
      star (attenuatorMatrix (Real.sqrt lambda) ell j (j + ell))

/-- PDF p.10, Eq.(37): actual full-Fock vacuum-loss output coefficients.
For normalized trace-class inputs and lambda in [0,1], the theorem below
concludes summability and normalization; they are not hypotheses. -/
def vacuumLossOutput (lambda : ℝ) (rho : Matrix ℕ ℕ ℂ) : Matrix ℕ ℕ ℂ :=
  fun i j => ∑' ell : ℕ, vacuumLossSummand lambda rho i j ell

example (rho : Matrix ℕ ℕ ℂ) : vacuumLossSummand 1 rho 0 0 0 = rho 0 0 := by
  simp [vacuumLossSummand, attenuatorMatrix]

example (lambda : ℝ) : vacuumLossOutput lambda 0 = 0 := by
  funext i j
  simp [vacuumLossOutput, vacuumLossSummand]

end QAlgorithms.Papers.Independent.Claimed50.P11


