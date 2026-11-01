-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P62
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P62
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T07:05:16.470175+00:00
-- url     : https://prove2.me/theorems/1d403a80-0954-4ffb-b0b6-e182d8645a5f
-- title:
--   Definitions for Limits on classical communication from quantum entropy power inequalities
-- statement:
--   The objects the formalized statements of *Limits on classical communication from quantum entropy power inequalities* (arXiv:1205.3407) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `photonCapacityNats`: PDF p.8, Appendix A: unassisted operational capacity in nats/use. The accepted bits capacity uses arbitrary normalized mixed entangled block signals, collective POVMs, vanishing uniform-message average error at all large positive blocklengths, and ensemble-average total input photons at most n*N. The positive unit factor preserves infinity. No entropy formula defines capacity.
--   - `balancedThermalUpperNats`: PDF p.8, (A2): the balanced thermal upper bound in nats. Only the average output photon number is inside g.
--   - `conjecturedThermalUpperNats`: PDF p.9, (A14): the conjecture-conditional numerical thermal bound. The complete weighted sum is inside the logarithm.
--   - `GeneralQuantumEPI`: PDF pp.2,7,9, (17)/(A15): the universal general-transmissivity exponential EPI is a premise, never an unconditional theorem of this paper. Entropy is in nats, as required by (A10)–(A15), correcting the p.2 bit-unit mismatch. The full closed interval and arbitrary independent normalized n-mode inputs are quantified here, before any channel parameters in its applications.
--   - `oneModeBeamChannel`: PDF pp.3–4, Fig.2/Fig.3: retained-port channel for a fixed arbitrary normalized one-mode environment, fresh and independent on every use. The accepted n-mode beam splitter is reindexed at n=1; no Gaussianity or finite environment-energy/entropy assumption is added.
--   - `maximumOutputEntropyNats`: PDF pp.3–4, (7) and Fig.3: supremal one-use output entropy under the input photon budget. The extended supremum keeps infinity; it is the maximum value whenever attained and asserts no new attainment result.
--   - `classicalNoiseKernel`: PDF pp.3,9, Fig.2 and (A18)–(A21): Gaussian displacement noise with photon increment nu. The accepted complex displacement has density exp(-|z|^2/nu)/(pi*nu) for nu>0 and is the identity at nu=0. This fixes the operational photon normalization without copying the inconsistent quadrature-density scale in Fig.2. The bounded realization is used on trace class.
-- source:
--   Limits on classical communication from quantum entropy power inequalities, arXiv:1205.3407v2, https://arxiv.org/abs/1205.3407v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P17
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P28

/-!
König and Smith, arXiv:1205.3407v2, PDF pp.1–9.
Only pinned accepted library modules are imported, as authorized by the independent
paper workflow. States and channels act on the full countable Fock space.
Capacity is operational; entropy remains extended nonnegative. New definitions
are confined to this paper. Reused results and two deferrals are recorded in the
unit artifacts. Compilation and independent moderation are pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P62

open scoped ENNReal BigOperators
open QAlgorithms.Papers.Independent.Dependency50.P33 (State productCoeff)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)
open QAlgorithms.Papers.Independent.Claimed50.P19 (FockIndex)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g displacementNoiseChannel)
open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)
open QAlgorithms.Papers.Independent.Gap48.P26 (weightedPhotonExpectation)
open QAlgorithms.Papers.Independent.Bridge50.P28
  (classicalPhotonCapacityBits thermalNoiseChannelKernel coherentSignalRateBits)
open QAlgorithms.Papers.Independent.Next46.P17
  (beamSplitter bosonicEntropyPower diffusionChannel TotalFisherRegular totalFisher)

/-- PDF p.8, Appendix A: unassisted operational capacity in nats/use.
The accepted bits capacity uses arbitrary normalized mixed entangled block
signals, collective POVMs, vanishing uniform-message average error at all large
positive blocklengths, and ensemble-average total input photons at most n*N.
The positive unit factor preserves infinity. No entropy formula defines capacity. -/
def photonCapacityNats (T : Matrix ℕ ℕ ℂ → Matrix ℕ ℕ ℂ) (N : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.log 2) * classicalPhotonCapacityBits id T N

/-- PDF p.8, (A2): the balanced thermal upper bound in nats.
Only the average output photon number is inside g. -/
def balancedThermalUpperNats (NE N : ℝ) : ℝ :=
  g ((N + NE) / 2) - Real.log (1 + Real.exp (g NE)) + Real.log 2

/-- PDF p.9, (A14): the conjecture-conditional numerical thermal bound.
The complete weighted sum is inside the logarithm. -/
def conjecturedThermalUpperNats (lam NE N : ℝ) : ℝ :=
  g (lam * N + (1 - lam) * NE) -
    Real.log (lam + (1 - lam) * Real.exp (g NE))

/-- PDF pp.2,7,9, (17)/(A15): the universal general-transmissivity exponential
EPI is a premise, never an unconditional theorem of this paper. Entropy is in
nats, as required by (A10)–(A15), correcting the p.2 bit-unit mismatch.
The full closed interval and arbitrary independent normalized n-mode inputs
are quantified here, before any channel parameters in its applications. -/
def GeneralQuantumEPI : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (lam : ℝ), 0 ≤ lam → lam ≤ 1 →
    ∀ rhoX rhoY : State (FockIndex n),
      ENNReal.ofReal lam * bosonicEntropyPower n (extendedEntropyNats rhoX.coefficients) +
        ENNReal.ofReal (1 - lam) *
          bosonicEntropyPower n (extendedEntropyNats rhoY.coefficients) ≤
      bosonicEntropyPower n (extendedEntropyNats (beamSplitter lam
        (productCoeff rhoX.coefficients rhoY.coefficients)))

/-- PDF pp.3–4, Fig.2/Fig.3: retained-port channel for a fixed arbitrary
normalized one-mode environment, fresh and independent on every use.
The accepted n-mode beam splitter is reindexed at n=1; no Gaussianity or
finite environment-energy/entropy assumption is added. -/
def oneModeBeamChannel (lam : ℝ) (sigma : State ℕ)
    (X : Matrix ℕ ℕ ℂ) : Matrix ℕ ℕ ℂ :=
  fun a b => beamSplitter lam
    (productCoeff
      (fun p q : FockIndex 1 => X (p 0) (q 0))
      (fun p q : FockIndex 1 => sigma.coefficients (p 0) (q 0)))
    (fun _ => a) (fun _ => b)

/-- PDF pp.3–4, (7) and Fig.3: supremal one-use output entropy under the
input photon budget. The extended supremum keeps infinity; it is the maximum
value whenever attained and asserts no new attainment result. -/
def maximumOutputEntropyNats (T : Matrix ℕ ℕ ℂ → Matrix ℕ ℕ ℂ)
    (N : ℝ) : ℝ≥0∞ :=
  ⨆ rho : {rho : State ℕ //
    weightedPhotonExpectation id rho.coefficients ≤ ENNReal.ofReal N},
    extendedEntropyNats (T rho.val.coefficients)

/-- PDF pp.3,9, Fig.2 and (A18)–(A21): Gaussian displacement noise with
photon increment nu. The accepted complex displacement has density
exp(-|z|^2/nu)/(pi*nu) for nu>0 and is the identity at nu=0.
This fixes the operational photon normalization without copying the inconsistent
quadrature-density scale in Fig.2. The bounded realization is used on trace class. -/
def classicalNoiseKernel (nu : ℝ) (X : Matrix ℕ ℕ ℂ) : Matrix ℕ ℕ ℂ :=
  operatorCoeff (displacementNoiseChannel nu (boundedOperator X))

/-! Sanity checks pin unit conversion, zero-noise boundaries, the universal
premise's mode domain, input-budget restriction, and one-mode coordinate adapter.
These are definition checks, not proofs of any source result. -/

example (T : Matrix ℕ ℕ ℂ → Matrix ℕ ℕ ℂ) (N : ℝ) :
    photonCapacityNats T N =
      ENNReal.ofReal (Real.log 2) * classicalPhotonCapacityBits id T N := rfl

example (N : ℝ) : balancedThermalUpperNats 0 N = g (N / 2) := by
  simp [balancedThermalUpperNats, g]
  norm_num <;> ring

example (NE N : ℝ) : conjecturedThermalUpperNats 1 NE N = g N := by
  simp [conjecturedThermalUpperNats]

example (h : GeneralQuantumEPI) (rhoX rhoY : State (FockIndex 1)) :
    ENNReal.ofReal (1 / 2 : ℝ) *
        bosonicEntropyPower 1 (extendedEntropyNats rhoX.coefficients) +
      ENNReal.ofReal (1 - (1 / 2 : ℝ)) *
        bosonicEntropyPower 1 (extendedEntropyNats rhoY.coefficients) ≤
    bosonicEntropyPower 1 (extendedEntropyNats (beamSplitter (1 / 2 : ℝ)
      (productCoeff rhoX.coefficients rhoY.coefficients))) := by
  exact h 1 (by norm_num) (1 / 2) (by norm_num) (by norm_num) rhoX rhoY

example (lam : ℝ) (sigma : State ℕ) : oneModeBeamChannel lam sigma 0 = 0 := by
  funext a b
  simp [oneModeBeamChannel, beamSplitter, productCoeff]

example (T : Matrix ℕ ℕ ℂ → Matrix ℕ ℕ ℂ) (N : ℝ) (rho : State ℕ)
    (h : weightedPhotonExpectation id rho.coefficients ≤ ENNReal.ofReal N) :
    extendedEntropyNats (T rho.coefficients) ≤ maximumOutputEntropyNats T N := by
  exact le_iSup_of_le ⟨rho, h⟩ le_rfl

example (X : Matrix ℕ ℕ ℂ) :
    classicalNoiseKernel 0 X = operatorCoeff (boundedOperator X) := by
  simp [classicalNoiseKernel, displacementNoiseChannel]

end QAlgorithms.Papers.Independent.Intakenext100.P62


