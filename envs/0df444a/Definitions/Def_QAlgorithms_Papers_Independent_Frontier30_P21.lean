-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P21
-- name    : QAlgorithms_Papers_Independent_Frontier30_P21
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:19:49.351974+00:00
-- url     : https://prove2.me/theorems/e799db77-9598-4a2b-9f6d-aa53ea203a24
-- title:
--   Definitions for Classical capacity of the lossy bosonic channel: the exact solution
-- statement:
--   The objects the formalized statements of *Classical capacity of the lossy bosonic channel: the exact solution* (arXiv:quant-ph/0308012) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `bosonicEntropy`: Thermal entropy in bits, PDF p.1 after Eq.(4). Physical arguments are nonnegative; the total formula interprets zero times log zero as zero.
--   - `coherentDensity`: Rank-one coherent density coefficients on the full oscillator, PDF p.2.
--   - `IsPureFockDensity`: A normalized pure density kernel represents an actual rank-one trace-class operator on the complete oscillator Hilbert space, PDF pp.1-2.
--   - `vacuumLossTerm`: The lost-photon summand in the number-basis expansion of the vacuum beam-splitter channel, PDF p.1 Eq.(3). The index ell counts photons traced out. The two square-root binomial coefficients arise from the beam-splitter action on the ket and bra. Only eta in [0,1] is used in the theorem.
--   - `vacuumLossKernel`: Number-basis kernel of vacuum loss, obtained by tracing the vacuum beam-splitter environment, PDF p.1 Eq.(3). Every asserted use below includes HasSum, so the default value of a divergent complex tsum is never used.
--   - `WordFock`: Full Hilbert space for a finite word of L oscillator modes, PDF p.2. There is no photon-number cutoff; the basis is the set of occupation tuples.
--   - `numberWord`: Product number-state codeword, PDF p.2, lossless comparison.
--   - `coherentWordCoefficient`: Coefficients of the finite product coherent word, PDF p.2.
--   - `coherentWord`: The Hilbert realization of the product coherent word, PDF p.2. The theorem concludes its coefficients and unit norm. Thus the fallback can never stand in for a normalized source state in a stated result.
--   - `CoherentWordRealized`: Coefficients and normalization, made a conclusion rather than an assumption of the discrimination theorem, PDF p.2.
--   - `BinaryEffect`: A binary POVM {T,I-T} on the full word Hilbert space, PDF p.2 operational pairwise-confusion convention. T is the decision for the first word.
--   - `binaryAverageError`: Uniformity is not assumed: p and 1-p are the binary priors, PDF p.2. For normalized states and an effect T this is the executed average error.
--   - `binaryErrorValues`: All achievable binary average errors, PDF p.2. IsLeast of this set asserts both an attained minimum and its lower bound against every binary POVM.
--   - `gridFrequency`: Positive frequency grid, PDF p.3: k starts at one, not zero.
--   - `gridTransmission`: The far-field quadratic transmissivity D(omega), PDF pp.3-4. Dc is D(cutoff); physical parameters give transmissivity in (0,1].
--   - `allocationEnergy`: Normal-ordered ensemble mean photon energy, PDF p.1 Eq.(5).
--   - `receiverObjective`: The explicitly printed receiver objective, PDF p.2 Eq.(11). This scalar functional makes no identification of a homodyne modulation ensemble.
--   - `FeasibleAllocation`: Feasible photon allocations, PDF p.1 Eq.(5) and p.4 maximization.
--   - `OptimalAllocation`: Attained maximum of the numerical objective (11), PDF p.4. Neither a maximizer nor a KKT condition is an input hypothesis of the theorem.
--   - `receiverAllocation`: Printed allocation, PDF p.4: beta absorbs the common xi/log(2) factor. The theorem requires beta,hbar,omega and eta to be positive.
-- source:
--   Classical capacity of the lossy bosonic channel: the exact solution, arXiv:quant-ph/0308012v2, https://arxiv.org/abs/quant-ph/0308012v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

/-!
Statements from arXiv:quant-ph/0308012v2. The general multimode capacity,
continuum approximations, and operational single-mode capacity are deferred in
HARD.md. The kernel below describes vacuum loss in the complete number basis;
it is not a finite photon cutoff or a definition of capacity.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Frontier30.P21

open Filter
open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient)
open scoped Topology

attribute [local instance] Classical.propDecidable

/-- Thermal entropy in bits, PDF p.1 after Eq.(4). Physical arguments are
nonnegative; the total formula interprets zero times log zero as zero. -/
def bosonicEntropy (x : ℝ) : ℝ :=
  (x + 1) * Real.logb 2 (x + 1) - x * Real.logb 2 x

/-- Rank-one coherent density coefficients on the full oscillator, PDF p.2. -/
def coherentDensity (alpha : ℂ) (m n : ℕ) : ℂ :=
  coherentCoefficient alpha m * star (coherentCoefficient alpha n)

/-- A normalized pure density kernel represents an actual rank-one trace-class
operator on the complete oscillator Hilbert space, PDF pp.1-2. -/
def IsPureFockDensity (rho : ℕ → ℕ → ℂ) : Prop :=
  ∃ u : QAlgorithms.RealRegisters.Hilbert ℕ,
    ‖u‖ = 1 ∧ ∀ m n, rho m n = u m * star (u n)

/-- The lost-photon summand in the number-basis expansion of the vacuum
beam-splitter channel, PDF p.1 Eq.(3). The index ell counts photons traced out.
The two square-root binomial coefficients arise from the beam-splitter action
on the ket and bra. Only eta in [0,1] is used in the theorem. -/
def vacuumLossTerm (eta : ℝ) (rho : ℕ → ℕ → ℂ) (m n ell : ℕ) : ℂ :=
  ((Real.sqrt (Nat.choose (m + ell) ell : ℝ) *
    Real.sqrt (Nat.choose (n + ell) ell : ℝ) *
    Real.sqrt eta ^ m * Real.sqrt eta ^ n * (1 - eta) ^ ell : ℝ) : ℂ) *
      rho (m + ell) (n + ell)

/-- Number-basis kernel of vacuum loss, obtained by tracing the vacuum
beam-splitter environment, PDF p.1 Eq.(3). Every asserted use below includes
HasSum, so the default value of a divergent complex tsum is never used. -/
def vacuumLossKernel (eta : ℝ) (rho : ℕ → ℕ → ℂ) (m n : ℕ) : ℂ :=
  ∑' ell, vacuumLossTerm eta rho m n ell

/-- Full Hilbert space for a finite word of L oscillator modes, PDF p.2.
There is no photon-number cutoff; the basis is the set of occupation tuples. -/
abbrev WordFock (L : ℕ) := QAlgorithms.RealRegisters.Hilbert (Fin L → ℕ)

/-- Product number-state codeword, PDF p.2, lossless comparison. -/
def numberWord {L : ℕ} (occupation : Fin L → ℕ) : WordFock L :=
  lp.single 2 occupation 1

/-- Coefficients of the finite product coherent word, PDF p.2. -/
def coherentWordCoefficient {L : ℕ} (alpha : Fin L → ℂ) (occupation : Fin L → ℕ) : ℂ :=
  ∏ i, coherentCoefficient (alpha i) (occupation i)

/-- The Hilbert realization of the product coherent word, PDF p.2. The theorem
concludes its coefficients and unit norm. Thus the fallback can never stand in
for a normalized source state in a stated result. -/
def coherentWord {L : ℕ} (alpha : Fin L → ℂ) : WordFock L :=
  if h : ∃ u : WordFock L, ∀ occupation,
      u occupation = coherentWordCoefficient alpha occupation then
    Classical.choose h else 0

/-- Coefficients and normalization, made a conclusion rather than an assumption
of the discrimination theorem, PDF p.2. -/
def CoherentWordRealized {L : ℕ} (alpha : Fin L → ℂ) : Prop :=
  (∀ occupation, coherentWord alpha occupation = coherentWordCoefficient alpha occupation) ∧
    ‖coherentWord alpha‖ = 1

/-- A binary POVM {T,I-T} on the full word Hilbert space, PDF p.2 operational
pairwise-confusion convention. T is the decision for the first word. -/
structure BinaryEffect (L : ℕ) where
  operator : WordFock L →L[ℂ] WordFock L
  selfAdjoint : ContinuousLinearMap.adjoint operator = operator
  nonnegative : ∀ u, 0 ≤ (inner (𝕜 := ℂ) u (operator u)).re
  atMostIdentity : ∀ u, (inner (𝕜 := ℂ) u (operator u)).re ≤ ‖u‖ ^ 2

/-- Uniformity is not assumed: p and 1-p are the binary priors, PDF p.2.
For normalized states and an effect T this is the executed average error. -/
def binaryAverageError {L : ℕ} (p : ℝ) (u v : WordFock L)
    (T : WordFock L →L[ℂ] WordFock L) : ℝ :=
  p * (1 - (inner (𝕜 := ℂ) u (T u)).re) +
    (1 - p) * (inner (𝕜 := ℂ) v (T v)).re

/-- All achievable binary average errors, PDF p.2. IsLeast of this set asserts
both an attained minimum and its lower bound against every binary POVM. -/
def binaryErrorValues {L : ℕ} (p : ℝ) (u v : WordFock L) : Set ℝ :=
  {e | ∃ T : BinaryEffect L, e = binaryAverageError p u v T.operator}

/-- Positive frequency grid, PDF p.3: k starts at one, not zero. -/
def gridFrequency (spacing : ℝ) {m : ℕ} (i : Fin m) : ℝ :=
  (i.val + 1 : ℕ) * spacing

/-- The far-field quadratic transmissivity D(omega), PDF pp.3-4.
Dc is D(cutoff); physical parameters give transmissivity in (0,1]. -/
def gridTransmission (spacing cutoff Dc : ℝ) {m : ℕ} (i : Fin m) : ℝ :=
  Dc * (gridFrequency spacing i / cutoff) ^ 2

/-- Normal-ordered ensemble mean photon energy, PDF p.1 Eq.(5). -/
def allocationEnergy {m : ℕ} (hbar spacing : ℝ) (N : Fin m → ℝ) : ℝ :=
  ∑ i, hbar * gridFrequency spacing i * N i

/-- The explicitly printed receiver objective, PDF p.2 Eq.(11). This scalar
functional makes no identification of a homodyne modulation ensemble. -/
def receiverObjective {m : ℕ} (spacing cutoff Dc xi : ℝ) (N : Fin m → ℝ) : ℝ :=
  ∑ i, xi * Real.logb 2 (1 + gridTransmission spacing cutoff Dc i * N i / xi ^ 2)

/-- Feasible photon allocations, PDF p.1 Eq.(5) and p.4 maximization. -/
def FeasibleAllocation {m : ℕ} (hbar spacing E : ℝ) (N : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ N i) ∧ allocationEnergy hbar spacing N = E

/-- Attained maximum of the numerical objective (11), PDF p.4. Neither a
maximizer nor a KKT condition is an input hypothesis of the theorem. -/
def OptimalAllocation {m : ℕ} (hbar spacing cutoff Dc xi E : ℝ)
    (N : Fin m → ℝ) : Prop :=
  FeasibleAllocation hbar spacing E N ∧
    ∀ M : Fin m → ℝ, FeasibleAllocation hbar spacing E M →
      receiverObjective spacing cutoff Dc xi M ≤ receiverObjective spacing cutoff Dc xi N

/-- Printed allocation, PDF p.4: beta absorbs the common xi/log(2) factor.
The theorem requires beta,hbar,omega and eta to be positive. -/
def receiverAllocation {m : ℕ} (hbar spacing cutoff Dc xi beta : ℝ) : Fin m → ℝ :=
  fun i => max (1 / (beta * hbar * gridFrequency spacing i) -
    xi ^ 2 / gridTransmission spacing cutoff Dc i) 0

/-- Sanity check: vacuum has zero entropy. -/
example : bosonicEntropy 0 = 0 := by
  simp [bosonicEntropy]

/-- Sanity check: the zero binary effect always decides the second word. -/
example {L : ℕ} (p : ℝ) (u v : WordFock L) :
    binaryAverageError p u v 0 = p := by
  simp [binaryAverageError]

/-- Sanity check: zero photon allocation has zero energy and zero objective. -/
example {m : ℕ} (hbar spacing cutoff Dc xi : ℝ) :
    allocationEnergy (m := m) hbar spacing (fun _ => 0) = 0 ∧
      receiverObjective (m := m) spacing cutoff Dc xi (fun _ => 0) = 0 := by
  simp [allocationEnergy, receiverObjective]

/-- Sanity check: the first grid frequency is positive spacing, not zero. -/
example (spacing : ℝ) : gridFrequency spacing (0 : Fin 1) = spacing := by
  simp [gridFrequency]

/-- Sanity check: the vacuum coefficient is one. -/
example : coherentCoefficient 0 0 = 1 := by
  simp [coherentCoefficient]

/-- Sanity check: the no-loss vacuum entry has its original coefficient. -/
example (rho : ℕ → ℕ → ℂ) : vacuumLossTerm 1 rho 0 0 0 = rho 0 0 := by
  simp [vacuumLossTerm]

end QAlgorithms.Papers.Independent.Frontier30.P21


