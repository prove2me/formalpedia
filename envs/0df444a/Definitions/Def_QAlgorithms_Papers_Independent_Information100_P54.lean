-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54
-- name    : QAlgorithms_Papers_Independent_Information100_P54
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T12:06:26.438545+00:00
-- url     : https://prove2.me/theorems/1960612c-3215-4a91-ae02-bf7a60a68c23
-- title:
--   Definitions for Energy-constrained two-way capacities of pure-loss and quantum-limited amplifier channels
-- statement:
--   The objects the formalized statements of *Energy-constrained two-way capacities of pure-loss and quantum-limited amplifier channels* (arXiv:2610.06832) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `thermalEntropy`: arXiv:2610.06832v1, PDF pp.1,7, Eq.(2): thermal entropy in bits, with 0 log 0 = 0.
--   - `lossRate`: arXiv:2610.06832v1, PDF p.1, Eq.(2): the finite-energy rate function.
--   - `shannonEntropy`: arXiv:2610.06832v1, PDF p.7, Eq.(A2): extended Shannon entropy in bits. For probability laws each summand is nonnegative; divergent entropy is infinity.
--   - `countMean`: arXiv:2610.06832v1, PDF pp.8–9: extended first moment of a photon-count law.
--   - `sectorDimension`: arXiv:2610.06832v1, PDF p.9, Eq.(A15): s-mode m-photon sector dimension. Every theorem using this quantity requires s >= 1.
--   - `binomialMass`: arXiv:2610.06832v1, PDF p.7: binomial mass; finite sums range over 0,...,m.
--   - `sectorCost`: arXiv:2610.06832v1, PDF p.12, Eq.(B15): explicit scalar sector-resource cost. The index ell counts lost photons, not received photons.
--   - `averageSectorCost`: arXiv:2610.06832v1, PDF p.14, Eq.(B37): extended expected sector cost. For physical parameters sectorCost is nonnegative, so no divergent real tsum is used.
--   - `relativeEntropyBits`: arXiv:2610.06832v1, PDF pp.7–8, Eq.(A6): finite relative entropy in bits. The accepted Umegaki definition uses nats and enforces support inclusion. Invalid unnormalized arguments receive infinity; theorem arguments are states.
--   - `relativeEntanglement`: arXiv:2610.06832v1, PDF p.8, Eq.(A6): finite-dimensional REE across I:J. The finite convex hull of product states is already closed in finite dimensions.
--   - `Occupations`: arXiv:2610.06832v1, PDF p.9, Eq.(A15): occupation-basis ambient space. For an m-photon sector, every individual occupation lies between 0 and m. Zero padding into this finite ambient space preserves the Reference:Bob REE cut.
--   - `occupationTotal`: arXiv:2610.06832v1, PDF p.9: total occupation of a number-basis vector.
--   - `sectorLossAmplitude`: arXiv:2610.06832v1, PDF pp.7,10,13, Eqs.(A17),(B17): number-basis amplitude of the purification of the resource J. r is Alice's reference, b is Bob's received occupation, and ell is the lost occupation. This is the vacuum beam-splitter expansion on each mode, applied to the normalized sector pair. The guard enforces exact total input number m and r=b+ell componentwise.
--   - `sectorResource`: arXiv:2610.06832v1, PDF p.10, Eq.(A17): sector Choi resource, obtained by tracing the loss environment out of the explicit purified state. All amplitudes are real in this fixed number-basis convention. The two factors are Reference:Bob.
--   - `receivedProbability`: arXiv:2610.06832v1, PDF p.12, Eq.(B13): actual probability of Bob's received total k, computed by the number-projector trace on the resource.
--   - `conditionalSectorResource`: arXiv:2610.06832v1, PDF p.12, Eq.(B14): resource conditioned on the received total k. Normalize by its actual computed probability, not by an assumed binomial law. The theorem restricts k<=m and 0<eta<1, so this probability is positive.
--   - `stateCopies`: arXiv:2610.06832v1, PDF p.8, Eq.(A6): independent copies regrouped across aggregate Alice:Bob. The parties within one copy need not be independent.
--   - `regularizedEntanglement`: arXiv:2610.06832v1, PDF p.8, Eq.(A6): regularized REE of a fixed finite state. The liminf is the regularization limit, which exists by subadditivity on normalized finite states. Copy number r+1 is always positive.
--   - `bobPinching`: arXiv:2610.06832v1, PDF p.9, Eq.(A13): Bob pinching with outcome forgotten.
--   - `pinchingProbability`: arXiv:2610.06832v1, PDF p.9, Eq.(A13): Bob projection-outcome probabilities.
--   - `maximallyEntangledProjector`: arXiv:2610.06832v1, PDF p.7, Eq.(A3): maximally entangled projector. Theorems require d >= 1.
-- source:
--   Energy-constrained two-way capacities of pure-loss and quantum-limited amplifier channels, arXiv:2610.06832v1, https://arxiv.org/abs/2610.06832v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability

noncomputable section

open scoped ENNReal Matrix
open Filter

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P54

/-- arXiv:2610.06832v1, PDF pp.1,7, Eq.(2): thermal entropy in bits, with 0 log 0 = 0. -/
def thermalEntropy (x : ℝ) : ℝ :=
  ((x + 1) * Real.log (x + 1) - x * Real.log x) / Real.log 2

/-- arXiv:2610.06832v1, PDF p.1, Eq.(2): the finite-energy rate function. -/
def lossRate (eta x : ℝ) : ℝ :=
  thermalEntropy x - thermalEntropy ((1 - eta) * x)

/-- arXiv:2610.06832v1, PDF p.7, Eq.(A2): extended Shannon entropy in bits.
For probability laws each summand is nonnegative; divergent entropy is infinity. -/
def shannonEntropy {I : Type*} (p : I → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (-(p i).toReal * Real.log (p i).toReal / Real.log 2)

/-- arXiv:2610.06832v1, PDF pp.8–9: extended first moment of a photon-count law. -/
def countMean (p : PMF ℕ) : ℝ≥0∞ :=
  ∑' m : ℕ, (m : ℝ≥0∞) * p m

/-- arXiv:2610.06832v1, PDF p.9, Eq.(A15): s-mode m-photon sector dimension.
Every theorem using this quantity requires s >= 1. -/
def sectorDimension (s m : ℕ) : ℕ :=
  (s + m - 1).choose m

/-- arXiv:2610.06832v1, PDF p.7: binomial mass; finite sums range over 0,...,m. -/
def binomialMass (m : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (m.choose k : ℝ) * p ^ k * (1 - p) ^ (m - k)

/-- arXiv:2610.06832v1, PDF p.12, Eq.(B15): explicit scalar sector-resource cost.
The index ell counts lost photons, not received photons. -/
def sectorCost (eta : ℝ) (s m : ℕ) : ℝ :=
  Real.log (sectorDimension s m) / Real.log 2 -
    ∑ ell ∈ Finset.range (m + 1), binomialMass m (1 - eta) ell *
      (Real.log (sectorDimension s ell) / Real.log 2)

/-- arXiv:2610.06832v1, PDF p.14, Eq.(B37): extended expected sector cost.
For physical parameters sectorCost is nonnegative, so no divergent real tsum is used. -/
def averageSectorCost (eta : ℝ) (s : ℕ) (p : PMF ℕ) : ℝ≥0∞ :=
  ∑' m, p m * ENNReal.ofReal (sectorCost eta s m)

/-- arXiv:2610.06832v1, PDF pp.7–8, Eq.(A6): finite relative entropy in bits.
The accepted Umegaki definition uses nats and enforces support inclusion.
Invalid unnormalized arguments receive infinity; theorem arguments are states. -/
def relativeEntropyBits {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : ℝ≥0∞ :=
  if h : QAlgorithms.IsDensityMatrix rho ∧ QAlgorithms.IsDensityMatrix sigma then
    QAlgorithms.QuantumLoss.umegakiEntropy rho sigma h.1 h.2 / ENNReal.ofReal (Real.log 2)
  else ⊤

/-- arXiv:2610.06832v1, PDF p.8, Eq.(A6): finite-dimensional REE across I:J.
The finite convex hull of product states is already closed in finite dimensions. -/
def relativeEntanglement {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (rho : Matrix (I × J) (I × J) ℂ) : ℝ≥0∞ :=
  sInf {e | ∃ sigma : Matrix (I × J) (I × J) ℂ,
    QAlgorithms.Entanglement.IsSeparableDensity sigma ∧ e = relativeEntropyBits rho sigma}

/-- arXiv:2610.06832v1, PDF p.9, Eq.(A15): occupation-basis ambient space.
For an m-photon sector, every individual occupation lies between 0 and m.
Zero padding into this finite ambient space preserves the Reference:Bob REE cut. -/
abbrev Occupations (s m : ℕ) := Fin s → Fin (m + 1)

/-- arXiv:2610.06832v1, PDF p.9: total occupation of a number-basis vector. -/
def occupationTotal {s m : ℕ} (r : Occupations s m) : ℕ :=
  ∑ j, (r j).val

/-- arXiv:2610.06832v1, PDF pp.7,10,13, Eqs.(A17),(B17): number-basis
amplitude of the purification of the resource J. r is Alice's reference,
b is Bob's received occupation, and ell is the lost occupation. This is the
vacuum beam-splitter expansion on each mode, applied to the normalized sector pair.
The guard enforces exact total input number m and r=b+ell componentwise. -/
def sectorLossAmplitude (eta : ℝ) (s m : ℕ)
    (r b ell : Occupations s m) : ℝ :=
  if occupationTotal r = m ∧ ∀ j, (r j).val = (b j).val + (ell j).val then
    Real.sqrt (((∏ j, ((r j).val.choose (ell j).val : ℝ)) *
      eta ^ occupationTotal b * (1 - eta) ^ occupationTotal ell) /
      (sectorDimension s m : ℝ))
  else 0

/-- arXiv:2610.06832v1, PDF p.10, Eq.(A17): sector Choi resource, obtained
by tracing the loss environment out of the explicit purified state. All amplitudes
are real in this fixed number-basis convention. The two factors are Reference:Bob. -/
def sectorResource (eta : ℝ) (s m : ℕ) :
    Matrix (Occupations s m × Occupations s m)
      (Occupations s m × Occupations s m) ℂ :=
  fun a c => ∑ ell : Occupations s m,
    (sectorLossAmplitude eta s m a.1 a.2 ell : ℂ) *
      (sectorLossAmplitude eta s m c.1 c.2 ell : ℂ)

/-- arXiv:2610.06832v1, PDF p.12, Eq.(B13): actual probability of Bob's
received total k, computed by the number-projector trace on the resource. -/
def receivedProbability (eta : ℝ) (s m k : ℕ) : ℝ :=
  ∑ r : Occupations s m, ∑ b : Occupations s m,
    if occupationTotal b = k then (sectorResource eta s m (r, b) (r, b)).re else 0

/-- arXiv:2610.06832v1, PDF p.12, Eq.(B14): resource conditioned on the
received total k. Normalize by its actual computed probability, not by an assumed
binomial law. The theorem restricts k<=m and 0<eta<1, so this probability is positive. -/
def conditionalSectorResource (eta : ℝ) (s m k : ℕ) :
    Matrix (Occupations s m × Occupations s m)
      (Occupations s m × Occupations s m) ℂ :=
  fun a c => if occupationTotal a.2 = k ∧ occupationTotal c.2 = k then
    sectorResource eta s m a c / (receivedProbability eta s m k : ℂ)
  else 0

/-- arXiv:2610.06832v1, PDF p.8, Eq.(A6): independent copies regrouped across
aggregate Alice:Bob. The parties within one copy need not be independent. -/
def stateCopies {I J : Type*} (rho : Matrix (I × J) (I × J) ℂ) (r : ℕ) :
    Matrix ((Fin r → I) × (Fin r → J)) ((Fin r → I) × (Fin r → J)) ℂ :=
  fun a b => ∏ t, rho (a.1 t, a.2 t) (b.1 t, b.2 t)

/-- arXiv:2610.06832v1, PDF p.8, Eq.(A6): regularized REE of a fixed finite state.
The liminf is the regularization limit, which exists by subadditivity on normalized
finite states. Copy number r+1 is always positive. -/
def regularizedEntanglement {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (rho : Matrix (I × J) (I × J) ℂ) : ℝ≥0∞ :=
  Filter.liminf (fun r : ℕ => relativeEntanglement (stateCopies rho (r + 1)) /
    (r + 1 : ℝ≥0∞)) Filter.atTop

/-- arXiv:2610.06832v1, PDF p.9, Eq.(A13): Bob pinching with outcome forgotten. -/
def bobPinching {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] (P : K → Matrix J J ℂ)
    (rho : Matrix (I × J) (I × J) ℂ) : Matrix (I × J) (I × J) ℂ :=
  ∑ k, (Matrix.kronecker (1 : Matrix I I ℂ) (P k)) * rho *
    (Matrix.kronecker (1 : Matrix I I ℂ) (P k)).conjTranspose

/-- arXiv:2610.06832v1, PDF p.9, Eq.(A13): Bob projection-outcome probabilities. -/
def pinchingProbability {I J K : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (P : K → Matrix J J ℂ) (rho : Matrix (I × J) (I × J) ℂ) (k : K) : ℝ≥0∞ :=
  ENNReal.ofReal (((Matrix.kronecker (1 : Matrix I I ℂ) (P k)) * rho).trace.re)

/-- arXiv:2610.06832v1, PDF p.7, Eq.(A3): maximally entangled projector.
Theorems require d >= 1. -/
def maximallyEntangledProjector (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun a b => if a.1 = a.2 ∧ b.1 = b.2 then (d : ℂ)⁻¹ else 0

example : thermalEntropy 0 = 0 := by simp [thermalEntropy]

example (eta : ℝ) : lossRate eta 0 = 0 := by simp [lossRate, thermalEntropy]

example {I : Type*} : shannonEntropy (fun _ : I => 0) = 0 := by
  simp [shannonEntropy]

example (m : ℕ) : sectorDimension 1 m = 1 := by simp [sectorDimension]

example (m : ℕ) (p : ℝ) : binomialMass m p 0 = (1 - p) ^ m := by
  simp [binomialMass]

example (eta : ℝ) (m : ℕ) : sectorCost eta 1 m = 0 := by
  simp [sectorCost, sectorDimension]

example {I : Type*} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) (h : ¬ QAlgorithms.IsDensityMatrix rho) :
    relativeEntropyBits rho sigma = ⊤ := by simp [relativeEntropyBits, h]

example {I J : Type*} (rho : Matrix (I × J) (I × J) ℂ)
    (a b : (Fin 0 → I) × (Fin 0 → J)) : stateCopies rho 0 a b = 1 := by
  simp [stateCopies]

example : maximallyEntangledProjector 1 = (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) := by
  ext a b
  have ha : a.1 = a.2 := Subsingleton.elim _ _
  have hb : b.1 = b.2 := Subsingleton.elim _ _
  have hab : a = b := Subsingleton.elim _ _
  simp [maximallyEntangledProjector, ha, hb, Matrix.one_apply, hab]

example (s : ℕ) : occupationTotal (fun _ : Fin s => (0 : Fin 1)) = 0 := by
  simp [occupationTotal]

example (eta : ℝ) (s m : ℕ) (r b ell : Occupations s m)
    (h : occupationTotal r ≠ m) : sectorLossAmplitude eta s m r b ell = 0 := by
  simp [sectorLossAmplitude, h]

example (eta : ℝ) (s m k : ℕ)
    (a c : Occupations s m × Occupations s m) (h : occupationTotal a.2 ≠ k) :
    conditionalSectorResource eta s m k a c = 0 := by
  simp [conditionalSectorResource, h]

example (eta : ℝ) (s : ℕ) (r b ell : Occupations s 0) :
    sectorLossAmplitude eta s 0 r b ell = 1 := by
  have hr : r = fun _ => 0 := by
    funext j
    apply Fin.ext
    have h := (r j).isLt
    omega
  have hb : b = fun _ => 0 := by
    funext j
    apply Fin.ext
    have h := (b j).isLt
    omega
  have he : ell = fun _ => 0 := by
    funext j
    apply Fin.ext
    have h := (ell j).isLt
    omega
  subst r
  subst b
  subst ell
  simp [sectorLossAmplitude, occupationTotal, sectorDimension]

end QAlgorithms.Papers.Independent.Information100.P54


