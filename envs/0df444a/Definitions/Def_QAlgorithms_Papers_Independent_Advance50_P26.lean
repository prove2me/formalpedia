-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P26
-- name    : QAlgorithms_Papers_Independent_Advance50_P26
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T10:39:49.183443+00:00
-- url     : https://prove2.me/theorems/b1931f90-50bb-4cd5-9e38-72a6da4f299c
-- title:
--   Definitions for Renyi Entropy and Free Energy
-- statement:
--   The objects the formalized statements of *Renyi Entropy and Free Energy* (arXiv:1102.2098) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `classicalRenyiNats`: PDF p.1, (1): real-order classical Renyi entropy in natural units. The q = 1 branch is the source's Shannon extension. Only q > 0 is interpreted.
--   - `referenceEnergies`: PDF p.2: the energies constructed from a strictly positive law at temperature T0. They are not a separately supplied spectrum: E_i = -T0 log p_i.
--   - `classicalPartition`: PDF p.2: the classical partition function at temperature T, in units k = 1.
--   - `classicalFreeEnergy`: PDF p.2: classical Helmholtz free energy F_E(T) = -T log Z_E(T), with k = 1.
--   - `thermalPartition`: PDF p.3, (4): Z_H(k,T) = Tr exp(-H/(kT)). Correct the printed E in (4) to H, as required by (3) and the final calculation of (9). For Hermitian H and positive k,T this trace is real and strictly positive.
--   - `thermalGibbs`: PDF p.3, (3): the actual normalized Gibbs matrix at temperature T. The accepted exponential-normalization definition is used with exponent -H/(kT). For nonempty finite Hermitian H and k,T > 0 this is positive definite with trace one; these properties follow from the construction and are not assumed identities.
--   - `thermalFreeEnergy`: PDF p.3, (5): Helmholtz free energy of the fixed Hamiltonian H and fixed k.
--   - `renyiEntropyWithBoltzmann`: PDF p.3, (6)-(7): natural-log spectral Renyi entropy with Boltzmann constant k. For q = 1 use -k Tr(rho log rho), spectrally evaluated with 0 log 0 = 0. For q > 0 and a density matrix the trace power is positive; taking the real part therefore represents the real trace and does not discard an imaginary contribution.
--   - `qDerivative`: PDF p.4: D_a f(x) = (f(ax) - f(x))/(ax - x). The application in (11) uses a = q inverse and x = T > 0, with q > 0 and q != 1.
-- source:
--   Renyi Entropy and Free Energy, arXiv:1102.2098v4, https://arxiv.org/abs/1102.2098v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SDP
import Definitions.Def_QAlgorithms_Defs_ZeroSumGeometry
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

/-!
Statements from John C. Baez, *Renyi Entropy and Free Energy*, arXiv:1102.2098v4.
Only finite systems and finite positive entropy orders are used in the target statements.
The operational maximum-work claim is deferred: the source does not specify a process model.

Source corrections on PDF p.3: use H in the partition function (4), restore k in the
intermediate exponential, and restore logarithms of partition functions in the following
line. Equations (3), (5), (6), and the final calculation yielding (9) determine these corrections.
They do not change the final displayed result (9). Independent moderation is pending.
-/

noncomputable section

open Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P26

-- Reuse pinned accepted declarations, as required by the repair instruction.
-- The Shannon interface uses Fin d; finite reindexing below preserves arbitrary alphabets.
open QAlgorithms.Papers.Independent.Support50.P15 (shannonEntropyNats)
open QAlgorithms.ZeroSum (classicalGibbs)
open QAlgorithms.Papers.Independent.Dependency50.P35 (spectralPower)

/-- PDF p.1, (1): real-order classical Renyi entropy in natural units.
The q = 1 branch is the source's Shannon extension. Only q > 0 is interpreted. -/
def classicalRenyiNats {I : Type*} [Fintype I] (p : I → ℝ) (q : ℝ) : ℝ :=
  if q = 1 then shannonEntropyNats (fun i => p ((Fintype.equivFin I).symm i))
  else Real.log (∑ i, (p i) ^ q) / (1 - q)

/-- PDF p.2: the energies constructed from a strictly positive law at temperature T0.
They are not a separately supplied spectrum: E_i = -T0 log p_i. -/
def referenceEnergies {I : Type*} (p : I → ℝ) (T0 : ℝ) : I → ℝ :=
  fun i => -T0 * Real.log (p i)

/-- PDF p.2: the classical partition function at temperature T, in units k = 1. -/
def classicalPartition {I : Type*} [Fintype I] (E : I → ℝ) (T : ℝ) : ℝ :=
  ∑ i, Real.exp (-E i / T)

/-- PDF p.2: classical Helmholtz free energy F_E(T) = -T log Z_E(T), with k = 1. -/
def classicalFreeEnergy {I : Type*} [Fintype I] (E : I → ℝ) (T : ℝ) : ℝ :=
  -T * Real.log (classicalPartition E T)

/-- PDF p.3, (4): Z_H(k,T) = Tr exp(-H/(kT)).
Correct the printed E in (4) to H, as required by (3) and the final calculation of (9).
For Hermitian H and positive k,T this trace is real and strictly positive. -/
def thermalPartition {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (k T : ℝ) : ℝ :=
  (NormedSpace.exp ((-(k * T)⁻¹) • H)).trace.re

/-- PDF p.3, (3): the actual normalized Gibbs matrix at temperature T.
The accepted exponential-normalization definition is used with exponent -H/(kT).
For nonempty finite Hermitian H and k,T > 0 this is positive definite with trace one;
these properties follow from the construction and are not assumed identities. -/
def thermalGibbs {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (k T : ℝ) : Matrix I I ℂ :=
  QAlgorithms.gibbsState ((-(k * T)⁻¹) • H)

/-- PDF p.3, (5): Helmholtz free energy of the fixed Hamiltonian H and fixed k. -/
def thermalFreeEnergy {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (k T : ℝ) : ℝ :=
  -k * T * Real.log (thermalPartition H k T)

/-- PDF p.3, (6)-(7): natural-log spectral Renyi entropy with Boltzmann constant k.
For q = 1 use -k Tr(rho log rho), spectrally evaluated with 0 log 0 = 0.
For q > 0 and a density matrix the trace power is positive; taking the real part
therefore represents the real trace and does not discard an imaginary contribution. -/
def renyiEntropyWithBoltzmann {I : Type} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) (k q : ℝ) : ℝ :=
  if q = 1 then -k * (cfc (fun x : ℝ => x * Real.log x) rho).trace.re
  else k * Real.log (spectralPower rho q).trace.re / (1 - q)

/-- PDF p.4: D_a f(x) = (f(ax) - f(x))/(ax - x).
The application in (11) uses a = q inverse and x = T > 0, with q > 0 and q != 1. -/
def qDerivative (f : ℝ → ℝ) (a x : ℝ) : ℝ :=
  (f (a * x) - f x) / (a * x - x)

/-! Definition sanity examples. These do not prove the target theorems. -/

example : shannonEntropyNats (fun _ : Fin 1 => (1 : ℝ)) = 0 := by
  simp [shannonEntropyNats]

example (q : ℝ) : classicalRenyiNats (fun _ : Fin 1 => (1 : ℝ)) q = 0 := by
  simp [classicalRenyiNats, shannonEntropyNats]

example (T0 : ℝ) : referenceEnergies (fun _ : Fin 1 => (1 : ℝ)) T0 = 0 := by
  funext i
  simp [referenceEnergies]

example (T : ℝ) : classicalPartition (fun _ : Fin 1 => (0 : ℝ)) T = 1 := by
  simp [classicalPartition]

example (T : ℝ) : classicalGibbs (fun _ : Unit => -(0 : ℝ) / T) () = 1 := by
  simp [classicalGibbs, PMF.ofFintype_apply]

example (T : ℝ) : classicalFreeEnergy (fun _ : Fin 1 => (0 : ℝ)) T = 0 := by
  simp [classicalFreeEnergy, classicalPartition]

-- The frozen interface specifies the zero exponent even on the kernel.
-- Positive entropy orders below use its spectral real powers.
example {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) : spectralPower A 0 = 1 := by
  simp [spectralPower]

example (k T : ℝ) : thermalPartition (0 : Matrix (Fin 2) (Fin 2) ℂ) k T = 2 := by
  simp [thermalPartition, NormedSpace.exp_zero, Matrix.trace_one]

example (k T : ℝ) : thermalGibbs (0 : Matrix (Fin 1) (Fin 1) ℂ) k T = 1 := by
  simp [thermalGibbs, QAlgorithms.gibbsState, NormedSpace.exp_zero, Matrix.trace_one]

example (k T : ℝ) : thermalFreeEnergy (0 : Matrix (Fin 2) (Fin 2) ℂ) k T =
    -k * T * Real.log 2 := by
  simp [thermalFreeEnergy, thermalPartition, NormedSpace.exp_zero, Matrix.trace_one]

example {I : Type} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) (k : ℝ) : renyiEntropyWithBoltzmann rho k 1 =
      -k * (cfc (fun x : ℝ => x * Real.log x) rho).trace.re := by
  simp [renyiEntropyWithBoltzmann]

example : qDerivative (fun x : ℝ => x) 2 1 = 1 := by
  norm_num [qDerivative]

end QAlgorithms.Papers.Independent.Advance50.P26


