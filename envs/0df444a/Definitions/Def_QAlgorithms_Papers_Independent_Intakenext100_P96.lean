-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P96
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P96
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T08:47:14.17573+00:00
-- url     : https://prove2.me/theorems/ba5fdf89-1e22-4819-b8e4-a70519d1c4ed
-- title:
--   Definitions for Quantum Illumination
-- statement:
--   The objects the formalized statements of *Quantum Illumination* (arXiv:0803.2022) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SignalIndex`: PDF pp.2--3: a vacuum outcome and d orthogonal single-photon modes.
--   - `ModelParameters`: PDF pp.2--3: parameters for the exact retained finite model. The physical approximation db << 1 is not a claim of full-channel exactness.
--   - `background`: PDF p.3, (1.0): the retained thermal background, including the vacuum.
--   - `signalState`: PDF p.3: embed the normalized single-photon input with zero vacuum amplitude.
--   - `signalTest`: PDF p.3: the yes projector of the unentangled test.
--   - `signalPresent`: PDF p.3, (1.1): returned state when the object is present.
--   - `pairState`: PDF pp.5--6: Phi_d = d^(-1/2) sum_k |k>_S |k>_A; no vacuum component.
--   - `pairTest`: PDF pp.6--7: the ideal joint yes projector onto Phi_d.
--   - `ancillaMixed`: PDF p.6: the perfectly retained ancilla's completely mixed marginal I_A/d.
--   - `pairAbsent`: PDF p.6, retained body of (8.0): rho_SA0 = rho_0 tensor I_A/d.
--   - `pairPresent`: PDF p.6, retained body of (8.1): only the signal traverses the noisy path.
--   - `ebits`: PDF p.9, (14): logarithmic mode count, identified with marginal entropy in the theorem.
--   - `binaryError`: PDF pp.3--4: equal-prior error of the binary effect whose yes answer means present.
--   - `iidEqualPriorError`: PDF p.4: optimal equal-prior error over all joint n-copy binary POVMs. Reuse the accepted tensor copies and total effect-error infimum, dividing by two for equal priors. On density inputs that extended infimum is finite and in [0,1], so toReal never uses its infinity default.
--   - `countMass`: PDF pp.4--5: probability of k yes outcomes in n independent Bernoulli trials.
--   - `countingError`: PDF pp.4--5,8: minimum error after counting yes outcomes and optimally deciding from the entire count. This includes both hypotheses with prior probability 1/2.
--   - `errorFactor`: PDF p.4, (3): exponential error factor, indexed using n+1 copies so that all root exponents have a strictly positive denominator.
--   - `illuminationChernoffFactor`: PDF p.4, (3), p.7, (11): the one-copy scalar Chernoff factor. Reuse the accepted Petz overlap with the arguments reversed: cyclicity of trace identifies Tr(rho1^s rho0^(1-s)) with the source Tr(rho0^(1-s) rho1^s). Using 0<s<1 includes one-sided endpoint limits without kernel 0^0 conventions. For density inputs this is a nonempty, bounded-below real infimum. It differs from the accepted oscillator N-copy quantumChernoff bound.
--   - `binaryChernoff`: PDF pp.4--5,8: Chernoff factor for the two Bernoulli yes probabilities.
--   - `entangledFactor`: PDF p.7, first line of (11), with its printed parentheses and denominator.
-- source:
--   Quantum Illumination, arXiv:0803.2022v2, https://arxiv.org/abs/0803.2022v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P15
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

/-!
# Quantum Illumination, arXiv:0803.2022v2

All states below belong to the retained vacuum/single-photon model, (1.0), (1.1),
(8.0), (8.1). No equality with the full optical thermal channel is asserted.
Page numbers are PDF page numbers. The ancillary photon is retained perfectly.
All new definitions are local to this paper. Compilation is pending batch handoff.
-/

noncomputable section

open Filter
open scoped BigOperators Topology ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Intakenext100.P96

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2--3: a vacuum outcome and d orthogonal single-photon modes. -/
abbrev SignalIndex (d : ℕ) := Option (Fin d)

/-- PDF pp.2--3: parameters for the exact retained finite model.
The physical approximation db << 1 is not a claim of full-channel exactness. -/
structure ModelParameters where
  d : ℕ
  d_pos : 0 < d
  b : ℝ
  b_nonneg : 0 ≤ b
  db_le_one : (d : ℝ) * b ≤ 1
  eta : ℝ
  eta_nonneg : 0 ≤ eta
  eta_le_one : eta ≤ 1

/-- PDF p.3, (1.0): the retained thermal background, including the vacuum. -/
def background (d : ℕ) (b : ℝ) : Matrix (SignalIndex d) (SignalIndex d) ℂ :=
  Matrix.diagonal fun i => match i with
    | none => ((1 - (d : ℝ) * b : ℝ) : ℂ)
    | some _ => (b : ℂ)

/-- PDF p.3: embed the normalized single-photon input with zero vacuum amplitude. -/
def signalState {d : ℕ} (psi : EuclideanSpace ℂ (Fin d)) :
    EuclideanSpace ℂ (SignalIndex d) :=
  WithLp.toLp 2 (fun i => match i with | none => 0 | some k => psi k)

/-- PDF p.3: the yes projector of the unentangled test. -/
def signalTest {d : ℕ} (psi : EuclideanSpace ℂ (Fin d)) :
    Matrix (SignalIndex d) (SignalIndex d) ℂ :=
  pureDensity (signalState psi)

/-- PDF p.3, (1.1): returned state when the object is present. -/
def signalPresent {d : ℕ} (b eta : ℝ) (psi : EuclideanSpace ℂ (Fin d)) :
    Matrix (SignalIndex d) (SignalIndex d) ℂ :=
  ((1 - eta : ℝ) : ℂ) • background d b + (eta : ℂ) • signalTest psi

/-- PDF pp.5--6: Phi_d = d^(-1/2) sum_k |k>_S |k>_A; no vacuum component. -/
def pairState (d : ℕ) : EuclideanSpace ℂ (SignalIndex d × Fin d) :=
  if hd : 0 < d then
    letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    WithLp.toLp 2 (fun i => match i.1 with
      | none => 0
      | some k => finiteMaxEntangled (Fin d) (k, i.2))
  else 0

/-- PDF pp.6--7: the ideal joint yes projector onto Phi_d. -/
def pairTest (d : ℕ) : Matrix (SignalIndex d × Fin d) (SignalIndex d × Fin d) ℂ :=
  pureDensity (pairState d)

/-- PDF p.6: the perfectly retained ancilla's completely mixed marginal I_A/d. -/
def ancillaMixed (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  (((d : ℝ)⁻¹ : ℝ) : ℂ) • 1

/-- PDF p.6, retained body of (8.0): rho_SA0 = rho_0 tensor I_A/d. -/
def pairAbsent (d : ℕ) (b : ℝ) :
    Matrix (SignalIndex d × Fin d) (SignalIndex d × Fin d) ℂ :=
  Matrix.kronecker (background d b) (ancillaMixed d)

/-- PDF p.6, retained body of (8.1): only the signal traverses the noisy path. -/
def pairPresent (d : ℕ) (b eta : ℝ) :
    Matrix (SignalIndex d × Fin d) (SignalIndex d × Fin d) ℂ :=
  ((1 - eta : ℝ) : ℂ) • pairAbsent d b + (eta : ℂ) • pairTest d

/-- PDF p.9, (14): logarithmic mode count, identified with marginal entropy in the theorem. -/
def ebits (d : ℕ) : ℝ := Real.log (d : ℝ) / Real.log 2

/-- PDF pp.3--4: equal-prior error of the binary effect whose yes answer means present. -/
def binaryError {I : Type*} [Fintype I] [DecidableEq I]
    (rho0 rho1 M : Matrix I I ℂ) : ℝ :=
  (effectProb M rho0 + effectProb (1 - M) rho1) / 2

/-- PDF p.4: optimal equal-prior error over all joint n-copy binary POVMs.
Reuse the accepted tensor copies and total effect-error infimum, dividing by two
for equal priors. On density inputs that extended infimum is finite and in [0,1],
so toReal never uses its infinity default. -/
def iidEqualPriorError {I : Type*} [Fintype I] [DecidableEq I]
    (rho0 rho1 : Matrix I I ℂ) (n : ℕ) : ℝ :=
  (QAlgorithms.Papers.Independent.Claimed50.P15.optimalError true
    (QAlgorithms.Papers.Independent.Information100.P60.copies n rho0)
    (QAlgorithms.Papers.Independent.Information100.P60.copies n rho1)).toReal / 2

/-- PDF pp.4--5: probability of k yes outcomes in n independent Bernoulli trials. -/
def countMass (p : ℝ) (n k : ℕ) : ℝ :=
  (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)

/-- PDF pp.4--5,8: minimum error after counting yes outcomes and optimally deciding
from the entire count. This includes both hypotheses with prior probability 1/2. -/
def countingError (p0 p1 : ℝ) (n : ℕ) : ℝ :=
  (∑ k : Fin (n + 1), min (countMass p0 n k.val) (countMass p1 n k.val)) / 2

/-- PDF p.4, (3): exponential error factor, indexed using n+1 copies so that
all root exponents have a strictly positive denominator. -/
def errorFactor (err : ℕ → ℝ) (n : ℕ) : ℝ :=
  (2 * err (n + 1)) ^ (((n + 1 : ℕ) : ℝ)⁻¹)

/-- PDF p.4, (3), p.7, (11): the one-copy scalar Chernoff factor.
Reuse the accepted Petz overlap with the arguments reversed: cyclicity of trace
identifies Tr(rho1^s rho0^(1-s)) with the source Tr(rho0^(1-s) rho1^s).
Using 0<s<1 includes one-sided endpoint limits without kernel 0^0 conventions.
For density inputs this is a nonempty, bounded-below real infimum. It differs
from the accepted oscillator N-copy quantumChernoff bound. -/
def illuminationChernoffFactor {I : Type*} [Fintype I] [DecidableEq I]
    (rho0 rho1 : Matrix I I ℂ) : ℝ :=
  sInf ((fun s : ℝ =>
    QAlgorithms.Papers.Independent.Claimed50.P15.petzOverlap rho1 rho0 s) '' Set.Ioo 0 1)

/-- PDF pp.4--5,8: Chernoff factor for the two Bernoulli yes probabilities. -/
def binaryChernoff (p0 p1 : ℝ) : ℝ :=
  sInf ((fun s : ℝ => (1 - p0) ^ (1 - s) * (1 - p1) ^ s +
    p0 ^ (1 - s) * p1 ^ s) '' Set.Ioo 0 1)

/-- PDF p.7, first line of (11), with its printed parentheses and denominator. -/
def entangledFactor (d : ℕ) (b eta s : ℝ) : ℝ :=
  (1 - eta) ^ s * (1 + b / (d : ℝ) *
    (-1 + (1 + eta * (d : ℝ) / ((1 - eta) * b)) ^ s))

/-! Small definition-level sanity checks; theorem proofs are intentionally omitted. -/

example : background 1 (1 / 4) none none = (3 / 4 : ℂ) := by
  norm_num [background]

example {d : ℕ} (psi : EuclideanSpace ℂ (Fin d)) : signalState psi none = 0 := rfl

example {d : ℕ} (b : ℝ) (psi : EuclideanSpace ℂ (Fin d)) :
    signalPresent b 0 psi = background d b := by
  simp [signalPresent]

example : pairState 1 (some (0 : Fin 1), (0 : Fin 1)) = 1 := by
  norm_num [pairState, finiteMaxEntangled]

example (d : ℕ) (b : ℝ) : pairPresent d b 0 = pairAbsent d b := by
  simp [pairPresent]

example {I : Type*} (rho : Matrix I I ℂ) (x y : Fin 0 → I) :
    QAlgorithms.Papers.Independent.Information100.P60.copies 0 rho x y = 1 := by
  simp [QAlgorithms.Papers.Independent.Information100.P60.copies]

example (p0 p1 : ℝ) : countingError p0 p1 0 = 1 / 2 := by
  simp [countingError, countMass]

example : ebits 1 = 0 := by simp [ebits]

example (err : ℕ → ℝ) : errorFactor err 0 = 2 * err 1 := by
  simp [errorFactor]

end QAlgorithms.Papers.Independent.Intakenext100.P96


