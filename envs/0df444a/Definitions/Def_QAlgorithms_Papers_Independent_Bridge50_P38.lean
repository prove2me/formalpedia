-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P38
-- name    : QAlgorithms_Papers_Independent_Bridge50_P38
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T18:36:28.20778+00:00
-- url     : https://prove2.me/theorems/a697c1f6-1d55-46b7-9122-993282db3af3
-- title:
--   Definitions for Decoding quantum information via the Petz recovery map
-- statement:
--   The objects the formalized statements of *Decoding quantum information via the Petz recovery map* (arXiv:1504.04449) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SubspaceCode`: PDF pp.7–8, (3.1),(3.4): a positive integer dimensional subspace, represented by an orthonormal frame, and a CPTP decoder into the ambient input. Changing the frame does not change either Haar-average or entanglement fidelity.
--   - `codeMap`: PDF pp.7–8: the actual decoded map compressed to code coordinates. This compression need not preserve trace: ambient decoder leakage is retained.
--   - `codeAverageFidelity`: PDF p.7, (3.1): normalized Haar average of squared pure-state overlap.
--   - `codeEntanglementFidelity`: PDF p.8, (3.4): squared fidelity to the normalized maximally entangled code input, evaluated after the actual ambient decoder.
--   - `subspaceCapacity`: PDF p.8, (3.2)–(3.6): exact feasible positive integer message sizes. For a lawful channel and 0<=epsilon<1 the set is nonempty and bounded by card(A)^n. Extended suprema also give explicit empty/unbounded conventions off that domain.
--   - `averageCapacity`: PDF p.8, (3.3): average pure-state transmission capacity in qubits per block.
--   - `inputVariance`: PDF pp.6–7: relative information variance for the actual purified output. For density inputs and CPTP N the support inclusion needed by D and V is automatic.
--   - `quantumDispersion`: PDF p.7, (2.5): source dispersion in the two OPEN error regimes. Only used at epsilon != 1/2; this definition supplies no source value at 1/2.
--   - `secondOrderCorrection`: PDF pp.18–20: the second-order correction, with its zero middle-error case stated directly, without assigning a value to V_(1/2).
--   - `basisClock`: PDF p.10: Z_U = U diag(exp(2 pi i (k+1)/d)) U^dagger. The diagonal clock is the accepted one-based clock, not a zero-based variant.
--   - `firstAction`: PDF p.10: a map acting on the first register, keeping all second-register blocks.
--   - `collisionExponential`: PDF pp.6,11: the actual collision exponential tr(rho sigma^-1/2 rho sigma^-1/2). The inverse square root is the support inverse, zero on the kernel. This quadratic form is defined even for zero or unnormalized CP outputs, with no log(0) artifact.
--   - `symmetricErasure`: PDF pp.2,20: symmetric erasure channel into the input plus one orthogonal flag. Both transmitted off-diagonal entries and the erasure probability are explicit.
-- source:
--   Decoding quantum information via the Petz recovery map, arXiv:1504.04449v4, https://arxiv.org/abs/1504.04449v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P03
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

/-!
Beigi–Datta–Leditzky, arXiv:1504.04449v4. Page numbers are PDF pages.
The source's codes have isometric subspace inclusion and an ambient-space decoder.
Capacities below are total log2(message dimension), not per-use rates.
Theorem 3.1 and the quantitative Petz-decoder witness are deferred in HARD.md.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms

namespace QAlgorithms.Papers.Independent.Bridge50.P38

open QAlgorithms.Papers.Independent.Information100.P80 (log2)
open QAlgorithms.Papers.Independent.Information100.P63 (normalQuantile)
open QAlgorithms.Papers.Independent.Dependency50.P36
  (relativeEntropyFinite pairInformationVariance)
open QAlgorithms.Papers.Independent.Dependency50.P35
  (columnProjector pinch marginalAB marginalAC)
open QAlgorithms.Papers.Independent.Information100.P22
  (densityPurification singleUseInformation coherentInformation)
open QAlgorithms.Papers.Independent.Gap48.P23 (CompletelyPositive)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C : Type} [Fintype A] [DecidableEq A]
variable [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

/-- PDF pp.7–8, (3.1),(3.4): a positive integer dimensional subspace,
represented by an orthonormal frame, and a CPTP decoder into the ambient input.
Changing the frame does not change either Haar-average or entanglement fidelity. -/
structure SubspaceCode (A B : Type) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] where
  m : ℕ
  positive : 0 < m
  inclusion : Matrix A (Fin m) ℂ
  isometry : inclusionᴴ * inclusion = 1
  decoder : Superop B A
  decoder_channel : IsChannel decoder

/-- PDF pp.7–8: the actual decoded map compressed to code coordinates.
This compression need not preserve trace: ambient decoder leakage is retained. -/
def codeMap (N : Superop A B) (K : SubspaceCode A B) :
    Superop (Fin K.m) (Fin K.m) :=
  fun X => K.inclusionᴴ * K.decoder (N (conjSuperop K.inclusion X)) * K.inclusion

/-- PDF p.7, (3.1): normalized Haar average of squared pure-state overlap. -/
def codeAverageFidelity (N : Superop A B) (K : SubspaceCode A B) : ℝ :=
  QuditFidelity.averageFidelity K.m K.positive (codeMap N K)

/-- PDF p.8, (3.4): squared fidelity to the normalized maximally entangled
code input, evaluated after the actual ambient decoder. -/
def codeEntanglementFidelity (N : Superop A B) (K : SubspaceCode A B) : ℝ :=
  QuditFidelity.entanglementFidelity K.m K.positive (codeMap N K)

/-- PDF p.8, (3.2)–(3.6): exact feasible positive integer message sizes.
For a lawful channel and 0<=epsilon<1 the set is nonempty and bounded by card(A)^n.
Extended suprema also give explicit empty/unbounded conventions off that domain. -/
def subspaceCapacity (entanglement : Bool) (N : Superop A B)
    (n : ℕ) (epsilon : ℝ) : EReal :=
  sSup {r | ∃ K : SubspaceCode (Fin n → A) (Fin n → B),
    1 - epsilon ≤ (if entanglement then
      codeEntanglementFidelity (piSuperop (fun _ : Fin n => N)) K else
      codeAverageFidelity (piSuperop (fun _ : Fin n => N)) K) ∧
    r = (log2 K.m : EReal)}

/-- PDF p.8, (3.3): average pure-state transmission capacity in qubits per block. -/
def averageCapacity (N : Superop A B) (n : ℕ) (epsilon : ℝ) : EReal :=
  subspaceCapacity false N n epsilon

/-- PDF pp.6–7: relative information variance for the actual purified output.
For density inputs and CPTP N the support inclusion needed by D and V is automatic. -/
def inputVariance (N : Superop A B) (rho : Matrix A A ℂ) : ℝ :=
  let omega := idTensorSuperop N (pureDensity (densityPurification rho))
  pairInformationVariance omega (Matrix.kronecker (1 : Matrix A A ℂ) (traceLeft omega))

/-- PDF p.7, (2.5): source dispersion in the two OPEN error regimes.
Only used at epsilon != 1/2; this definition supplies no source value at 1/2. -/
def quantumDispersion (N : Superop A B) (epsilon : ℝ)
    (_hne : epsilon ≠ 1/2) : ℝ :=
  let vs := {v | ∃ rho : Matrix A A ℂ,
    (IsDensityMatrix rho ∧ coherentInformation N rho = singleUseInformation N) ∧
    v = inputVariance N rho}
  if epsilon < 1/2 then sInf vs else sSup vs

/-- PDF pp.18–20: the second-order correction, with its zero middle-error
case stated directly, without assigning a value to V_(1/2). -/
def secondOrderCorrection (N : Superop A B) (epsilon : ℝ) (n : ℕ) : ℝ :=
  if h : epsilon = 1/2 then 0 else
    Real.sqrt ((n : ℝ) * quantumDispersion N epsilon h) * normalQuantile epsilon

/-- PDF p.10: Z_U = U diag(exp(2 pi i (k+1)/d)) U^dagger.
The diagonal clock is the accepted one-based clock, not a zero-based variant. -/
def basisClock {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  (U : Matrix (Fin d) (Fin d) ℂ) *
    QAlgorithms.Papers.Independent.Gap48.P03.clockUnitary d *
    (U : Matrix (Fin d) (Fin d) ℂ)ᴴ

/-- PDF p.10: a map acting on the first register, keeping all second-register blocks. -/
def firstAction {R S T : Type} (L : Superop R S) : Superop (R × T) (S × T) :=
  fun X p q => L (fun i j => X (i,p.2) (j,q.2)) p.1 q.1

/-- PDF pp.6,11: the actual collision exponential tr(rho sigma^-1/2 rho sigma^-1/2).
The inverse square root is the support inverse, zero on the kernel. This quadratic
form is defined even for zero or unnormalized CP outputs, with no log(0) artifact. -/
def collisionExponential {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : ℝ :=
  let S := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) sigma
  (rho * S * rho * S).trace.re

/-- PDF pp.2,20: symmetric erasure channel into the input plus one orthogonal flag.
Both transmitted off-diagonal entries and the erasure probability are explicit. -/
def symmetricErasure (A : Type) [Fintype A] : Superop A (Option A) :=
  fun X p q => match p, q with
  | some a, some b => (1/2 : ℂ) * X a b
  | none, none => (1/2 : ℂ) * X.trace
  | _, _ => 0

/-- Sanity: the middle-error second-order term is exactly zero. -/
example (N : Superop A B) (n : ℕ) : secondOrderCorrection N (1/2) n = 0 := by
  simp [secondOrderCorrection]

/-- Sanity: no inaccessible output-flag coherence is introduced by erasure. -/
example (X : Matrix A A ℂ) (a : A) : symmetricErasure A X (some a) none = 0 := by
  rfl

/-- Sanity: the erasure flag carries half the actual input trace. -/
example (X : Matrix A A ℂ) : symmetricErasure A X none none = (1/2 : ℂ) * X.trace := by
  rfl

/-- Sanity: zero CP output has zero collision quadratic form, even at singular sigma. -/
example {I : Type} [Fintype I] [DecidableEq I] (sigma : Matrix I I ℂ) :
    collisionExponential 0 sigma = 0 := by
  simp [collisionExponential]

/-- Sanity: register order in the input purification is second-factor input. -/
example (rho : Matrix A A ℂ) (r a s b : A) :
    pureDensity (densityPurification rho) (r,a) (s,b) =
      cfc Real.sqrt rho a r * conj (cfc Real.sqrt rho b s) := by
  rfl

/-- Sanity: a singleton marginal is the projector of the same supplied vector. -/
example (psi : EuclideanSpace ℂ (Unit × Unit × Unit)) :
    marginalAB (pureDensity psi) ((),()) ((),()) = psi ((),(),()) * conj (psi ((),(),())) := by
  simp [marginalAB, pureDensity]

end QAlgorithms.Papers.Independent.Bridge50.P38


