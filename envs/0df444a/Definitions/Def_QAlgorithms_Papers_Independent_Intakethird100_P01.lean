-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P01
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P01
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T03:43:32.312486+00:00
-- url     : https://prove2.me/theorems/e8ecc912-f206-4502-8f2d-f0e888967cb8
-- title:
--   Definitions for Tight Finite-Key Analysis for Quantum Cryptography
-- statement:
--   The objects the formalized statements of *Tight Finite-Key Analysis for Quantum Cryptography* (arXiv:1103.4130) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `StringPair`: PDF p.13: a pair of total classical strings, with no independence assumption on their bits.
--   - `Sample`: PDF p.13: the possible samples, exactly the k-element subsets of n+k positions.
--   - `SamplingOutcome`: PDF p.13: the original strings and the independently drawn sample.
--   - `samplingWeight`: PDF p.13: product of the input string law and the uniform law on k-subsets.
--   - `subsetEventProbability`: PDF p.13: event probability in the product experiment; validity requires P>=0 and sum P=1.
--   - `sampleError`: PDF p.13: relative Hamming distance on the test sample (used only with k>0).
--   - `complementErrorFraction`: PDF p.13: relative Hamming distance on the complementary key positions (used with n>0).
--   - `complementaryString`: PDF p.13: the complementary n positions, in their original increasing order.
--   - `passProbability`: PDF p.13: passing parameter estimation means sample error at most Q_tol.
--   - `probabilityGivenPass`: PDF p.13, (S11)--(S14): normalized conditional probability; the theorems require positive pass probability.
--   - `keyLawGivenPass`: PDF pp.13--14, (S15): the conditioned marginal of the two key strings; Lambda is marginalized.
--   - `samplingFailureParameter`: PDF p.13, (S13)--(S14): epsilon as a function of the nonnegative deviation mu.
--   - `samplingDeviation`: PDF p.13, (S15): deviation with the paper's finite-population correction and natural logarithm.
--   - `truncatedBinaryEntropy`: PDF p.12 footnote 1: binary entropy in bits, truncated to one above one half. The theorem only evaluates this function at nonnegative arguments.
--   - `logTwoExtended`: Extended logarithm for nonnegative fidelity squares: zero has value minus infinity. This elementary helper is retained with its sanity example; entropy itself is imported.
--   - `classicalDensity`: PDF p.13: embed the actual classical joint law as a diagonal density operator.
--   - `singletKet`: PDF pp.9,11: accepted normalized singlet ket, with Bool coordinates relabeled false=0 and true=1. The emitted system is the second tensor factor.
--   - `singletMeasurementVector`: PDF pp.9,11: the measurement vector (conj b,-conj a) that remotely prepares (a,b) from the singlet. The choice explicitly includes the singlet's conjugation and sign.
--   - `preparationEffect`: PDF pp.9,11: rank-one effect on the measured half, constructed from a preparation basis.
--   - `singletContraction`: PDF pp.9,11: unnormalized emitted vector after the rank-one measurement outcome v.
--   - `remoteBranch`: PDF pp.9,11: the emitted branch density; its trace is the Born probability of the outcome.
--   - `RealizesUniformQubitBasis`: PDF pp.3,9,11: the constructed projective measurement is complete and gives each outcome probability 1/2, with conditional emitted density equal to the desired preparation density.
--   - `fourMaximum`: PDF pp.3--4: finite maximum over the four pairs of binary outcomes.
--   - `preparationOverlap`: PDF p.3: maximum squared inner-product overlap of the two preparation bases.
--   - `preparationMeasurementOverlap`: PDF pp.4,9,11: maximum squared L2 operator norm of the products of square-root effects. This uses the frozen operator norm, rather than the matrix entrywise norm.
-- source:
--   Tight Finite-Key Analysis for Quantum Cryptography, arXiv:1103.4130v2, https://arxiv.org/abs/1103.4130v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14

/-!
# Tight Finite-Key Analysis for Quantum Cryptography

arXiv:1103.4130v2. Independent statistical statements and the local qubit-source reduction.
Operational protocol nodes deferred in the accompanying HARD.md are deliberately absent.
New paper-specific constructions are local; matching frozen primitives are imported. Compilation is pending the mechanical handoff.
-/

namespace QAlgorithms.Papers.Independent.Intakethird100.P01

open scoped BigOperators ComplexConjugate ComplexOrder

-- Accepted extended entropy: the finite-real smoothing helper excludes radius >= 1.
open QAlgorithms.Papers.Independent.Information100.P67
  (IsSubnormalized purifiedDistance conditionalMaxEntropy smoothConditionalMaxEntropyExtended)

noncomputable section

/-- PDF p.13: a pair of total classical strings, with no independence assumption on their bits. -/
abbrev StringPair (N : ℕ) := Qubits N × Qubits N

/-- PDF p.13: the possible samples, exactly the k-element subsets of n+k positions. -/
abbrev Sample (n k : ℕ) := {s : Finset (Fin (n + k)) // s.card = k}

/-- PDF p.13: the original strings and the independently drawn sample. -/
abbrev SamplingOutcome (n k : ℕ) := StringPair (n + k) × Sample n k

/-- PDF p.13: product of the input string law and the uniform law on k-subsets. -/
def samplingWeight {n k : ℕ} (P : StringPair (n + k) → ℝ)
    (w : SamplingOutcome n k) : ℝ :=
  P w.1 / (Fintype.card (Sample n k) : ℝ)

/-- PDF p.13: event probability in the product experiment; validity requires P>=0 and sum P=1. -/
def subsetEventProbability {n k : ℕ} (P : StringPair (n + k) → ℝ)
    (event : SamplingOutcome n k → Prop) : ℝ := by
  classical
  exact ∑ w, if event w then samplingWeight P w else 0

/-- PDF p.13: relative Hamming distance on the test sample (used only with k>0). -/
def sampleError {n k : ℕ} (w : SamplingOutcome n k) : ℝ :=
  ((w.2.val.filter (fun i => w.1.1 i ≠ w.1.2 i)).card : ℝ) / (k : ℝ)

/-- PDF p.13: relative Hamming distance on the complementary key positions (used with n>0). -/
def complementErrorFraction {n k : ℕ} (w : SamplingOutcome n k) : ℝ :=
  (((w.2.valᶜ).filter (fun i => w.1.1 i ≠ w.1.2 i)).card : ℝ) / (n : ℝ)

/-- PDF p.13: the complementary n positions, in their original increasing order. -/
def complementaryString {n k : ℕ} (s : Sample n k) (z : Qubits (n + k)) : Qubits n :=
  fun i => z ((s.valᶜ).orderEmbOfFin (by
    rw [Finset.card_compl, Fintype.card_fin, s.property]
    omega) i)

/-- PDF p.13: passing parameter estimation means sample error at most Q_tol. -/
def passProbability {n k : ℕ} (P : StringPair (n + k) → ℝ) (Q : ℝ) : ℝ :=
  subsetEventProbability P (fun w => sampleError w ≤ Q)

/-- PDF p.13, (S11)--(S14): normalized conditional probability; the theorems require positive pass probability. -/
def probabilityGivenPass {n k : ℕ} (P : StringPair (n + k) → ℝ) (Q : ℝ)
    (event : SamplingOutcome n k → Prop) : ℝ :=
  subsetEventProbability P (fun w => sampleError w ≤ Q ∧ event w) / passProbability P Q

/-- PDF pp.13--14, (S15): the conditioned marginal of the two key strings; Lambda is marginalized. -/
def keyLawGivenPass {n k : ℕ} (P : StringPair (n + k) → ℝ) (Q : ℝ)
    (z : StringPair n) : ℝ :=
  probabilityGivenPass P Q (fun w =>
    (complementaryString w.2 w.1.1, complementaryString w.2 w.1.2) = z)

/-- PDF p.13, (S13)--(S14): epsilon as a function of the nonnegative deviation mu. -/
def samplingFailureParameter (n k : ℕ) (mu : ℝ) : ℝ :=
  Real.exp (-(((k : ℝ) * (n : ℝ)) / ((n : ℝ) + (k : ℝ))) *
    ((k : ℝ) / ((k : ℝ) + 1)) * mu ^ 2)

/-- PDF p.13, (S15): deviation with the paper's finite-population correction and natural logarithm. -/
def samplingDeviation (n k : ℕ) (epsilon : ℝ) : ℝ :=
  Real.sqrt ((((n : ℝ) + (k : ℝ)) / ((n : ℝ) * (k : ℝ))) *
    (((k : ℝ) + 1) / (k : ℝ)) * Real.log (1 / epsilon))

/-- PDF p.12 footnote 1: binary entropy in bits, truncated to one above one half.
The theorem only evaluates this function at nonnegative arguments. -/
def truncatedBinaryEntropy (t : ℝ) : ℝ :=
  if t ≤ 1 / 2 then binEntropy2 t else 1

/-- Extended logarithm for nonnegative fidelity squares: zero has value minus infinity.
This elementary helper is retained with its sanity example; entropy itself is imported. -/
def logTwoExtended (x : ℝ) : EReal :=
  if x ≤ 0 then ⊥ else (Real.logb 2 x : EReal)

/-- PDF p.13: embed the actual classical joint law as a diagonal density operator. -/
def classicalDensity {I : Type*} [DecidableEq I] (P : I → ℝ) : Matrix I I ℂ :=
  Matrix.diagonal (fun i => (P i : ℂ))

/-- PDF pp.9,11: accepted normalized singlet ket, with Bool coordinates relabeled
false=0 and true=1. The emitted system is the second tensor factor. -/
def singletKet : EuclideanSpace ℂ (Bool × Bool) :=
  WithLp.toLp 2 (fun p => QAlgorithms.Papers.Independent.Frontier18.P14.singlet
    (if p.1 then 1 else 0, if p.2 then 1 else 0))

/-- PDF pp.9,11: the measurement vector (conj b,-conj a) that remotely prepares (a,b)
from the singlet. The choice explicitly includes the singlet's conjugation and sign. -/
def singletMeasurementVector (psi : EuclideanSpace ℂ Bool) : EuclideanSpace ℂ Bool :=
  WithLp.toLp 2 (fun b => if b then -conj (psi false) else conj (psi true))

/-- PDF pp.9,11: rank-one effect on the measured half, constructed from a preparation basis. -/
def preparationEffect (B : Bool → EuclideanSpace ℂ Bool) (x : Bool) : Matrix Bool Bool ℂ :=
  pureDensity (singletMeasurementVector (B x))

/-- PDF pp.9,11: unnormalized emitted vector after the rank-one measurement outcome v. -/
def singletContraction (v : EuclideanSpace ℂ Bool) : EuclideanSpace ℂ Bool :=
  WithLp.toLp 2 (fun j => ∑ i : Bool, conj (v i) * singletKet (i, j))

/-- PDF pp.9,11: the emitted branch density; its trace is the Born probability of the outcome. -/
def remoteBranch (B : Bool → EuclideanSpace ℂ Bool) (x : Bool) : Matrix Bool Bool ℂ :=
  pureDensity (singletContraction (singletMeasurementVector (B x)))

/-- PDF pp.3,9,11: the constructed projective measurement is complete and gives each outcome
probability 1/2, with conditional emitted density equal to the desired preparation density. -/
def RealizesUniformQubitBasis (B : Bool → EuclideanSpace ℂ Bool) : Prop :=
  Orthonormal ℂ (fun x => singletMeasurementVector (B x)) ∧
    (∑ x : Bool, preparationEffect B x) = 1 ∧
    ∀ x : Bool, (preparationEffect B x).PosSemidef ∧
      preparationEffect B x * preparationEffect B x = preparationEffect B x ∧
      (remoteBranch B x).trace = (1 / 2 : ℂ) ∧
      (2 : ℂ) • remoteBranch B x = pureDensity (B x)

/-- PDF pp.3--4: finite maximum over the four pairs of binary outcomes. -/
def fourMaximum (f : Bool → Bool → ℝ) : ℝ :=
  max (max (f false false) (f false true)) (max (f true false) (f true true))

/-- PDF p.3: maximum squared inner-product overlap of the two preparation bases. -/
def preparationOverlap (X Z : Bool → EuclideanSpace ℂ Bool) : ℝ :=
  fourMaximum (fun x z => ‖inner ℂ (X x) (Z z)‖ ^ 2)

/-- PDF pp.4,9,11: maximum squared L2 operator norm of the products of square-root effects.
This uses the frozen operator norm, rather than the matrix entrywise norm. -/
def preparationMeasurementOverlap (X Z : Bool → EuclideanSpace ℂ Bool) : ℝ :=
  fourMaximum (fun x z =>
    specNorm (cfc Real.sqrt (preparationEffect X x) *
      cfc Real.sqrt (preparationEffect Z z)) ^ 2)

/-- Definition sanity: no deviation remains at epsilon=1. -/
example (n k : ℕ) : samplingDeviation n k 1 = 0 := by
  simp [samplingDeviation]

/-- Definition sanity: the tail parameter at zero deviation is exactly one. -/
example (n k : ℕ) : samplingFailureParameter n k 0 = 1 := by
  simp [samplingFailureParameter]

/-- Definition sanity: the entropy cap is one at error fraction one. -/
example : truncatedBinaryEntropy 1 = 1 := by
  norm_num [truncatedBinaryEntropy]

/-- Definition sanity: zero fidelity has extended logarithm minus infinity. -/
example : logTwoExtended 0 = ⊥ := by
  simp [logTwoExtended]

/-- Definition sanity: the classical embedding uses precisely the given diagonal weights. -/
example {I : Type*} [DecidableEq I] (P : I → ℝ) (i : I) :
    classicalDensity P i i = (P i : ℂ) := by
  simp [classicalDensity]

/-- Definition sanity: the singlet has no amplitude on |00>. -/
example : singletKet (false, false) = 0 := by
  simp [singletKet, QAlgorithms.Papers.Independent.Frontier18.P14.singlet]

/-- Definition sanity: the first measurement coordinate is conj b. -/
example (psi : EuclideanSpace ℂ Bool) :
    singletMeasurementVector psi false = conj (psi true) := rfl

/-- Definition sanity: the second measurement coordinate is -conj a. -/
example (psi : EuclideanSpace ℂ Bool) :
    singletMeasurementVector psi true = -conj (psi false) := rfl

end

end QAlgorithms.Papers.Independent.Intakethird100.P01


