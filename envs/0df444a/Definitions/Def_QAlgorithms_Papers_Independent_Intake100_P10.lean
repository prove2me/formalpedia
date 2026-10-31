-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P10
-- name    : QAlgorithms_Papers_Independent_Intake100_P10
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T12:51:18.062094+00:00
-- url     : https://prove2.me/theorems/4713a890-3171-4208-abca-fcf7cde5b3f0
-- title:
--   Definitions for Conditional Mutual Information and Quantum Steering
-- statement:
--   The objects the formalized statements of *Conditional Mutual Information and Quantum Steering* (arXiv:1612.03875) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `AssemblageCoefficients`: PDF p.2, (3): raw subnormalized operator coefficients, with input first. Validity is imposed separately by IsAssemblage in every general result. This coefficient array is distinct from Complexity.Family, a circuit family.
--   - `IsAssemblage`: PDF p.2, (3)--(5): positive nuclear blocks, normalized common total state. No bipartite realization or nonzero-block premise is required.
--   - `HasCoefficientLHS`: PDF p.2, (7): one shared law and normalized Bob states, independent of x. PMFs allow every discrete hidden-variable alphabet; zero weights are allowed. Unlike Advance50.P47.Assemblage.HasLHS, this predicate consumes coefficient arrays rather than HilbertBasis-indexed bounded operators.
--   - `Extension`: PDF p.4, (16)--(17): every positive trace-class BE extension with the actual E partial trace and no-signaling at ALL x, including zero-law inputs.
--   - `cmiBits`: PDF p.2, (1): extended QCMI in BITS. Only finite PMF masses are converted to reals elsewhere. The denominator is log(2) in nats, and is strictly positive.
--   - `cqCoefficients`: PDF p.4, (16): coefficient embedding of the cq state, ordered XA : B : E. Zero assemblage blocks and zero input masses remain zero without normalization.
--   - `restrictedSteerability`: PDF p.4, (18): supremum of input laws, then infimum over ALL Eve systems and admissible extensions. Extended infima avoid empty/unbounded real defaults; for valid assemblages trivial extensions exist, and (22) supplies finite bounds when Bob is finite dimensional. No infimum is asserted to be attained.
--   - `DiscreteTraceClassInstrument`: PDF p.3, (8)--(9): a discrete quantum instrument. Each branch is CP and trace nonincreasing on the full trace class; its actual sum is a TP channel. Output Bf and outcome Y are unrestricted types, not fixed matrix dimensions. The positive trace-class branch sum converges absolutely on valid inputs. The frozen finite Kraus/vector Instruments have narrower system domains.
--   - `ProcessedExtension`: PDF p.3, (11)--(13): instrument-dependent extensions. The instrument is fixed before the input; Eve may choose a new extension after that strategy. Constraints are imposed for every x and y, including probability-zero events.
--   - `processedCoefficients`: PDF p.3, (11): coefficient embedding ordered XA : Bf : EY. Bob's outcome is classical, whereas arbitrary off-diagonal BE coefficients are kept.
--   - `intrinsicSteerability`: PDF p.3, (14): exactly sup_strategy inf_extension, including optimization over every output system and outcome alphabet. The instrument and Alice's conditional input channel precede Eve's system and extension.
--   - `branchMass`: PDF p.7, (74): actual branch probability, independent of the selected x on an assemblage. A representative x is used only to name its common total.
--   - `branchTransform`: PDF p.7, (73): normalized branch assemblage. Used only at p(z)>0; the division missing in the proof's (77) is retained, as in (73),(74),(85).
--   - `restrictedTransform`: PDF p.12, (139)--(140): input channel is independent of z, and Bob's outcome is summed OUT. This is the deterministic restricted operation.
--   - `IntrinsicAverageMonotonicity`: PDF p.7, (75): full monotonicity on average. Zero branches are omitted and every positive branch uses its computed, normalized output.
--   - `RestrictedDeterministicMonotonicity`: PDF p.12, (141): deterministic restricted monotonicity; there is no claim about the average of restricted steerabilities of retained branches.
--   - `IntrinsicLHSVanishing`: PDF p.7, Proposition 7: only the forward LHS implication.
--   - `RestrictedLHSVanishing`: PDF p.12, Proposition 12: no converse faithfulness assertion.
--   - `IntrinsicConvexity`: PDF p.9, (99)--(101): convexity with both endpoints included.
--   - `RestrictedConvexity`: PDF p.13, (160)--(161): restricted convexity with both endpoints included.
--   - `bb84Ket`: PDF pp.4--5, (24)--(29): x=false is Z, x=true is X; a=true is outcome 1.
--   - `bb84Assemblage`: PDF pp.4--5, (24)--(29): the FOUR constructed blocks, each of trace 1/2.
--   - `steeredFourierKet`: PDF p.6, (46),(51): the steered ket has NEGATIVE Fourier exponent. The positive-exponent ket in (46) is Alice's measurement vector.
--   - `schmidtFourierAssemblage`: PDF p.6, (47): Schmidt/Fourier assemblage; x=false is the Schmidt basis. The Fourier block carries 1/d, not 1/sqrt(d), because it is an outer product.
--   - `schmidtEntropyBits`: PDF pp.6--7, (48),(66): Shannon entropy of the Schmidt weights in bits. Real.log 0=0 implements the continuous convention 0 log 0=0.
--   - `GroupedNoSignaling`: PDF pp.10,13,15: additional no-signaling for the FULL Bob operator. This is not a constraint on Eve extensions and is not a product premise.
--   - `firstGrouped`: PDF pp.10,13,15: first grouped marginal, computed by discarding outcome 2. The representative input 2 has no effect under GroupedNoSignaling.
--   - `secondGrouped`: PDF pp.10,13,15: second grouped marginal, computed by discarding outcome 1.
--   - `firstReduced`: PDF pp.10,13: the first local assemblage uses the actual B2 partial trace.
--   - `secondReduced`: PDF pp.10,13: the second local assemblage uses the actual B1 partial trace.
--   - `productFamily`: PDF p.14, (165): constructed tensor product of two assemblages.
--   - `processedOutcomeCoefficients`: PDF p.3, (15): move the classical input into the conditioning system; the resulting order is A : Bf : E(XY).
--   - `processedInputCoefficients`: PDF p.3 before (15): trace out A, ordered X : Bf : EY.
--   - `outcomeCoefficients`: PDF p.4, (19): same reordering without Bob's instrument outcome.
--   - `inputCoefficients`: PDF p.4 before (19): trace out A, ordered X : B : E.
-- source:
--   Conditional Mutual Information and Quantum Steering, arXiv:1612.03875v2, https://arxiv.org/abs/1612.03875v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P19

/-!
# Conditional Mutual Information and Quantum Steering

Kaur, Wang and Wilde, arXiv:1612.03875v2. Page numbers are PDF pages.
All new definitions are local to this paper. The rank-one outer product and
binary operator mixture are imported from the frozen accepted library.
Arbitrary orthonormal-coordinate labels represent completed Hilbert spaces, with nuclear trace-class blocks.
Actual partial traces and extended QCMI are reused from the accepted library.
Information is in bits, without a factor 1/2. No entropy subtraction at infinity
or conversion of an infinite information value to a real is used.

Definitions 1 and 3 use precisely the grouped no-signaling convention printed
in (13) and (17). The multipartite claims retain the printed Bob-marginal
hypotheses; the proof's stronger BE-marginal convention requires independent
moderation. Equation (197) is deferred, not assigned a new interpretation.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P10

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel productCoeff)
open QAlgorithms.Papers.Independent.Frontier18.P08
  (PositiveTraceClass operatorTrace partialTraceFirst partialTraceSecond IsQuantumOperation)
open QAlgorithms.Papers.Independent.Renew46.P08 (qcmi)
open QAlgorithms.Papers.Independent.Frontier18.P01 (convexOperatorMixture)
open QAlgorithms.Papers.Independent.Information100.P19 (outer)

/-- PDF p.2, (3): raw subnormalized operator coefficients, with input first.
Validity is imposed separately by IsAssemblage in every general result.
This coefficient array is distinct from Complexity.Family, a circuit family. -/
abbrev AssemblageCoefficients (X A B : Type) := X → A → Matrix B B ℂ

/-- PDF p.2, (3)--(5): positive nuclear blocks, normalized common total state.
No bipartite realization or nonzero-block premise is required. -/
def IsAssemblage {X A B : Type} [Fintype A] (rho : AssemblageCoefficients X A B) : Prop :=
  (∀ x a, PositiveTraceClass (rho x a)) ∧
  (∀ x, operatorTrace (∑ a, rho x a) = 1) ∧
  ∀ x z, ∑ a, rho x a = ∑ a, rho z a

/-- PDF p.2, (7): one shared law and normalized Bob states, independent of x.
PMFs allow every discrete hidden-variable alphabet; zero weights are allowed.
Unlike Advance50.P47.Assemblage.HasLHS, this predicate consumes coefficient
arrays rather than HilbertBasis-indexed bounded operators. -/
def HasCoefficientLHS {X A B : Type} (rho : AssemblageCoefficients X A B) : Prop :=
  ∃ (L : Type) (mu : PMF L) (sigma : L → State B) (response : L → X → PMF A),
    ∀ x a i j, rho x a i j = ∑' l,
      (((mu l).toReal * (response l x a).toReal : ℝ) : ℂ) *
        (sigma l).coefficients i j

/-- PDF p.4, (16)--(17): every positive trace-class BE extension with the
actual E partial trace and no-signaling at ALL x, including zero-law inputs. -/
structure Extension {X A B : Type} [Fintype A] (rho : AssemblageCoefficients X A B) (E : Type) where
  block : AssemblageCoefficients X A (B × E)
  positive : ∀ x a, PositiveTraceClass (block x a)
  marginal : ∀ x a, partialTraceSecond (block x a) = rho x a
  noSignaling : ∀ x z, ∑ a, block x a = ∑ a, block z a

/-- PDF p.2, (1): extended QCMI in BITS. Only finite PMF masses are converted
to reals elsewhere. The denominator is log(2) in nats, and is strictly positive. -/
def cmiBits {I J K : Type} (rho : Matrix (I × (J × K)) (I × (J × K)) ℂ) : ℝ≥0∞ :=
  qcmi rho / ENNReal.ofReal (Real.log 2)

/-- PDF p.4, (16): coefficient embedding of the cq state, ordered XA : B : E.
Zero assemblage blocks and zero input masses remain zero without normalization. -/
def cqCoefficients {X A B E : Type} (p : PMF X) (r : AssemblageCoefficients X A (B × E)) :
    Matrix ((X × A) × (B × E)) ((X × A) × (B × E)) ℂ :=
  fun i j => if i.1 = j.1 then ((p i.1.1).toReal : ℂ) * r i.1.1 i.1.2 i.2 j.2 else 0

/-- PDF p.4, (18): supremum of input laws, then infimum over ALL Eve systems
and admissible extensions. Extended infima avoid empty/unbounded real defaults;
for valid assemblages trivial extensions exist, and (22) supplies finite bounds
when Bob is finite dimensional. No infimum is asserted to be attained. -/
def restrictedSteerability {X A B : Type} [Fintype X] [Fintype A]
    (rho : AssemblageCoefficients X A B) : ℝ≥0∞ :=
  ⨆ p : PMF X, ⨅ (E : Type) (r : Extension rho E), cmiBits (cqCoefficients p r.block)

/-- PDF p.3, (8)--(9): a discrete quantum instrument. Each branch is CP and
trace nonincreasing on the full trace class; its actual sum is a TP channel.
Output Bf and outcome Y are unrestricted types, not fixed matrix dimensions.
The positive trace-class branch sum converges absolutely on valid inputs.
The frozen finite Kraus/vector Instruments have narrower system domains. -/
structure DiscreteTraceClassInstrument (B Bf Y : Type) where
  branch : Y → Matrix B B ℂ → Matrix Bf Bf ℂ
  operation : ∀ y, IsQuantumOperation (branch y)
  summableTrace : ∀ t, PositiveTraceClass t → Summable (fun y => operatorTrace (branch y t))
  totalChannel : IsTraceClassChannel (fun t i j => ∑' y, branch y t i j)

/-- PDF p.3, (11)--(13): instrument-dependent extensions. The instrument is
fixed before the input; Eve may choose a new extension after that strategy.
Constraints are imposed for every x and y, including probability-zero events. -/
structure ProcessedExtension {X A B Bf Y : Type} [Fintype A]
    (rho : AssemblageCoefficients X A B) (K : DiscreteTraceClassInstrument B Bf Y) (E : Type) where
  block : Y → AssemblageCoefficients X A (Bf × E)
  positive : ∀ y x a, PositiveTraceClass (block y x a)
  marginal : ∀ y x a, partialTraceSecond (block y x a) = K.branch y (rho x a)
  noSignaling : ∀ y x z, ∑ a, block y x a = ∑ a, block y z a

/-- PDF p.3, (11): coefficient embedding ordered XA : Bf : EY. Bob's
outcome is classical, whereas arbitrary off-diagonal BE coefficients are kept. -/
def processedCoefficients {X A Bf Y E : Type} (p : Y → PMF X)
    (r : Y → AssemblageCoefficients X A (Bf × E)) :
    Matrix ((X × A) × (Bf × (E × Y))) ((X × A) × (Bf × (E × Y))) ℂ :=
  fun i j => if i.1 = j.1 ∧ i.2.2.2 = j.2.2.2 then
    ((p i.2.2.2 i.1.1).toReal : ℂ) *
      r i.2.2.2 i.1.1 i.1.2 (i.2.1, i.2.2.1) (j.2.1, j.2.2.1) else 0

/-- PDF p.3, (14): exactly sup_strategy inf_extension, including optimization
over every output system and outcome alphabet. The instrument and Alice's
conditional input channel precede Eve's system and extension. -/
def intrinsicSteerability {X A B : Type} [Fintype X] [Fintype A]
    (rho : AssemblageCoefficients X A B) : ℝ≥0∞ :=
  ⨆ (Bf : Type) (Y : Type) (K : DiscreteTraceClassInstrument B Bf Y) (p : Y → PMF X),
    ⨅ (E : Type) (r : ProcessedExtension rho K E),
      cmiBits (processedCoefficients p r.block)

/-- PDF p.7, (74): actual branch probability, independent of the selected x
on an assemblage. A representative x is used only to name its common total. -/
def branchMass {X A B Bf Z : Type} [Fintype A] [Nonempty X]
    (rho : AssemblageCoefficients X A B) (K : DiscreteTraceClassInstrument B Bf Z) (z : Z) : ℝ :=
  operatorTrace (K.branch z (∑ a, rho (Classical.choice (inferInstance : Nonempty X)) a))

/-- PDF p.7, (73): normalized branch assemblage. Used only at p(z)>0;
the division missing in the proof's (77) is retained, as in (73),(74),(85). -/
def branchTransform {X A B Bf Z Xf Af : Type} [Fintype X] [Fintype A] [Nonempty X]
    (rho : AssemblageCoefficients X A B) (K : DiscreteTraceClassInstrument B Bf Z)
    (input : Z → Xf → PMF X) (output : Z → Xf → X → A → PMF Af) (z : Z) :
    AssemblageCoefficients Xf Af Bf :=
  fun xf af => ((branchMass rho K z : ℂ)⁻¹) •
    ∑ x, ∑ a, ((((input z xf x).toReal * (output z xf x a af).toReal : ℝ) : ℂ) •
      K.branch z (rho x a))

/-- PDF p.12, (139)--(140): input channel is independent of z, and Bob's
outcome is summed OUT. This is the deterministic restricted operation. -/
def restrictedTransform {X A B Bf Z Xf Af : Type} [Fintype X] [Fintype A]
    (rho : AssemblageCoefficients X A B) (K : DiscreteTraceClassInstrument B Bf Z)
    (input : Xf → PMF X) (output : Z → Xf → X → A → PMF Af) : AssemblageCoefficients Xf Af Bf :=
  fun xf af i j => ∑' z, ∑ x, ∑ a,
    (((input xf x).toReal * (output z xf x a af).toReal : ℝ) : ℂ) * K.branch z (rho x a) i j

/-- PDF p.7, (75): full monotonicity on average. Zero branches are omitted
and every positive branch uses its computed, normalized output. -/
def IntrinsicAverageMonotonicity : Prop :=
  ∀ (X A B Bf Z Xf Af : Type) [Fintype X] [Fintype A] [Fintype Xf] [Fintype Af]
    [Nonempty X] [Nonempty A] [Nonempty Xf] [Nonempty Af]
    (rho : AssemblageCoefficients X A B), IsAssemblage rho →
    ∀ (K : DiscreteTraceClassInstrument B Bf Z) (input : Z → Xf → PMF X)
      (output : Z → Xf → X → A → PMF Af),
      (∑' z : {z : Z // 0 < branchMass rho K z},
        ENNReal.ofReal (branchMass rho K z.val) *
          intrinsicSteerability (branchTransform rho K input output z.val)) ≤
        intrinsicSteerability rho

/-- PDF p.12, (141): deterministic restricted monotonicity; there is no
claim about the average of restricted steerabilities of retained branches. -/
def RestrictedDeterministicMonotonicity : Prop :=
  ∀ (X A B Bf Z Xf Af : Type) [Fintype X] [Fintype A] [Fintype Xf] [Fintype Af]
    [Nonempty X] [Nonempty A] [Nonempty Xf] [Nonempty Af]
    (rho : AssemblageCoefficients X A B), IsAssemblage rho →
    ∀ (K : DiscreteTraceClassInstrument B Bf Z) (input : Xf → PMF X)
      (output : Z → Xf → X → A → PMF Af),
      restrictedSteerability (restrictedTransform rho K input output) ≤ restrictedSteerability rho

/-- PDF p.7, Proposition 7: only the forward LHS implication. -/
def IntrinsicLHSVanishing : Prop :=
  ∀ (X A B : Type) [Fintype X] [Fintype A] [Nonempty X] [Nonempty A]
    (rho : AssemblageCoefficients X A B), IsAssemblage rho → HasCoefficientLHS rho → intrinsicSteerability rho = 0

/-- PDF p.12, Proposition 12: no converse faithfulness assertion. -/
def RestrictedLHSVanishing : Prop :=
  ∀ (X A B : Type) [Fintype X] [Fintype A] [Nonempty X] [Nonempty A]
    (rho : AssemblageCoefficients X A B), IsAssemblage rho → HasCoefficientLHS rho → restrictedSteerability rho = 0

/-- PDF p.9, (99)--(101): convexity with both endpoints included. -/
def IntrinsicConvexity : Prop :=
  ∀ (X A B : Type) [Fintype X] [Fintype A] [Nonempty X] [Nonempty A]
    (rho sigma : AssemblageCoefficients X A B), IsAssemblage rho → IsAssemblage sigma →
    ∀ lambda : ℝ, 0 ≤ lambda → lambda ≤ 1 →
      intrinsicSteerability (fun x a => convexOperatorMixture lambda (rho x a) (sigma x a)) ≤
        ENNReal.ofReal lambda * intrinsicSteerability rho +
          ENNReal.ofReal (1 - lambda) * intrinsicSteerability sigma

/-- PDF p.13, (160)--(161): restricted convexity with both endpoints included. -/
def RestrictedConvexity : Prop :=
  ∀ (X A B : Type) [Fintype X] [Fintype A] [Nonempty X] [Nonempty A]
    (rho sigma : AssemblageCoefficients X A B), IsAssemblage rho → IsAssemblage sigma →
    ∀ lambda : ℝ, 0 ≤ lambda → lambda ≤ 1 →
      restrictedSteerability (fun x a => convexOperatorMixture lambda (rho x a) (sigma x a)) ≤
        ENNReal.ofReal lambda * restrictedSteerability rho +
          ENNReal.ofReal (1 - lambda) * restrictedSteerability sigma

/-- PDF pp.4--5, (24)--(29): x=false is Z, x=true is X; a=true is outcome 1. -/
def bb84Ket (x a : Bool) (i : Fin 2) : ℂ :=
  if x = false then (if i.val = (if a then 1 else 0) then 1 else 0)
  else if a = true ∧ i.val = 1 then -(1 / (Real.sqrt 2 : ℂ)) else 1 / (Real.sqrt 2 : ℂ)

/-- PDF pp.4--5, (24)--(29): the FOUR constructed blocks, each of trace 1/2. -/
def bb84Assemblage : AssemblageCoefficients Bool Bool (Fin 2) :=
  fun x a => (1 / 2 : ℂ) • outer (bb84Ket x a)

/-- PDF p.6, (46),(51): the steered ket has NEGATIVE Fourier exponent.
The positive-exponent ket in (46) is Alice's measurement vector. -/
def steeredFourierKet {d : ℕ} (alpha : Fin d → ℂ) (a k : Fin d) : ℂ :=
  alpha k * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ) * (k.val : ℂ) / (d : ℂ))

/-- PDF p.6, (47): Schmidt/Fourier assemblage; x=false is the Schmidt basis.
The Fourier block carries 1/d, not 1/sqrt(d), because it is an outer product. -/
def schmidtFourierAssemblage {d : ℕ} (alpha : Fin d → ℂ) : AssemblageCoefficients Bool (Fin d) (Fin d) :=
  fun x a => if x then ((d : ℂ)⁻¹) • outer (steeredFourierKet alpha a)
    else outer (fun k => if k = a then alpha a else 0)

/-- PDF pp.6--7, (48),(66): Shannon entropy of the Schmidt weights in bits.
Real.log 0=0 implements the continuous convention 0 log 0=0. -/
def schmidtEntropyBits {d : ℕ} (alpha : Fin d → ℂ) : ℝ :=
  -(∑ j, Complex.normSq (alpha j) * Real.log (Complex.normSq (alpha j))) / Real.log 2

/-- PDF pp.10,13,15: additional no-signaling for the FULL Bob operator.
This is not a constraint on Eve extensions and is not a product premise. -/
def GroupedNoSignaling {X1 X2 A1 A2 B : Type} [Fintype A1] [Fintype A2]
    (rho : AssemblageCoefficients (X1 × X2) (A1 × A2) B) : Prop :=
  (∀ x1 x2 z2 a1, ∑ a2, rho (x1, x2) (a1, a2) = ∑ a2, rho (x1, z2) (a1, a2)) ∧
  (∀ x1 z1 x2 a2, ∑ a1, rho (x1, x2) (a1, a2) = ∑ a1, rho (z1, x2) (a1, a2))

/-- PDF pp.10,13,15: first grouped marginal, computed by discarding outcome 2.
The representative input 2 has no effect under GroupedNoSignaling. -/
def firstGrouped {X1 X2 A1 A2 B : Type} [Fintype A2] [Nonempty X2]
    (rho : AssemblageCoefficients (X1 × X2) (A1 × A2) B) : AssemblageCoefficients X1 A1 B :=
  fun x1 a1 => ∑ a2, rho (x1, Classical.choice (inferInstance : Nonempty X2)) (a1, a2)

/-- PDF pp.10,13,15: second grouped marginal, computed by discarding outcome 1. -/
def secondGrouped {X1 X2 A1 A2 B : Type} [Fintype A1] [Nonempty X1]
    (rho : AssemblageCoefficients (X1 × X2) (A1 × A2) B) : AssemblageCoefficients X2 A2 B :=
  fun x2 a2 => ∑ a1, rho (Classical.choice (inferInstance : Nonempty X1), x2) (a1, a2)

/-- PDF pp.10,13: the first local assemblage uses the actual B2 partial trace. -/
def firstReduced {X1 X2 A1 A2 B1 B2 : Type} [Fintype A2] [Nonempty X2]
    (rho : AssemblageCoefficients (X1 × X2) (A1 × A2) (B1 × B2)) : AssemblageCoefficients X1 A1 B1 :=
  fun x a => partialTraceSecond (firstGrouped rho x a)

/-- PDF pp.10,13: the second local assemblage uses the actual B1 partial trace. -/
def secondReduced {X1 X2 A1 A2 B1 B2 : Type} [Fintype A1] [Nonempty X1]
    (rho : AssemblageCoefficients (X1 × X2) (A1 × A2) (B1 × B2)) : AssemblageCoefficients X2 A2 B2 :=
  fun x a => partialTraceFirst (secondGrouped rho x a)

/-- PDF p.14, (165): constructed tensor product of two assemblages. -/
def productFamily {X1 X2 A1 A2 B1 B2 : Type}
    (theta : AssemblageCoefficients X1 A1 B1) (kappa : AssemblageCoefficients X2 A2 B2) :
    AssemblageCoefficients (X1 × X2) (A1 × A2) (B1 × B2) :=
  fun x a => productCoeff (theta x.1 a.1) (kappa x.2 a.2)

/-- PDF p.3, (15): move the classical input into the conditioning system;
the resulting order is A : Bf : E(XY). -/
def processedOutcomeCoefficients {X A Bf Y E : Type} (p : Y → PMF X)
    (r : Y → AssemblageCoefficients X A (Bf × E)) :
    Matrix (A × (Bf × (E × (X × Y)))) (A × (Bf × (E × (X × Y)))) ℂ :=
  fun i j => if i.1 = j.1 ∧ i.2.2.2 = j.2.2.2 then
    ((p i.2.2.2.2 i.2.2.2.1).toReal : ℂ) *
      r i.2.2.2.2 i.2.2.2.1 i.1 (i.2.1, i.2.2.1) (j.2.1, j.2.2.1) else 0

/-- PDF p.3 before (15): trace out A, ordered X : Bf : EY. -/
def processedInputCoefficients {X A Bf Y E : Type} [Fintype A] (p : Y → PMF X)
    (r : Y → AssemblageCoefficients X A (Bf × E)) :
    Matrix (X × (Bf × (E × Y))) (X × (Bf × (E × Y))) ℂ :=
  fun i j => if i.1 = j.1 ∧ i.2.2.2 = j.2.2.2 then
    ((p i.2.2.2 i.1).toReal : ℂ) *
      ∑ a, r i.2.2.2 i.1 a (i.2.1, i.2.2.1) (j.2.1, j.2.2.1) else 0

/-- PDF p.4, (19): same reordering without Bob's instrument outcome. -/
def outcomeCoefficients {X A B E : Type} (p : PMF X) (r : AssemblageCoefficients X A (B × E)) :
    Matrix (A × (B × (E × X))) (A × (B × (E × X))) ℂ :=
  fun i j => if i.1 = j.1 ∧ i.2.2.2 = j.2.2.2 then
    ((p i.2.2.2).toReal : ℂ) * r i.2.2.2 i.1 (i.2.1, i.2.2.1) (j.2.1, j.2.2.1) else 0

/-- PDF p.4 before (19): trace out A, ordered X : B : E. -/
def inputCoefficients {X A B E : Type} [Fintype A] (p : PMF X) (r : AssemblageCoefficients X A (B × E)) :
    Matrix (X × (B × E)) (X × (B × E)) ℂ :=
  fun i j => if i.1 = j.1 then ((p i.1).toReal : ℂ) * ∑ a, r i.1 a i.2 j.2 else 0

/-! Definition sanity checks. No source theorem is proved. -/

example {B : Type} : outer (fun _ : B => 0) = 0 := by
  funext i j
  simp [outer]

example {X A B : Type} (rho sigma : AssemblageCoefficients X A B) : (fun x a => convexOperatorMixture 0 (rho x a) (sigma x a)) = sigma := by
  funext x a
  simp [convexOperatorMixture]

example {X A B : Type} (rho sigma : AssemblageCoefficients X A B) : (fun x a => convexOperatorMixture 1 (rho x a) (sigma x a)) = rho := by
  funext x a
  simp [convexOperatorMixture]

example : bb84Assemblage false false 0 0 = 1 / 2 := by
  simp [bb84Assemblage, bb84Ket, outer]

example : bb84Ket true true 1 = -(1 / (Real.sqrt 2 : ℂ)) := by
  simp [bb84Ket]

example {d : ℕ} (alpha : Fin d → ℂ) (a : Fin d) :
    schmidtFourierAssemblage alpha false a a a = alpha a * star (alpha a) := by
  simp [schmidtFourierAssemblage, outer]

example : ¬ IsAssemblage (fun (_ _ : Unit) => (0 : Matrix Unit Unit ℂ)) := by
  simp [IsAssemblage, operatorTrace]

example {X A B E : Type} (p : PMF X) (r : AssemblageCoefficients X A (B × E))
    (x : X) (a : A) (u v : B × E) :
    cqCoefficients p r ((x, a), u) ((x, a), v) = ((p x).toReal : ℂ) * r x a u v := by
  simp [cqCoefficients]

example {X A B E : Type} (p : PMF X) (r : AssemblageCoefficients X A (B × E))
    (x z : X) (a b : A) (u v : B × E) (h : (x, a) ≠ (z, b)) :
    cqCoefficients p r ((x, a), u) ((z, b), v) = 0 := by
  simp [cqCoefficients, h]

section Multipartite

variable {X1 X2 A1 A2 B1 B2 B : Type}
variable [Fintype X1] [Fintype X2] [Fintype A1] [Fintype A2]
variable [Nonempty X1] [Nonempty X2] [Nonempty A1] [Nonempty A2]

end Multipartite

end QAlgorithms.Papers.Independent.Intake100.P10


