-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P28
-- name    : QAlgorithms_Papers_Independent_Claimed50_P28
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T12:12:54.056557+00:00
-- url     : https://prove2.me/theorems/f285a734-443f-486f-ae4b-b17d6fa191c4
-- title:
--   Definitions for Optimal quantum tomography for states, measurements, and transformations
-- statement:
--   The objects the formalized statements of *Optimal quantum tomography for states, measurements, and transformations* (arXiv:0806.1172) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ChoiBasis`: PDF p.2: equal-dimension output × input register, output first.
--   - `HSMatrix`: PDF p.1, (3)–(5): matrices acting on vectorized operators.
--   - `operatorCoordinates`: PDF p.1, (3): vectorization is row index first, with no conjugation.
--   - `operatorDyad`: PDF p.1, (3)–(5): |A>><<A| on Hilbert–Schmidt operator space.
--   - `hsSquared`: PDF p.2, (21): squared Hilbert–Schmidt norm, not the matrix sup norm.
--   - `representationQuadratic`: PDF p.1, (9): the quadratic form <<A|G|A>>.
--   - `onOperator`: PDF p.1, (6): action of an operator-space matrix on an operator.
--   - `traceInput`: PDF p.2, (12),(31): trace over the input, retaining the output.
--   - `IsOperation`: PDF p.2: CP trace-nonincreasing operations in output-first Choi coordinates. The partial trace inequality permits a missing-probability failure outcome.
--   - `applyWithAncilla`: PDF p.2, (12): the operation tensored with the identity, constructed from its Choi matrix.
--   - `inducedTester`: PDF p.2, (14): setup-induced tester; indices specify all transposes.
--   - `IsTesterDensity`: PDF pp.2–3, (15),(24): integrable positive tester density.
--   - `IsPOVMDensity`: PDF p.2: a physical POVM density, retaining its actual normalization.
--   - `IsTomographyDual`: PDF pp.1–2, (5),(18): a complex-linear unbiased reconstruction dual on the target span.
--   - `TomographyDomain`: PDF p.3, (31): the three target domains.
--   - `physicalTarget`: PDF p.3, (31): the physical affine sets, before taking their complex linear spans.
--   - `tomographyTargetSpan`: PDF p.3, (31)–(32): span, not the affine set or its trace-zero tangent space.
--   - `SU`: PDF p.2: Mathlib special unitary group, not the full unitary group.
--   - `IsProbabilityHaar`: PDF p.2, (24): probability Haar measure, specified by left invariance.
--   - `GroupPair`: PDF pp.2–3: two independent SU(d) Haar variables.
--   - `conjugateTesterSeed`: PDF p.2, (22): conjugation on output × input; U and V are independent.
--   - `covariant`: PDF pp.2–3, (22): covariant density on seed label × SU(d) × SU(d).
--   - `testerSeedOrbit`: PDF pp.3–4: single-seed covariant density.
--   - `maximallyEntangledDensity`: PDF p.2, (24): normalized input density |I>><<I|/d, distinct from the auxiliary pair.
--   - `twirledFrame`: PDF p.3, (27): twirled frame, with zero seeds discarded by the theorem hypotheses.
--   - `frameSupportInverse`: PDF p.3, after (30): Moore–Penrose inverse of a positive Hermitian frame.
--   - `FrameComplete`: PDF p.3: the target must lie in the range of the frame. A zero inverse on an unmeasured target direction is not admissible.
--   - `pairedTensor`: PDF p.4, note [12]: pair wires 1,3 and 2,4 in the natural vec order 1,2,3,4.
--   - `sector`: PDF p.3, (28): the four orthogonal sectors, indexed in printed order.
--   - `targetProjector`: PDF p.3, (32): projectors onto the complex target spans.
--   - `etaIntegrand`: PDF p.1, (10), and p.3 after (30): symmetric-prior loss on the required span. The quadratic form is ||Q_K D||_HS²; irrelevant dual components are not charged. For operations Q_K=I, recovering (21).
--   - `eta`: PDF p.1, (10), p.2, (21), and p.3, (33): target-dependent second-moment term.
--   - `TomographyAdmissible`: PDF pp.2–3: physical tester and finite projected-loss dual on the chosen span.
--   - `coefficientA`: PDF p.3, (29): coefficient A, using the input marginal (trace over wire 2).
--   - `coefficientB`: PDF p.3, (29): coefficient B, using the output marginal (trace over wire 1).
--   - `coefficientC`: PDF p.3, (29): coefficient C.
--   - `Seeds`: PDF p.3, (25): positive nonzero seeds, with total trace d.
--   - `RankOneSeed`: PDF p.3: rank-one positive seed, including its normalized vectorization.
--   - `rankOneLoss`: PDF p.3, (33): rational losses, used only on the explicitly admissible A range.
--   - `optimum`: PDF p.3, (34): attained minima, including the scalar value at d=1.
--   - `optimalBeta`: PDF pp.3–4, (33),(36): channel beta corrected using A=beta²/(d+1). Printed: beta_C=[(d-1)(2+sqrt(2)(d²-1))]^(-1/2). Changed: beta_C=sqrt((d+1)/(2+sqrt(2)(d²-1))). Why: (29),(36) give A=beta²/(d+1), while (33) fixes A=1/(2+sqrt(2)(d²-1)).
--   - `seedMatrix`: PDF p.4, (36): the explicit positive square-root seed matrix.
--   - `optimalSeed`: PDF p.4, (35)–(36): attaining tester seed d|Psi>><<Psi|.
--   - `Attains`: PDF pp.3–4: the attainment assertion, including physical preparation and target completeness.
--   - `bayesEta`: PDF p.1, (9): second moment for arbitrary mean and representation.
--   - `bayesVariance`: PDF pp.1–2, (7),(19): zero-valued estimator on a missing-probability failure.
--   - `BayesianReduction`: PDF pp.1–2, (8)–(10),(20): general prior mean reduction with projected observables.
--   - `BayesianIntegrable`: PDF pp.1–2: integrability assumptions prevent zero-valued undefined Bochner integrals.
--   - `bellMatrix`: PDF p.4, Fig.1: generalized Bell basis matrices (shift and phase), for positive d.
--   - `bellAmplitude`: PDF p.4: raw two-Bell contraction, keeping the auxiliary |Psi>> separate from the Choi input.
--   - `bellEffect`: PDF p.4: each pair of discrete Bell labels has its own physical effect.
--   - `branchEffect`: PDF p.4: one remaining branch, a projective measurement preceded by U.
--   - `branchPOVMProbability`: PDF p.4: normalized remote input for effect/POVM tomography is a uniformly selected projective outcome, followed by the entire unknown POVM.
--   - `branchDual`: Canonical linear dual for the randomized projective frame; no numerical optimum is asserted.
--   - `orbitRepresentation`: PDF p.4 after (37): representation operator for independently Haar-randomized input rho and output observable A. In output-first Choi coordinates the input is transposed.
-- source:
--   Optimal quantum tomography for states, measurements, and transformations, arXiv:0806.1172v1, https://arxiv.org/abs/0806.1172v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

/-!
Statements from Bisio et al., arXiv:0806.1172v1 (PDF pages 1–4).
Accepted matrix and Hilbert–Schmidt definitions are imported; new tomography concepts
are local to this independent paper. Compilation is pending.
The corrected channel seed and unital purity are documented in MODERATION_NOTES.md.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate ComplexOrder Matrix Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Claimed50.P28

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted aliases/pairing; unrelated short-name collisions are not reused.
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)

/-- PDF p.2: equal-dimension output × input register, output first. -/
abbrev ChoiBasis (d : ℕ) := Fin d × Fin d

/-- PDF p.1, (3)–(5): matrices acting on vectorized operators. -/
abbrev HSMatrix (I : Type*) := Op (I × I)

/-- PDF p.1, (3): vectorization is row index first, with no conjugation. -/
def operatorCoordinates {I : Type*} (A : Op I) : I × I → ℂ := fun p => A p.1 p.2

/-- PDF p.1, (3)–(5): |A>><<A| on Hilbert–Schmidt operator space. -/
def operatorDyad {I : Type*} (A : Op I) : HSMatrix I :=
  fun p q => operatorCoordinates A p * conj (operatorCoordinates A q)

/-- PDF p.2, (21): squared Hilbert–Schmidt norm, not the matrix sup norm. -/
def hsSquared {I : Type*} [Fintype I] (A : Op I) : ℝ := (hs A A).re

/-- PDF p.1, (9): the quadratic form <<A|G|A>>. -/
def representationQuadratic {I : Type*} [Fintype I] (G : HSMatrix I) (A : Op I) : ℝ :=
  (∑ p, ∑ q, conj (operatorCoordinates A p) * G p q * operatorCoordinates A q).re

/-- PDF p.1, (6): action of an operator-space matrix on an operator. -/
def onOperator {I : Type*} [Fintype I] (G : HSMatrix I) (A : Op I) : Op I :=
  fun i j => ∑ q, G (i, j) q * A q.1 q.2

/-- PDF p.2, (12),(31): trace over the input, retaining the output. -/
def traceInput {O I : Type*} [Fintype I] (R : Op (O × I)) : Op O :=
  fun x y => ∑ a, R (x, a) (y, a)

/-- PDF p.2: CP trace-nonincreasing operations in output-first Choi coordinates.
The partial trace inequality permits a missing-probability failure outcome. -/
def IsOperation {O I : Type*} [Fintype O] [Fintype I] [DecidableEq I]
    (R : Op (O × I)) : Prop :=
  R.PosSemidef ∧ (1 - QAlgorithms.traceLeft R).PosSemidef

/-- PDF p.2, (12): the operation tensored with the identity, constructed from its Choi matrix. -/
def applyWithAncilla {O I A : Type*} [Fintype I]
    (R : Op (O × I)) (rho : Op (I × A)) : Op (O × A) :=
  fun p q => ∑ a, ∑ b, R (p.1, a) (q.1, b) * rho (a, p.2) (b, q.2)

/-- PDF p.2, (14): setup-induced tester; indices specify all transposes. -/
def inducedTester {O I A : Type*} [Fintype A]
    (rho : Op (I × A)) (P : Op (O × A)) : Op (O × I) :=
  fun p q => ∑ r, ∑ s, rho (q.2, r) (p.2, s) * P (p.1, s) (q.1, r)

/-- PDF pp.2–3, (15),(24): integrable positive tester density. -/
def IsTesterDensity {O I X : Type*} [Fintype O] [Fintype I]
    [DecidableEq O] [MeasurableSpace X] (mu : Measure X) (P : X → Op (O × I)) : Prop :=
  Integrable P mu ∧ (∀ x, (P x).PosSemidef) ∧
    ∃ sigma : Op I, QAlgorithms.IsDensityMatrix sigma ∧
      ∫ x, P x ∂mu = Matrix.kronecker (1 : Op O) sigma

/-- PDF p.2: a physical POVM density, retaining its actual normalization. -/
def IsPOVMDensity {I X : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace X] (mu : Measure X) (P : X → Op I) : Prop :=
  Integrable P mu ∧ (∀ x, (P x).PosSemidef) ∧ ∫ x, P x ∂mu = 1

/-- PDF pp.1–2, (5),(18): a complex-linear unbiased reconstruction dual on the target span. -/
def IsTomographyDual {I X : Type*} [Fintype I] [MeasurableSpace X]
    (mu : Measure X) (P D : X → Op I) (V : Set (Op I)) : Prop :=
  AEStronglyMeasurable D mu ∧ ∀ A ∈ V,
    Integrable (fun x => hs (D x) A • P x) mu ∧ ∫ x, hs (D x) A • P x ∂mu = A

/-- PDF p.3, (31): the three target domains. -/
inductive TomographyDomain where
  | operations
  | channels
  | unital
  deriving DecidableEq

/-- PDF p.3, (31): the physical affine sets, before taking their complex linear spans. -/
def physicalTarget (d : ℕ) : TomographyDomain → Set (Op (ChoiBasis d))
  | .operations => {R | IsOperation R}
  | .channels => {R | R.PosSemidef ∧ QAlgorithms.traceLeft R = 1}
  | .unital => {R | R.PosSemidef ∧ QAlgorithms.traceLeft R = 1 ∧ traceInput R = 1}

/-- PDF p.3, (31)–(32): span, not the affine set or its trace-zero tangent space. -/
def tomographyTargetSpan (d : ℕ) (K : TomographyDomain) : Set (Op (ChoiBasis d)) :=
  (Submodule.span ℂ (physicalTarget d K) : Set (Op (ChoiBasis d)))

/-- PDF p.2: Mathlib special unitary group, not the full unitary group. -/
abbrev SU (d : ℕ) := ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)

/-- PDF p.2: Borel outcomes on SU(d). -/
instance suMeasurableSpace (d : ℕ) : MeasurableSpace (SU d) := borel _

/-- PDF p.2, (24): probability Haar measure, specified by left invariance. -/
def IsProbabilityHaar {d : ℕ} (mu : Measure (SU d)) : Prop :=
  IsProbabilityMeasure mu ∧ ∀ U : SU d, MeasurePreserving (fun V => U * V) mu mu

/-- PDF pp.2–3: two independent SU(d) Haar variables. -/
abbrev GroupPair (d : ℕ) := SU d × SU d

/-- PDF p.2, (22): conjugation on output × input; U and V are independent. -/
def conjugateTesterSeed {d : ℕ} (g : GroupPair d) (A : Op (ChoiBasis d)) : Op (ChoiBasis d) :=
  let W := Matrix.kronecker (g.1 : Op (Fin d)) (g.2 : Op (Fin d))
  W * A * Wᴴ

/-- PDF pp.2–3, (22): covariant density on seed label × SU(d) × SU(d). -/
def covariant {d : ℕ} {X : Type*} (P : X → Op (ChoiBasis d)) :
    X × GroupPair d → Op (ChoiBasis d) := fun z => conjugateTesterSeed z.2 (P z.1)

/-- PDF pp.3–4: single-seed covariant density. -/
def testerSeedOrbit {d : ℕ} (P : Op (ChoiBasis d)) : GroupPair d → Op (ChoiBasis d) :=
  fun g => conjugateTesterSeed g P

/-- PDF p.2, (24): normalized input density |I>><<I|/d, distinct from the auxiliary pair. -/
def maximallyEntangledDensity (d : ℕ) : Op (ChoiBasis d) :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then (d : ℂ)⁻¹ else 0

/-- PDF p.3, (27): twirled frame, with zero seeds discarded by the theorem hypotheses. -/
def twirledFrame {d : ℕ} {J : Type*} [Fintype J]
    (mu : Measure (SU d)) (P : J → Op (ChoiBasis d)) : HSMatrix (ChoiBasis d) :=
  ∑ j, ∫ g, ((d : ℂ) / (P j).trace) • operatorDyad (conjugateTesterSeed g (P j)) ∂(mu.prod mu)

/-- PDF p.3, after (30): Moore–Penrose inverse of a positive Hermitian frame. -/
def frameSupportInverse {I : Type*} [Fintype I] [DecidableEq I] (X : HSMatrix I) : HSMatrix I :=
  cfc (fun t : ℝ => t⁻¹) X

/-- PDF p.3: the target must lie in the range of the frame. A zero inverse on an
unmeasured target direction is not admissible. -/
def FrameComplete {d : ℕ} (X : HSMatrix (ChoiBasis d)) (K : TomographyDomain) : Prop :=
  ∀ A ∈ tomographyTargetSpan d K, onOperator (X * frameSupportInverse X) A = A

/-- PDF p.4, note [12]: pair wires 1,3 and 2,4 in the natural vec order 1,2,3,4. -/
def pairedTensor {d : ℕ} (L R : Op (Fin d × Fin d)) : HSMatrix (ChoiBasis d) :=
  fun p q => L (p.1.1, p.2.1) (q.1.1, q.2.1) * R (p.1.2, p.2.2) (q.1.2, q.2.2)

/-- PDF p.3, (28): the four orthogonal sectors, indexed in printed order. -/
def sector (d : ℕ) : Fin 4 → HSMatrix (ChoiBasis d) :=
  ![pairedTensor (maximallyEntangledDensity d) (maximallyEntangledDensity d),
    pairedTensor (1 - maximallyEntangledDensity d) (maximallyEntangledDensity d),
    pairedTensor (maximallyEntangledDensity d) (1 - maximallyEntangledDensity d),
    pairedTensor (1 - maximallyEntangledDensity d) (1 - maximallyEntangledDensity d)]

/-- PDF p.3, (32): projectors onto the complex target spans. -/
def targetProjector (d : ℕ) : TomographyDomain → HSMatrix (ChoiBasis d)
  | .operations => 1
  | .channels => sector d 0 + sector d 1 + sector d 3
  | .unital => sector d 0 + sector d 3

/-- PDF p.1, (10), and p.3 after (30): symmetric-prior loss on the required span.
The quadratic form is ||Q_K D||_HS²; irrelevant dual components are not charged.
For operations Q_K=I, recovering (21). -/
def etaIntegrand {d : ℕ} {X : Type*} (K : TomographyDomain)
    (P D : X → Op (ChoiBasis d)) (x : X) : ℝ :=
  representationQuadratic (targetProjector d K) (D x) * (P x).trace.re / (d : ℝ)

/-- PDF p.1, (10), p.2, (21), and p.3, (33): target-dependent second-moment term. -/
def eta {d : ℕ} {X : Type*} [MeasurableSpace X] (K : TomographyDomain)
    (mu : Measure X) (P D : X → Op (ChoiBasis d)) : ℝ :=
  ∫ x, etaIntegrand K P D x ∂mu

/-- PDF pp.2–3: physical tester and finite projected-loss dual on the chosen span. -/
def TomographyAdmissible {d : ℕ} {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (P D : X → Op (ChoiBasis d)) (K : TomographyDomain) : Prop :=
  IsTesterDensity mu P ∧ IsTomographyDual mu P D (tomographyTargetSpan d K) ∧
    Integrable (etaIntegrand K P D) mu

/-- PDF p.3, (29): coefficient A, using the input marginal (trace over wire 2). -/
def coefficientA {d : ℕ} {J : Type*} [Fintype J] (P : J → Op (ChoiBasis d)) : ℝ :=
  ((∑ j, ((traceInput (P j) * traceInput (P j)).trace.re / (P j).trace.re)) - 1) /
    ((d : ℝ)^2 - 1)

/-- PDF p.3, (29): coefficient B, using the output marginal (trace over wire 1). -/
def coefficientB {d : ℕ} {J : Type*} [Fintype J] (P : J → Op (ChoiBasis d)) : ℝ :=
  ((∑ j, ((QAlgorithms.traceLeft (P j) * QAlgorithms.traceLeft (P j)).trace.re /
    (P j).trace.re)) - 1) / ((d : ℝ)^2 - 1)

/-- PDF p.3, (29): coefficient C. -/
def coefficientC {d : ℕ} {J : Type*} [Fintype J] (P : J → Op (ChoiBasis d)) : ℝ :=
  ((∑ j, (d : ℝ) * (P j * P j).trace.re / (P j).trace.re) -
    ((d : ℝ)^2 - 1) * (coefficientA P + coefficientB P) - 1) / (((d : ℝ)^2 - 1)^2)

/-- PDF p.3, (25): positive nonzero seeds, with total trace d. -/
def Seeds {d : ℕ} {J : Type*} [Fintype J] (P : J → Op (ChoiBasis d)) : Prop :=
  (∀ j, (P j).PosSemidef ∧ 0 < (P j).trace.re) ∧ ∑ j, (P j).trace = (d : ℂ)

/-- PDF p.3: rank-one positive seed, including its normalized vectorization. -/
def RankOneSeed {d : ℕ} (P : Op (ChoiBasis d)) : Prop :=
  ∃ (alpha : ℝ) (Psi : Matrix (Fin d) (Fin d) ℂ), 0 < alpha ∧ hsSquared Psi = 1 ∧
    P = (alpha : ℂ) • operatorDyad Psi

/-- PDF p.3, (33): rational losses, used only on the explicitly admissible A range. -/
def rankOneLoss (d : ℕ) (K : TomographyDomain) (A : ℝ) : ℝ :=
  let m := (d : ℝ)^2 - 1
  match K with
  | .operations => 1 + m * (2 / A + m^2 / (1 - 2*A))
  | .channels => 1 + m * (1 / A + m^2 / (1 - 2*A))
  | .unital => 1 + m * (m^2 / (1 - 2*A))

/-- PDF p.3, (34): attained minima, including the scalar value at d=1. -/
def optimum (d : ℕ) : TomographyDomain → ℝ
  | .operations => (d : ℝ)^6 + (d : ℝ)^4 - (d : ℝ)^2
  | .channels => (d : ℝ)^6 + (2 * Real.sqrt 2 - 3) * (d : ℝ)^4 +
      (5 - 4 * Real.sqrt 2) * (d : ℝ)^2 + 2 * (Real.sqrt 2 - 1)
  | .unital => ((d : ℝ)^2 - 1)^3 + 1

/-- PDF pp.3–4, (33),(36): channel beta corrected using A=beta²/(d+1).
Printed: beta_C=[(d-1)(2+sqrt(2)(d²-1))]^(-1/2).
Changed: beta_C=sqrt((d+1)/(2+sqrt(2)(d²-1))).
Why: (29),(36) give A=beta²/(d+1), while (33) fixes A=1/(2+sqrt(2)(d²-1)). -/
def optimalBeta (d : ℕ) : TomographyDomain → ℝ
  | .operations => Real.sqrt (((d : ℝ) + 1) / ((d : ℝ)^2 + 1))
  | .channels => Real.sqrt (((d : ℝ) + 1) / (2 + Real.sqrt 2 * ((d : ℝ)^2 - 1)))
  | .unital => 0

/-- PDF p.4, (36): the explicit positive square-root seed matrix. -/
def seedMatrix {d : ℕ} (K : TomographyDomain) (psi : EuclideanSpace ℂ (Fin d)) : Op (Fin d) :=
  let beta := optimalBeta d K
  cfc Real.sqrt (((((1 - beta) / (d : ℝ)) : ℂ) • (1 : Op (Fin d))) +
    (beta : ℂ) • QAlgorithms.pureDensity psi)

/-- PDF p.4, (35)–(36): attaining tester seed d|Psi>><<Psi|. -/
def optimalSeed {d : ℕ} (K : TomographyDomain) (psi : EuclideanSpace ℂ (Fin d)) : Op (ChoiBasis d) :=
  (d : ℂ) • operatorDyad (seedMatrix K psi)

/-- PDF pp.3–4: the attainment assertion, including physical preparation and target completeness. -/
def Attains {d : ℕ} (mu : Measure (SU d)) (K : TomographyDomain)
    (psi : EuclideanSpace ℂ (Fin d)) : Prop :=
  FrameComplete (twirledFrame mu (fun _ : Fin 1 => optimalSeed K psi)) K ∧
    QAlgorithms.IsDensityMatrix (maximallyEntangledDensity d) ∧
    IsPOVMDensity (mu.prod mu) (fun g => (d : ℂ) • testerSeedOrbit (optimalSeed K psi) g) ∧
    (∀ g, inducedTester (maximallyEntangledDensity d)
      ((d : ℂ) • testerSeedOrbit (optimalSeed K psi) g) = testerSeedOrbit (optimalSeed K psi) g) ∧
    ∃ D : GroupPair d → Op (ChoiBasis d),
      TomographyAdmissible (mu.prod mu) (testerSeedOrbit (optimalSeed K psi)) D K ∧
      eta K (mu.prod mu) (testerSeedOrbit (optimalSeed K psi)) D = optimum d K

/-- PDF p.1, (9): second moment for arbitrary mean and representation. -/
def bayesEta {I X : Type*} [Fintype I] [MeasurableSpace X]
    (mu : Measure X) (P D : X → Op I) (R : Op I) (G : HSMatrix I) : ℝ :=
  ∫ x, (P x * R).trace.re * representationQuadratic G (D x) ∂mu

/-- PDF pp.1–2, (7),(19): zero-valued estimator on a missing-probability failure. -/
def bayesVariance {I X : Type*} [Fintype I] [MeasurableSpace X]
    (mu : Measure X) (P D : X → Op I) (R : Op I) (G : HSMatrix I) : ℝ :=
  bayesEta mu P D R G - representationQuadratic G R

/-- PDF pp.1–2, (8)–(10),(20): general prior mean reduction with projected observables. -/
def BayesianReduction {I X K : Type*} [Fintype I] [MeasurableSpace X] [MeasurableSpace K]
    (mu : Measure X) (nu : Measure K) (P D : X → Op I) (R : K → Op I)
    (G Q : HSMatrix I) : Prop :=
  let mean := ∫ k, R k ∂nu
  (∫ k, bayesVariance mu P D (R k) G ∂nu) =
    bayesEta mu P D mean G - ∫ k, representationQuadratic G (R k) ∂nu ∧
  (∫ k, bayesVariance mu P D (R k) (Q * G * Q) ∂nu) =
    bayesEta mu P D mean (Q * G * Q) - ∫ k, representationQuadratic G (R k) ∂nu

/-- PDF pp.1–2: integrability assumptions prevent zero-valued undefined Bochner integrals. -/
def BayesianIntegrable {I X K : Type*} [Fintype I] [MeasurableSpace X] [MeasurableSpace K]
    (mu : Measure X) (nu : Measure K) (P D : X → Op I) (R : K → Op I)
    (G : HSMatrix I) : Prop :=
  Integrable R nu ∧ Integrable (fun k => representationQuadratic G (R k)) nu ∧
    Integrable (fun z : K × X =>
      (P z.2 * R z.1).trace.re * representationQuadratic G (D z.2)) (nu.prod mu) ∧
    (∀ k, Integrable (fun x => (P x * R k).trace.re * representationQuadratic G (D x)) mu)

/-- PDF p.4, Fig.1: generalized Bell basis matrices (shift and phase), for positive d. -/
def bellMatrix (d : ℕ) (j : Fin d × Fin d) : Op (Fin d) :=
  fun a x => if a.val = (x.val + j.1.val) % d then
    Complex.exp (2 * Real.pi * Complex.I * ((j.2.val * x.val : ℕ) : ℂ) / (d : ℂ)) else 0

/-- PDF p.4: raw two-Bell contraction, keeping the auxiliary |Psi>> separate from the Choi input. -/
def bellAmplitude {d : ℕ} (Psi : Op (Fin d)) (g : GroupPair d)
    (j k : Fin d × Fin d) (p : ChoiBasis d) : ℂ :=
  (d : ℂ)⁻¹ * ∑ a, ∑ b, ∑ s, ∑ t,
    Psi a b * conj (bellMatrix d j a s) * (g.1 : Op (Fin d)) s p.1 *
      conj (bellMatrix d k b t) * (g.2 : Op (Fin d)) t p.2

/-- PDF p.4: each pair of discrete Bell labels has its own physical effect. -/
def bellEffect {d : ℕ} (Psi : Op (Fin d)) (g : GroupPair d)
    (j k : Fin d × Fin d) : Op (ChoiBasis d) :=
  fun p q => conj (bellAmplitude Psi g j k p) * bellAmplitude Psi g j k q

/-- PDF p.4: one remaining branch, a projective measurement preceded by U. -/
def branchEffect {d : ℕ} (U : SU d) (k : Fin d) : Op (Fin d) :=
  (U : Op (Fin d))ᴴ * QAlgorithms.pureDensity (QAlgorithms.ket k) * (U : Op (Fin d))

/-- PDF p.4: normalized remote input for effect/POVM tomography is a uniformly selected
projective outcome, followed by the entire unknown POVM. -/
def branchPOVMProbability {d : ℕ} {J : Type*} (E : J → Op (Fin d))
    (U : SU d) (k : Fin d) (j : J) : ℝ :=
  (E j * branchEffect U k).trace.re / (d : ℝ)

/-- Canonical linear dual for the randomized projective frame; no numerical optimum is asserted. -/
def branchDual {d : ℕ} (U : SU d) (k : Fin d) : Op (Fin d) :=
  ((d : ℂ) + 1) • branchEffect U k - 1

/-- PDF p.4 after (37): representation operator for independently Haar-randomized
input rho and output observable A. In output-first Choi coordinates the input is transposed. -/
def orbitRepresentation {d : ℕ} (haar : Measure (SU d))
    (rho A : Op (Fin d)) : HSMatrix (ChoiBasis d) :=
  ∫ g : GroupPair d, operatorDyad
    (Matrix.kronecker
      ((g.1 : Op (Fin d)) * A * (g.1 : Op (Fin d))ᴴ)
      (((g.2 : Op (Fin d)) * rho * (g.2 : Op (Fin d))ᴴ).transpose)) ∂(haar.prod haar)

/-! Sanity checks for local definitions (complete proofs, with no theorem proof obligations). -/

example {I : Type*} (A : Op I) (i j : I) : operatorCoordinates A (i,j) = A i j := rfl

example : maximallyEntangledDensity 1 (0,0) (0,0) = 1 := by
  norm_num [maximallyEntangledDensity]

example : optimum 1 .operations = 1 := by norm_num [optimum]

example : optimum 1 .unital = 1 := by norm_num [optimum]

example : optimalBeta 2 .unital = 0 := rfl

example {I : Type*} [Fintype I] (A : Op I) : representationQuadratic (0 : HSMatrix I) A = 0 := by
  simp [representationQuadratic]

example : operatorDyad (1 : Op (Fin 1)) (0,0) (0,0) = 1 := by
  simp [operatorDyad, operatorCoordinates]

example {O I A : Type*} [Fintype A] (rho : Op (I × A)) :
    inducedTester (O := O) rho (0 : Op (O × A)) = 0 := by
  ext p q
  simp [inducedTester]

example {I : Type*} [Fintype I] [DecidableEq I] :
    frameSupportInverse (1 : HSMatrix I) = 1 := by
  simp [frameSupportInverse, cfc_one]

example {d : ℕ} (P : Op (ChoiBasis d)) :
    conjugateTesterSeed ((1 : SU d), (1 : SU d)) P = P := by
  simp [conjugateTesterSeed, Matrix.one_kronecker_one]

example {d : ℕ} (haar : Measure (SU d)) (rho : Op (Fin d)) :
    orbitRepresentation haar rho 0 = 0 := by
  have hdyad : operatorDyad (0 : Op (ChoiBasis d)) = 0 := by
    ext p q
    simp [operatorDyad, operatorCoordinates]
  simp [orbitRepresentation, Matrix.kronecker, hdyad]

/-! The source results. Each named theorem below ends in `by sorry`. -/

end QAlgorithms.Papers.Independent.Claimed50.P28


