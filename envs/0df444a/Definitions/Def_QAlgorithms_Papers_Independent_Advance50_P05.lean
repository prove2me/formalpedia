-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P05
-- name    : QAlgorithms_Papers_Independent_Advance50_P05
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T08:23:23.136346+00:00
-- url     : https://prove2.me/theorems/1d10c83a-2120-4b83-8a50-c981ea084f7e
-- title:
--   Definitions for Distilling entanglement from arbitrary resources
-- statement:
--   The objects the formalized statements of *Distilling entanglement from arbitrary resources* (arXiv:1006.1896) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `embeddedMES`: PDF pp.3,16, (1),(60): the normalized rank-m MES embedded into arbitrary orthonormal local frames U,V. Theorems require m>0 and U,V isometries. The reused epr has density coefficients 1/m, hence ket coefficients 1/sqrt(m).
--   - `RectangularInstrument`: PDF p.7, Definition 4: a rectangular CP instrument. The private Kraus index is distinct from the communicated outcome. A common Kraus count loses no finite-dimensional CP branch, since shorter families can be padded by zero.
--   - `RectangularInstrument.branch`: PDF p.7, Definition 4: each CP branch is unnormalized.
--   - `RectangularInstrument.flagged`: PDF pp.7,9--10: the entire flagged output on C:(B,X), without postselection or division by a branch probability.
--   - `ForwardProtocol`: PDF pp.6--7,10: a forward protocol sends only Alice's classical outcome and applies an outcome-dependent CPTP decoder on Bob. Rectangular Kraus maps include arbitrary local preparation and disposal.
--   - `ForwardProtocol.operation`: PDF p.10, (33): sum every classical branch of the actual forward protocol.
--   - `finiteLOCCOn`: PDF p.6: transport physical local bases separately to the accepted finite adaptive LOCC tree. This neither transposes a matrix nor moves a quantum register between the parties.
--   - `DistillationDirection`: PDF p.6: the two distinct free-communication classes.
--   - `IsDistillationOperation`: PDF pp.6--7: actual protocol membership, never arbitrary joint channels or separable maps supplied in place of LOCC.
--   - `DistillationCode`: PDF pp.6--7, Definitions 1--2: a physical distillation code, with arbitrary positive integer rank and positive ambient local dimensions. Frames fix the MES before its fidelity is evaluated. No entangled ancilla is provided for free.
--   - `DistillationCode.Meets`: PDF pp.6--7: root-fidelity error of the full unconditional output.
--   - `distillableEntanglementOneShot`: PDF p.7, Definition 2: optimize logarithms of all feasible positive integer ranks. This equals optimization over all R>=0 with 2^R<=M in Definition 1. EReal preserves the unbounded endpoint eps>=1. Attainment on eps<1 is asserted in the converse theorems, rather than assumed in this definition.
--   - `OneShotAttained`: PDF p.7: retain the printed operational maximum on its finite domain.
--   - `fidelityBall`: PDF p.5, (11): subnormalized state smoothing with the unmodified root fidelity. No vacuum term and no normalization of a smoothing candidate.
--   - `acceptanceSet`: PDF p.5, (12): all positive effects P<=I with the specified acceptance. This is different from state smoothing and does not require P to be a projector.
--   - `effectZero`: PDF p.4, (7): effect-modified order-zero divergence, extended at zero overlap. The support and BOTH square roots of P occur in the printed order.
--   - `zeroCoherent`: PDF p.5, (13): minimization over every normalized Bob comparison state.
--   - `smoothedZero`: PDF p.4, (9): outer maximum over the fidelity ball, inner minimum over normalized comparison states. Zero candidates give +infinity through dMin.
--   - `conditionalEffectZero`: PDF p.4, (10): conditional effect divergence before effect maximization.
--   - `effectSmoothedZero`: PDF p.4, (10): effect smoothing; for delta>=1 the actual feasible zero effect gives +infinity, not Real.logb 2 0.
--   - `EffectExtremaAttained`: PDF p.4, (10): witnesses for the printed inner minimum and outer maximum.
--   - `petzTwo`: PDF pp.4--6, (5),(17)--(20), alpha=2: the UNNORMALIZED Petz expression. Support mismatch gives +infinity. Zero numerator gives -infinity. There is no division by Tr rho and no sandwiched-Renyi substitution.
--   - `twoCoherent`: PDF pp.5--6: unsmoothed order-two coherent information.
--   - `smoothedTwo`: PDF p.6, (19)--(20): MINIMIZE over subnormalized smoothing candidates at order two, unlike the order-zero maximum.
--   - `ZeroExtremaAttained`: PDF pp.4--6: the attained zero-order smoothing and comparison extrema.
--   - `TwoExtremaAttained`: PDF pp.5--6: the attained order-two smoothing and comparison minima.
--   - `AlicePreprocessing`: PDF pp.7,9,13: all finite instrument preprocessings on Alice, with output dimension and classical outcome count chosen as part of the map.
--   - `AlicePreprocessing.output`: PDF pp.9,13: all unnormalized branches retained, flags at Bob.
--   - `TwoWayPreprocessing`: PDF pp.11,13: general two-way preprocessing with changing output spaces.
--   - `dependentSpectralMass`: PDF p.12, (42): positive-part spectral mass on arbitrary dependent finite spaces. The threshold uses the actual positive block length k+1.
--   - `dependentSpectralInf`: PDF p.12, (42): spectral INF-divergence, allowing arbitrary changing finite output spaces. Empty/unbounded threshold sets have extended values.
--   - `spectralCoherent`: PDF pp.12--13, (45): minimization over ALL normalized comparison-state sequences, with no identical-copy restriction and no prescribed marginals.
--   - `SpectralMinimumAttained`: PDF p.13: the comparison minimum, not just its extremal value, is attained.
--   - `asymptoticInner`: PDF p.12, (40): first positive-block liminf, then the right limit in error. Theorem 1 asserts actual convergence to this computed liminf.
--   - `asymptoticDistillable`: PDF p.12, (40): separate operational value for each assistance class.
--   - `forwardSequenceScore`: PDF p.13, (47): score of a whole sequence of Alice instruments, chosen without any restriction on output growth or relation between different blocks.
--   - `twoWaySequenceScore`: PDF p.13, (48): score of a whole sequence of actual adaptive two-way maps.
--   - `identityInstrument`: PDF p.7: the single-outcome identity instrument, used to pin the instrument and protocol normalization conventions.
--   - `identityForward`: PDF pp.7,10: the identity forward protocol with one communicated outcome.
-- source:
--   Distilling entanglement from arbitrary resources, arXiv:1006.1896v2, https://arxiv.org/abs/1006.1896v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21

/-!
Buscemi--Datta, arXiv:1006.1896v2, Distilling entanglement from arbitrary resources.
Only pinned accepted definitions are reused. The independent-paper override permits
these reviewed imports; no imported theorem is assumed as a hypothesis.
All new objects are local to this paper. Alice is the first factor, classical flags
belong to Bob, and logarithms are in bits. Positive block length n is indexed by k=n-1.
The operational interpretation is the plan's arbitrary finite adaptive LOCC protocol,
with no uniform bound on rounds, local dimensions, outcomes, or Kraus multiplicities.
No closure of LOCC or compactness of its set is assumed.
The three defective direct bounds are deferred in HARD.md. Compilation is pending.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P05

open QAlgorithms Filter
open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Dependency50.P19 (first both epr IsIso)
open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)
open QAlgorithms.Papers.Independent.Dependency50.P35 (elog marginalAB marginalAC)
open QAlgorithms.Papers.Independent.Support50.P21 (dMin weakPositive PositiveTensorBasis)
open QAlgorithms.Papers.Independent.Information100.P21 (FiniteLOCC)
open QAlgorithms.Papers.Independent.Information100.P67 (IsSubnormalized)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.3,16, (1),(60): the normalized rank-m MES embedded into arbitrary
orthonormal local frames U,V. Theorems require m>0 and U,V isometries.
The reused epr has density coefficients 1/m, hence ket coefficients 1/sqrt(m). -/
def embeddedMES {A B : Type} [Fintype A] [Fintype B] {m : ℕ}
    (U : Matrix A (Fin m) ℂ) (V : Matrix B (Fin m) ℂ) : Matrix (A × B) (A × B) ℂ :=
  Matrix.kronecker U V * epr m * (Matrix.kronecker U V)ᴴ

/-- PDF p.7, Definition 4: a rectangular CP instrument. The private Kraus
index is distinct from the communicated outcome. A common Kraus count loses
no finite-dimensional CP branch, since shorter families can be padded by zero. -/
structure RectangularInstrument (A C X : Type) [Fintype A] [DecidableEq A]
    [Fintype C] [Fintype X] where
  krausCount : ℕ
  kraus : X → Fin krausCount → Matrix C A ℂ
  complete : (∑ x, ∑ j, (kraus x j)ᴴ * kraus x j) = 1

/-- PDF p.7, Definition 4: each CP branch is unnormalized. -/
def RectangularInstrument.branch {A C X : Type} [Fintype A] [DecidableEq A]
    [Fintype C] [Fintype X] (I : RectangularInstrument A C X) (x : X) : Superop A C :=
  krausApply (I.kraus x)

/-- PDF pp.7,9--10: the entire flagged output on C:(B,X), without
postselection or division by a branch probability. -/
def RectangularInstrument.flagged {A B C X : Type} [Fintype A] [DecidableEq A]
    [Fintype C] [Fintype X] [DecidableEq X] (I : RectangularInstrument A C X)
    (rho : Matrix (A × B) (A × B) ℂ) : Matrix (C × (B × X)) (C × (B × X)) ℂ :=
  fun p q => if p.2.2 = q.2.2 then
    first (I.branch p.2.2) rho (p.1, p.2.1) (q.1, q.2.1) else 0

/-- PDF pp.6--7,10: a forward protocol sends only Alice's classical outcome
and applies an outcome-dependent CPTP decoder on Bob. Rectangular Kraus maps
include arbitrary local preparation and disposal. -/
structure ForwardProtocol (A B C D : Type) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [Fintype D] where
  outcomeCount : ℕ
  instrument : RectangularInstrument A C (Fin (outcomeCount + 1))
  decoder : Fin (outcomeCount + 1) → Superop B D
  decoderCPTP : ∀ x, IsChannel (decoder x)

/-- PDF p.10, (33): sum every classical branch of the actual forward protocol. -/
def ForwardProtocol.operation {A B C D : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [Fintype D]
    (P : ForwardProtocol A B C D) : Superop (A × B) (C × D) :=
  fun rho => ∑ x, both (P.instrument.branch x) (P.decoder x) rho

/-- PDF p.6: transport physical local bases separately to the accepted
finite adaptive LOCC tree. This neither transposes a matrix nor moves a
quantum register between the parties. -/
def finiteLOCCOn {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (L : Superop (A × B) (C × D)) : Prop :=
  FiniteLOCC (fun X : Matrix (Fin (Fintype.card A) × Fin (Fintype.card B))
      (Fin (Fintype.card A) × Fin (Fintype.card B)) ℂ =>
    let input : Matrix (A × B) (A × B) ℂ := fun i j =>
      X ((Fintype.equivFin A) i.1, (Fintype.equivFin B) i.2)
        ((Fintype.equivFin A) j.1, (Fintype.equivFin B) j.2)
    fun i j => L input
      ((Fintype.equivFin C).symm i.1, (Fintype.equivFin D).symm i.2)
      ((Fintype.equivFin C).symm j.1, (Fintype.equivFin D).symm j.2))

/-- PDF p.6: the two distinct free-communication classes. -/
inductive DistillationDirection where
  | forward
  | twoWay

/-- PDF pp.6--7: actual protocol membership, never arbitrary joint channels
or separable maps supplied in place of LOCC. -/
def IsDistillationOperation {A B C D : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [Fintype D]
    (direction : DistillationDirection) (L : Superop (A × B) (C × D)) : Prop :=
  match direction with
  | .forward => ∃ P : ForwardProtocol A B C D, L = P.operation
  | .twoWay => finiteLOCCOn L

/-- PDF pp.6--7, Definitions 1--2: a physical distillation code, with arbitrary
positive integer rank and positive ambient local dimensions. Frames fix the
MES before its fidelity is evaluated. No entangled ancilla is provided for free. -/
structure DistillationCode (direction : DistillationDirection) (A B : Type)
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] where
  rank : ℕ
  rankPos : 0 < rank
  outA : ℕ
  outB : ℕ
  outAPos : 0 < outA
  outBPos : 0 < outB
  aliceFrame : Matrix (Fin outA) (Fin rank) ℂ
  bobFrame : Matrix (Fin outB) (Fin rank) ℂ
  aliceIso : IsIso aliceFrame
  bobIso : IsIso bobFrame
  operation : Superop (A × B) (Fin outA × Fin outB)
  allowed : IsDistillationOperation direction operation

/-- PDF pp.6--7: root-fidelity error of the full unconditional output. -/
def DistillationCode.Meets {direction : DistillationDirection} {A B : Type}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (C : DistillationCode direction A B) (rho : Matrix (A × B) (A × B) ℂ)
    (eps : ℝ) : Prop :=
  1 - eps ≤ rootFidelity (C.operation rho) (embeddedMES C.aliceFrame C.bobFrame)

/-- PDF p.7, Definition 2: optimize logarithms of all feasible positive integer
ranks. This equals optimization over all R>=0 with 2^R<=M in Definition 1.
EReal preserves the unbounded endpoint eps>=1. Attainment on eps<1 is asserted
in the converse theorems, rather than assumed in this definition. -/
def distillableEntanglementOneShot {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (direction : DistillationDirection) (rho : Matrix (A × B) (A × B) ℂ) (eps : ℝ) : EReal :=
  sSup {v | ∃ C : DistillationCode direction A B,
    C.Meets rho eps ∧ v = (Real.logb 2 (C.rank : ℝ) : EReal)}

/-- PDF p.7: retain the printed operational maximum on its finite domain. -/
def OneShotAttained {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (direction : DistillationDirection)
    (rho : Matrix (A × B) (A × B) ℂ) (eps : ℝ) : Prop :=
  ∃ C : DistillationCode direction A B, C.Meets rho eps ∧
    distillableEntanglementOneShot direction rho eps = (Real.logb 2 (C.rank : ℝ) : EReal)

/-- PDF p.5, (11): subnormalized state smoothing with the unmodified root
fidelity. No vacuum term and no normalization of a smoothing candidate. -/
def fidelityBall {I : Type} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) (delta : ℝ) : Set (Matrix I I ℂ) :=
  {r | IsSubnormalized r ∧ 1 - delta ^ 2 ≤ rootFidelity rho r ^ 2}

/-- PDF p.5, (12): all positive effects P<=I with the specified acceptance.
This is different from state smoothing and does not require P to be a projector. -/
def acceptanceSet {I : Type} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) (delta : ℝ) : Set (Matrix I I ℂ) :=
  {P | IsEffect P ∧ 1 - delta ≤ effectProb P rho}

/-- PDF p.4, (7): effect-modified order-zero divergence, extended at zero
overlap. The support and BOTH square roots of P occur in the printed order. -/
def effectZero {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma P : Matrix I I ℂ) : EReal :=
  -elog ((cfc Real.sqrt P * support rho * cfc Real.sqrt P * sigma).trace.re)

/-- PDF p.5, (13): minimization over every normalized Bob comparison state. -/
def zeroCoherent {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sInf {v | ∃ sigma : Matrix B B ℂ, IsDensityMatrix sigma ∧
    v = dMin rho (Matrix.kronecker (1 : Matrix A A ℂ) sigma)}

/-- PDF p.4, (9): outer maximum over the fidelity ball, inner minimum over
normalized comparison states. Zero candidates give +infinity through dMin. -/
def smoothedZero {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ)
    (delta : ℝ) : EReal :=
  sSup {v | ∃ r ∈ fidelityBall rho delta, v = zeroCoherent r}

/-- PDF p.4, (10): conditional effect divergence before effect maximization. -/
def conditionalEffectZero {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (rho P : Matrix (A × B) (A × B) ℂ) : EReal :=
  sInf {v | ∃ sigma : Matrix B B ℂ, IsDensityMatrix sigma ∧
    v = effectZero rho (Matrix.kronecker (1 : Matrix A A ℂ) sigma) P}

/-- PDF p.4, (10): effect smoothing; for delta>=1 the actual feasible zero
effect gives +infinity, not Real.logb 2 0. -/
def effectSmoothedZero {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ)
    (delta : ℝ) : EReal :=
  sSup {v | ∃ P ∈ acceptanceSet rho delta, v = conditionalEffectZero rho P}

/-- PDF p.4, (10): witnesses for the printed inner minimum and outer maximum. -/
def EffectExtremaAttained {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ)
    (delta : ℝ) : Prop :=
  ∃ P ∈ acceptanceSet rho delta, ∃ sigma : Matrix B B ℂ,
    IsDensityMatrix sigma ∧ effectSmoothedZero rho delta = conditionalEffectZero rho P ∧
    conditionalEffectZero rho P = effectZero rho
      (Matrix.kronecker (1 : Matrix A A ℂ) sigma) P

/-- PDF pp.4--6, (5),(17)--(20), alpha=2: the UNNORMALIZED Petz expression.
Support mismatch gives +infinity. Zero numerator gives -infinity.
There is no division by Tr rho and no sandwiched-Renyi substitution. -/
def petzTwo {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) : EReal :=
  if SupportIncluded rho sigma then
    elog ((rho * rho * supportPower sigma (-1)).trace.re)
  else ⊤

/-- PDF pp.5--6: unsmoothed order-two coherent information. -/
def twoCoherent {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : EReal :=
  sInf {v | ∃ sigma : Matrix B B ℂ, IsDensityMatrix sigma ∧
    v = petzTwo rho (Matrix.kronecker (1 : Matrix A A ℂ) sigma)}

/-- PDF p.6, (19)--(20): MINIMIZE over subnormalized smoothing candidates
at order two, unlike the order-zero maximum. -/
def smoothedTwo {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ)
    (delta : ℝ) : EReal :=
  sInf {v | ∃ r ∈ fidelityBall rho delta, v = twoCoherent r}

/-- PDF pp.4--6: the attained zero-order smoothing and comparison extrema. -/
def ZeroExtremaAttained {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ)
    (delta : ℝ) : Prop :=
  ∃ r ∈ fidelityBall rho delta, ∃ sigma : Matrix B B ℂ,
    IsDensityMatrix sigma ∧ smoothedZero rho delta = zeroCoherent r ∧
    zeroCoherent r = dMin r (Matrix.kronecker (1 : Matrix A A ℂ) sigma)

/-- PDF pp.5--6: the attained order-two smoothing and comparison minima. -/
def TwoExtremaAttained {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ)
    (delta : ℝ) : Prop :=
  ∃ r ∈ fidelityBall rho delta, ∃ sigma : Matrix B B ℂ,
    IsDensityMatrix sigma ∧ smoothedTwo rho delta = twoCoherent r ∧
    twoCoherent r = petzTwo r (Matrix.kronecker (1 : Matrix A A ℂ) sigma)

/-- PDF pp.7,9,13: all finite instrument preprocessings on Alice, with
output dimension and classical outcome count chosen as part of the map. -/
structure AlicePreprocessing (A : Type) [Fintype A] [DecidableEq A] where
  outDim : ℕ
  outPos : 0 < outDim
  outcomes : ℕ
  outcomesPos : 0 < outcomes
  instrument : RectangularInstrument A (Fin outDim) (Fin outcomes)

/-- PDF pp.9,13: all unnormalized branches retained, flags at Bob. -/
def AlicePreprocessing.output {A B : Type} [Fintype A] [DecidableEq A]
    (P : AlicePreprocessing A) (rho : Matrix (A × B) (A × B) ℂ) :=
  P.instrument.flagged rho

/-- PDF pp.11,13: general two-way preprocessing with changing output spaces. -/
structure TwoWayPreprocessing (A B : Type) [Fintype A] [Fintype B] where
  outA : ℕ
  outB : ℕ
  outAPos : 0 < outA
  outBPos : 0 < outB
  operation : Superop (A × B) (Fin outA × Fin outB)
  locc : finiteLOCCOn operation

/-- PDF p.12, (42): positive-part spectral mass on arbitrary dependent
finite spaces. The threshold uses the actual positive block length k+1. -/
def dependentSpectralMass {I : ℕ → Type} [∀ k, Fintype (I k)]
    [∀ k, DecidableEq (I k)] (rho sigma : (k : ℕ) → Matrix (I k) (I k) ℂ)
    (gamma : ℝ) (k : ℕ) : ℝ :=
  let delta := rho k - (Real.rpow 2 (((k + 1 : ℕ) : ℝ) * gamma) : ℂ) • sigma k
  (weakPositive delta * delta).trace.re

/-- PDF p.12, (42): spectral INF-divergence, allowing arbitrary changing
finite output spaces. Empty/unbounded threshold sets have extended values. -/
def dependentSpectralInf {I : ℕ → Type} [∀ k, Fintype (I k)]
    [∀ k, DecidableEq (I k)] (rho sigma : (k : ℕ) → Matrix (I k) (I k) ℂ) : EReal :=
  sSup {v : EReal | ∃ gamma : ℝ, v = (gamma : EReal) ∧
    Filter.liminf (dependentSpectralMass rho sigma gamma) atTop = 1}

/-- PDF pp.12--13, (45): minimization over ALL normalized comparison-state
sequences, with no identical-copy restriction and no prescribed marginals. -/
def spectralCoherent {A B : ℕ → Type} [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    [∀ k, Fintype (B k)] [∀ k, DecidableEq (B k)]
    (rho : (k : ℕ) → Matrix (A k × B k) (A k × B k) ℂ) : EReal :=
  sInf {v | ∃ sigma : (k : ℕ) → Matrix (B k) (B k) ℂ,
    (∀ k, IsDensityMatrix (sigma k)) ∧
    v = dependentSpectralInf rho (fun k => Matrix.kronecker (1 : Matrix (A k) (A k) ℂ) (sigma k))}

/-- PDF p.13: the comparison minimum, not just its extremal value, is attained. -/
def SpectralMinimumAttained {A B : ℕ → Type}
    [∀ k, Fintype (A k)] [∀ k, DecidableEq (A k)]
    [∀ k, Fintype (B k)] [∀ k, DecidableEq (B k)]
    (rho : (k : ℕ) → Matrix (A k × B k) (A k × B k) ℂ) : Prop :=
  ∃ sigma : (k : ℕ) → Matrix (B k) (B k) ℂ,
    (∀ k, IsDensityMatrix (sigma k)) ∧
    spectralCoherent rho = dependentSpectralInf rho
      (fun k => Matrix.kronecker (1 : Matrix (A k) (A k) ℂ) (sigma k))

/-- PDF p.12, (40): first positive-block liminf, then the right limit in
error. Theorem 1 asserts actual convergence to this computed liminf. -/
def asymptoticInner {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (direction : DistillationDirection)
    (rho : (k : ℕ) → Matrix (PositiveTensorBasis A k × PositiveTensorBasis B k)
      (PositiveTensorBasis A k × PositiveTensorBasis B k) ℂ) (eps : ℝ) : EReal :=
  Filter.liminf (fun k => (((1 / ((k + 1 : ℕ) : ℝ)) : ℝ) : EReal) *
    distillableEntanglementOneShot direction (rho k) eps) atTop

/-- PDF p.12, (40): separate operational value for each assistance class. -/
def asymptoticDistillable {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (direction : DistillationDirection)
    (rho : (k : ℕ) → Matrix (PositiveTensorBasis A k × PositiveTensorBasis B k)
      (PositiveTensorBasis A k × PositiveTensorBasis B k) ℂ) : EReal :=
  Filter.liminf (asymptoticInner direction rho) (nhdsWithin 0 (Set.Ioi 0))

/-- PDF p.13, (47): score of a whole sequence of Alice instruments, chosen
without any restriction on output growth or relation between different blocks. -/
def forwardSequenceScore {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (rho : (k : ℕ) → Matrix (PositiveTensorBasis A k × PositiveTensorBasis B k)
      (PositiveTensorBasis A k × PositiveTensorBasis B k) ℂ)
    (P : (k : ℕ) → AlicePreprocessing (PositiveTensorBasis A k)) : EReal :=
  spectralCoherent (fun k => (P k).output (rho k))

/-- PDF p.13, (48): score of a whole sequence of actual adaptive two-way maps. -/
def twoWaySequenceScore {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (rho : (k : ℕ) → Matrix (PositiveTensorBasis A k × PositiveTensorBasis B k)
      (PositiveTensorBasis A k × PositiveTensorBasis B k) ℂ)
    (P : (k : ℕ) → TwoWayPreprocessing (PositiveTensorBasis A k) (PositiveTensorBasis B k)) : EReal :=
  spectralCoherent (fun k => (P k).operation (rho k))

/-- PDF p.7: the single-outcome identity instrument, used to pin the
instrument and protocol normalization conventions. -/
def identityInstrument (A : Type) [Fintype A] [DecidableEq A] :
    RectangularInstrument A A (Fin 1) where
  krausCount := 1
  kraus := fun _ _ => 1
  complete := by simp

/-- PDF pp.7,10: the identity forward protocol with one communicated outcome. -/
def identityForward (A B : Type) [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] : ForwardProtocol A B A B where
  outcomeCount := 0
  instrument := identityInstrument A
  decoder := fun _ X => X
  decoderCPTP := by
    intro x
    refine ⟨1, (fun _ => 1), ?_, ?_⟩
    · simp [IsKrausFamily]
    · intro X
      simp [krausApply]

/-! Sanity examples: small source cases and agreement with the frozen substrate. -/

example {A B : Type} [Fintype A] [DecidableEq A]
    (rho : Matrix (A × B) (A × B) ℂ) (a a2 : A) (b b2 : B) :
    (identityInstrument A).flagged rho (a, (b, 0)) (a2, (b2, 0)) =
      rho (a, b) (a2, b2) := by
  have hbranch : (identityInstrument A).branch (0 : Fin 1) = (fun X => X) := by
    funext X
    change (∑ j : Fin 1, (1 : Matrix A A ℂ) * X * (1 : Matrix A A ℂ)ᴴ) = X
    simp only [Fin.sum_univ_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  simp only [RectangularInstrument.flagged, if_pos rfl, hbranch]
  rfl

example {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] :
    (identityForward A B).operation = (fun X => X) := by
  have hbranch : ∀ x : Fin 1, (identityInstrument A).branch x = (fun X => X) := by
    intro x
    funext X
    change (∑ j : Fin 1, (1 : Matrix A A ℂ) * X * (1 : Matrix A A ℂ)ᴴ) = X
    simp only [Fin.sum_univ_one, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  funext X
  change (∑ x : Fin 1, both ((identityInstrument A).branch x) (fun Y => Y) X) = X
  simp only [Fin.sum_univ_one, hbranch]
  rfl

example {A B : Type} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] :
    IsDistillationOperation .forward (identityForward A B).operation := ⟨identityForward A B, rfl⟩

example {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Matrix I I ℂ) :
    effectZero rho sigma 1 = dMin rho sigma := by
  simp [effectZero, dMin, cfc_one,
    QAlgorithms.Papers.Independent.Dependency50.P35.tr]

example {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ)
    (delta : ℝ) (hdelta : 1 ≤ delta) :
    (0 : Matrix I I ℂ) ∈ acceptanceSet rho delta := by
  refine ⟨⟨Matrix.PosSemidef.zero, ?_⟩, ?_⟩
  · simpa using (Matrix.PosSemidef.one : (1 : Matrix I I ℂ).PosSemidef)
  · simpa [effectProb] using (sub_nonpos.mpr hdelta)

example : embeddedMES (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 = epr 1 := by
  simp only [embeddedMES, Matrix.kronecker, Matrix.one_kronecker_one,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

example {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Matrix I I ℂ) :
    effectZero rho sigma 0 = ⊤ := by
  simp [effectZero, cfc_zero, elog]

example {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ)
    (h : IsDensityMatrix rho) : (1 : Matrix I I ℂ) ∈ acceptanceSet rho 0 := by
  refine ⟨⟨Matrix.PosSemidef.one, ?_⟩, ?_⟩
  · rw [sub_self]
    exact Matrix.PosSemidef.zero
  · simp only [effectProb, Matrix.one_mul, h.2, Complex.one_re, sub_zero, le_refl]

example {I : Type} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) :
    (0 : Matrix I I ℂ) ∈ fidelityBall rho 1 := by
  simp [fidelityBall, IsSubnormalized, rootFidelity, cfc_zero, Matrix.PosSemidef.zero]

example {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : Matrix I I ℂ) (h : ¬ SupportIncluded rho sigma) :
    petzTwo rho sigma = ⊤ := by
  simp [petzTwo, h]

example {A B E : Type} [Fintype B] [Fintype E] :
    marginalAC (0 : Matrix (A × (B × E)) (A × (B × E)) ℂ) = 0 ∧
    marginalAB (0 : Matrix (A × (B × E)) (A × (B × E)) ℂ) = 0 := by
  constructor <;> ext i j <;> simp [marginalAC, marginalAB]

-- Keep the enlarged elaboration budget local to this accepted-definition check.
set_option maxHeartbeats 2000000 in
example {I : Type} [Fintype I] [DecidableEq I]
    (rho sigma : (k : ℕ) → Matrix (PositiveTensorBasis I k) (PositiveTensorBasis I k) ℂ) :
    dependentSpectralInf rho sigma =
      QAlgorithms.Papers.Independent.Support50.P21.spectralInf rho sigma := by
  have mass_eq (gamma : ℝ) : dependentSpectralMass rho sigma gamma =
      QAlgorithms.Papers.Independent.Support50.P21.spectralMass rho sigma gamma := by
    have power_eq (y : ℝ) :
        (algebraMap NNReal ℂ (2 : NNReal)) ^ y = (Real.rpow 2 y : ℂ) := by
      rw [CFC.rpow_algebraMap]
      rfl
    funext k
    unfold dependentSpectralMass
      QAlgorithms.Papers.Independent.Support50.P21.spectralMass
      QAlgorithms.Papers.Independent.Dependency50.P35.tr
    dsimp only
    exact congrArg (fun c : ℂ =>
      (weakPositive (rho k - c • sigma k) * (rho k - c • sigma k)).trace.re)
      (power_eq (((k + 1 : ℕ) : ℝ) * gamma)).symm
  unfold dependentSpectralInf QAlgorithms.Papers.Independent.Support50.P21.spectralInf
  simp only [mass_eq]

end QAlgorithms.Papers.Independent.Advance50.P05


