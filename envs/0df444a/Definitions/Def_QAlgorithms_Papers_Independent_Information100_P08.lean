-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
-- name    : QAlgorithms_Papers_Independent_Information100_P08
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T15:56:27.762012+00:00
-- url     : https://prove2.me/theorems/6e0b7c39-f3b3-4577-b965-368d35350ff5
-- title:
--   Definitions for Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation
-- statement:
--   The objects the formalized statements of *Entanglement -of-formation potentials for feedback-assisted classical communication and randomness distillation* (arXiv:2610.04831) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Ensemble`: PDF p.10, (2.11): a finite ensemble of normalized density matrices; zero weights are allowed.
--   - `ensembleAverage`: PDF p.10: the average of the ensemble, including zero-weight entries.
--   - `PureEnsemble`: PDF p.10, (2.13): normalized pure-state ensembles for the pure convex roof.
--   - `pureAverage`: PDF p.10, (2.13): the matrix represented by a pure-state ensemble.
--   - `IsPure`: PDF p.10: a pure state is the projector of a unit vector, not of an arbitrary vector.
--   - `pureRoof`: PDF p.10, (2.13): the pure convex roof; on density matrices its feasible set is nonempty and its nonnegative, finite scores are bounded below. Only such arguments occur in results.
--   - `formation`: PDF p.10, (2.13): entanglement of formation across exactly the displayed product cut.
--   - `mixedRoof`: PDF p.21, (5.2): the mixed convex roof; all ensemble components may be mixed states.
--   - `canonicalPurification`: PDF p.12, (2.25): canonical purification, with reference first; its transmitted marginal is rho. The coefficient of |i,a> is sqrt(rho)[a,i].
--   - `channelFormation`: PDF p.12, (2.25): formation retained between a reference and the channel output.
--   - `outputHolevo`: PDF p.10, (2.11): output Holevo information for one common input ensemble.
--   - `channelObjective`: PDF p.12, (2.26): Holevo information plus retained formation; mixed inputs are essential.
--   - `channelPotential`: PDF p.12, (2.26): U_F. On positive-dimensional channels the value set is nonempty and lies in [0, log2 d_A]; there is no supremum over unnormalized states.
--   - `channelHolevo`: PDF p.10, (2.12): the ordinary single-use Holevo quantity, not regularized capacity.
--   - `measuredBranch`: PDF p.21, (5.1): the unnormalized B-state after measuring effect M on E.
--   - `measuredCorrelation`: PDF p.21, (5.1): J(E;B), measuring the second factor only. Zero-probability branches are omitted before normalization. POVMs have arbitrary finite cardinality.
--   - `environmentRoof`: PDF p.21, (5.2): G_E is the mixed roof of correlation measured on E.
--   - `leftApply`: PDF p.9: apply an Alice superoperator, leaving every Bob matrix block untouched.
--   - `Instrument`: PDF pp.9,38: a general finite instrument. Each branch has a finite Kraus family, and the aggregate normalization makes the branch sum CPTP and each branch trace nonincreasing. A common Kraus cardinality loses nothing, since finite families can be padded with zeros.
--   - `instrumentObjective`: PDF p.38, (9.10): actual information plus formation retained in Alice's full output. The marginal of B is unchanged by the sum instrument.
--   - `statePotential`: PDF p.38, (9.10): V_F^right, with unrestricted finite retained memory and instruments. On a state in positive dimensions the nonempty value set is bounded by S(B), independently of the retained dimension. This definition does not use Proposition 9.1 as a definition.
--   - `bellVector`: PDF p.42, (9.34): maximally entangled unit vector, in the specified computational basis.
--   - `maximallyMixed`: PDF p.42, (9.34): the maximally mixed state; d>0 is imposed wherever used.
--   - `choi`: PDF p.42: normalized Choi operator, reference first.
--   - `channelPenalty`: PDF p.42, (9.35): the conditional channel penalty.
--   - `constrainedPenalty`: PDF p.42, (9.36): the penalty roof with its fixed average input preserved.
--   - `relocationCut`: PDF p.16: reorder A' B' B to (A' B') B for the comparison cut.
--   - `useOutput`: PDF p.16, (4.5): apply the channel on A inside ((A' A) B'), keeping both memories.
--   - `cqPotential`: PDF p.16, (4.6)-(4.7): cq potential with arbitrary, possibly nonuniform classical label.
--   - `potentialIncrement`: PDF p.16, (4.5): one-use potential increment, computed from the input rather than free data.
--   - `amortizedPotential`: PDF p.18: optimized increment over arbitrary finite positive-dimensional memories.
--   - `flaggedState`: PDF p.10, (2.15): Bob's readable flag, not an unrecorded classical mixture.
--   - `depolarizing`: PDF p.26, (7.1): linear extension of the depolarizing channel to all operators.
--   - `finDamping`: PDF p.30, (8.1): the accepted Bool-indexed damping channel transported to Fin 2. The basis map sends 0 to false (ground) and 1 to true (excited). No new damping formula is introduced; both input and output indices use the same basis map.
--   - `qubitInput`: PDF p.30, (8.2): a qubit input with population t and coherence z.
--   - `formationFunction`: PDF p.27, (7.5): Wootters' binary-entropy function of concurrence.
--   - `determinantEntropy`: PDF p.30, (8.3): entropy as a function of a physical qubit determinant.
--   - `depolarizingObjective`: PDF p.27, (7.6): the actual scalar objective, without restricting inputs to pure states.
--   - `dampingPenalty`: PDF p.31, (8.7): diagonal damping penalty, including t=0,1 and g=0,1.
--   - `thermalChannel`: PDF p.45, (10.12): generalized amplitude damping, with equilibrium excitation n.
--   - `thermalState`: PDF p.46, (10.14): the specific thermal source, defined as the normalized Choi state.
--   - `isotropic`: PDF p.52, (11.2): isotropic state in the same normalized Choi convention.
--   - `thermalPopulation`: PDF p.46, (10.17): output excited population.
--   - `thermalDelta`: PDF p.46, (10.18): pure-input output determinant.
--   - `thermalConcurrence`: PDF p.46, (10.19): nonnegative normalized Choi concurrence.
--   - `thermalPenalty`: PDF p.47, (10.24): conditional thermal penalty on the entire physical domain.
--   - `populationPenalty`: PDF p.47, (10.25): minimum penalty over the nonempty compact determinant interval.
--   - `convexEnvelope`: PDF p.47, (10.25): greatest convex minorant on [0,1], evaluated only there. The constant zero is a minorant for physical parameters, and the set is bounded above pointwise by ell.
--   - `sourcePowersSwapped`: PDF p.39, (9.14): n-copy state with receiver powers first and sender powers second.
--   - `copyCorrelation`: PDF p.39, (9.14): Alice-measured finite-copy correlation; n=1 is included in results.
--   - `firstPair`: PDF p.73, (F.1): first pair marginal, tracing out the entire second pair.
--   - `secondPair`: PDF p.73, (F.1): second pair marginal, tracing out the entire first pair.
--   - `pureConcurrence`: PDF p.66: pure two-qubit concurrence 2|det C|, with C the coefficient matrix.
--   - `concurrence`: PDF p.66: normalized mixed-state concurrence is the pure convex roof.
--   - `twoRoundRate`: PDF p.55, (12.12): two-round rate function, independently of any operational-rate encoding.
--   - `inverseTanh`: PDF p.56: inverse hyperbolic tangent written by its natural-log formula on (-1,1).
--   - `gainCoefficient`: PDF p.56, (12.14): coefficient of s^2; parameters are fixed before remainder constants.
--   - `optimizerPenalty`: PDF p.68, (C.1): scalar penalty whose global minimizers optimize U_F.
--   - `tanhRatio`: PDF p.68, (C.2): continuous extension of atanh(x)/x at zero.
--   - `optimizerSign`: PDF p.69: the continuously extended derivative-sign expression at r=0.
--   - `certificateAlpha`: PDF pp.48,69: exact rational lower-certificate intercept.
--   - `certificateBeta`: PDF pp.48,69: exact rational lower-certificate slope.
--   - `rectangleC`: PDF p.69, (D.3): pure-input determinant term for the fixed thermal example.
--   - `certificateC`: PDF p.69, (D.1): fixed thermal concurrence.
--   - `certificateResidual`: PDF p.69, (D.2): certificate residual, not the truth value of a numerical checker.
--   - `complementaryMarginal`: PDF p.38: the BE marginal of an ABE purification with association (AB)E.
--   - `determinantEntropyDerivative`: PDF p.70, (D.6)-(D.7): derivative of H on its open differentiability interval.
-- source:
--   Entanglement-of-formation potentials for feedback-assisted classical communication and randomness distillation, arXiv:2610.04831v1, https://arxiv.org/abs/2610.04831v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_QuantumInstruments
import Definitions.Def_QAlgorithms_Papers_Independent_Independent2_P01

/-!
Statements from arXiv:2610.04831v1. All dimensions in results are strictly positive.
Paper-local definitions implement the pure and mixed roofs separately. Operational
protocols and the older Upsilon programs are deferred in the accompanying GAPS.json.
No operational capacity is replaced by an algebraic upper bound in this module.
-/

namespace QAlgorithms.Papers.Independent.Information100.P08

open scoped Matrix ComplexConjugate ComplexOrder

noncomputable section

attribute [local instance] Classical.propDecidable

/-- PDF p.10, (2.11): a finite ensemble of normalized density matrices; zero weights are allowed. -/
structure Ensemble (I : Type) [Fintype I] where
  size : ℕ
  prob : Fin size → ℝ
  state : Fin size → Matrix I I ℂ
  nonneg : ∀ x, 0 ≤ prob x
  total : ∑ x, prob x = 1
  density : ∀ x, IsDensityMatrix (state x)

/-- PDF p.10: the average of the ensemble, including zero-weight entries. -/
def ensembleAverage {I : Type} [Fintype I] (e : Ensemble I) : Matrix I I ℂ :=
  ∑ x, e.prob x • e.state x

/-- PDF p.10, (2.13): normalized pure-state ensembles for the pure convex roof. -/
structure PureEnsemble (I : Type) [Fintype I] where
  size : ℕ
  prob : Fin size → ℝ
  vector : Fin size → EuclideanSpace ℂ I
  nonneg : ∀ x, 0 ≤ prob x
  total : ∑ x, prob x = 1
  normalized : ∀ x, ‖vector x‖ = 1

/-- PDF p.10, (2.13): the matrix represented by a pure-state ensemble. -/
def pureAverage {I : Type} [Fintype I] (e : PureEnsemble I) : Matrix I I ℂ :=
  ∑ x, e.prob x • pureDensity (e.vector x)

/-- PDF p.10: a pure state is the projector of a unit vector, not of an arbitrary vector. -/
def IsPure {I : Type} [Fintype I] (rho : Matrix I I ℂ) : Prop :=
  ∃ v : EuclideanSpace ℂ I, ‖v‖ = 1 ∧ rho = pureDensity v

/-- PDF p.10, (2.13): the pure convex roof; on density matrices its feasible set is nonempty
and its nonnegative, finite scores are bounded below. Only such arguments occur in results. -/
def pureRoof {I : Type} [Fintype I] (score : EuclideanSpace ℂ I → ℝ)
    (rho : Matrix I I ℂ) : ℝ :=
  sInf {r | ∃ e : PureEnsemble I, pureAverage e = rho ∧
    r = ∑ x, e.prob x * score (e.vector x)}

/-- PDF p.10, (2.13): entanglement of formation across exactly the displayed product cut. -/
def formation {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  pureRoof (fun v => vnEntropy (traceRight (pureDensity v))) rho

/-- PDF p.21, (5.2): the mixed convex roof; all ensemble components may be mixed states. -/
def mixedRoof {I : Type} [Fintype I] (score : Matrix I I ℂ → ℝ)
    (rho : Matrix I I ℂ) : ℝ :=
  sInf {r | ∃ e : Ensemble I, ensembleAverage e = rho ∧
    r = ∑ x, e.prob x * score (e.state x)}

/-- PDF p.12, (2.25): canonical purification, with reference first; its transmitted marginal
is rho. The coefficient of |i,a> is sqrt(rho)[a,i]. -/
def canonicalPurification {I : Type} [Fintype I] [DecidableEq I]
    (rho : Matrix I I ℂ) : EuclideanSpace ℂ (I × I) :=
  WithLp.toLp 2 fun p => cfc Real.sqrt rho p.2 p.1

/-- PDF p.12, (2.25): formation retained between a reference and the channel output. -/
def channelFormation {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    (N : Superop A B) (rho : Matrix A A ℂ) : ℝ :=
  formation (idTensorSuperop (R := A) N (pureDensity (canonicalPurification rho)))

/-- PDF p.10, (2.11): output Holevo information for one common input ensemble. -/
def outputHolevo {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (N : Superop A B) (e : Ensemble A) : ℝ :=
  vnEntropy (N (ensembleAverage e)) - ∑ x, e.prob x * vnEntropy (N (e.state x))

/-- PDF p.12, (2.26): Holevo information plus retained formation; mixed inputs are essential. -/
def channelObjective {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N : Superop A B) (e : Ensemble A) : ℝ :=
  outputHolevo N e + ∑ x, e.prob x * channelFormation N (e.state x)

/-- PDF p.12, (2.26): U_F. On positive-dimensional channels the value set is nonempty and
lies in [0, log2 d_A]; there is no supremum over unnormalized states. -/
def channelPotential {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N : Superop A B) : ℝ :=
  sSup {r | ∃ e : Ensemble A, r = channelObjective N e}

/-- PDF p.10, (2.12): the ordinary single-use Holevo quantity, not regularized capacity. -/
def channelHolevo {A B : Type} [Fintype A] [Fintype B] [DecidableEq B]
    (N : Superop A B) : ℝ :=
  sSup {r | ∃ e : Ensemble A, r = outputHolevo N e}

/-- PDF p.21, (5.1): the unnormalized B-state after measuring effect M on E. -/
def measuredBranch {B E : Type} [Fintype E]
    (rho : Matrix (B × E) (B × E) ℂ) (M : Matrix E E ℂ) : Matrix B B ℂ :=
  fun b b2 => ∑ e, ∑ e2, M e e2 * rho (b, e2) (b2, e)

/-- PDF p.21, (5.1): J(E;B), measuring the second factor only. Zero-probability branches
are omitted before normalization. POVMs have arbitrary finite cardinality. -/
def measuredCorrelation {B E : Type} [Fintype B] [Fintype E]
    [DecidableEq B] [DecidableEq E] (rho : Matrix (B × E) (B × E) ℂ) : ℝ :=
  sSup {r | ∃ k : ℕ, ∃ M : Fin k → Matrix E E ℂ, IsPOVM M ∧
    r = vnEntropy (traceRight rho) - ∑ x,
      let tau := measuredBranch rho (M x)
      let q := tau.trace.re
      if 0 < q then q * vnEntropy (q⁻¹ • tau) else 0}

/-- PDF p.21, (5.2): G_E is the mixed roof of correlation measured on E. -/
def environmentRoof {B E : Type} [Fintype B] [Fintype E]
    [DecidableEq B] [DecidableEq E] (rho : Matrix (B × E) (B × E) ℂ) : ℝ :=
  mixedRoof measuredCorrelation rho

/-- PDF p.9: apply an Alice superoperator, leaving every Bob matrix block untouched. -/
def leftApply {A C B : Type} (L : Superop A C)
    (rho : Matrix (A × B) (A × B) ℂ) : Matrix (C × B) (C × B) ℂ :=
  fun p q => L (fun a a2 => rho (a, p.2) (a2, q.2)) p.1 q.1

/-- PDF pp.9,38: a general finite instrument. Each branch has a finite Kraus family, and
the aggregate normalization makes the branch sum CPTP and each branch trace nonincreasing.
A common Kraus cardinality loses nothing, since finite families can be padded with zeros. -/
structure Instrument (a c : ℕ) where
  outcomes : ℕ
  rank : ℕ
  kraus : Fin outcomes → Fin rank → Matrix (Fin c) (Fin a) ℂ
  complete : ∑ x, ∑ j, (kraus x j)ᴴ * kraus x j = 1

/-- PDF p.38, (9.10): actual information plus formation retained in Alice's full output.
The marginal of B is unchanged by the sum instrument. -/
def instrumentObjective {a c : ℕ} {B : Type} [Fintype B] [DecidableEq B]
    (M : Instrument a c) (rho : Matrix (Fin a × B) (Fin a × B) ℂ) : ℝ :=
  vnEntropy (traceLeft rho) + ∑ x,
    let tau := leftApply (krausApply (M.kraus x)) rho
    let q := tau.trace.re
    if 0 < q then q * (formation (q⁻¹ • tau) - vnEntropy (traceLeft (q⁻¹ • tau))) else 0

/-- PDF p.38, (9.10): V_F^right, with unrestricted finite retained memory and instruments.
On a state in positive dimensions the nonempty value set is bounded by S(B), independently
of the retained dimension. This definition does not use Proposition 9.1 as a definition. -/
def statePotential {a b : ℕ} (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : ℝ :=
  sSup {r | ∃ c : ℕ, 0 < c ∧ ∃ M : Instrument a c, r = instrumentObjective M rho}

/-- PDF p.42, (9.34): maximally entangled unit vector, in the specified computational basis. -/
def bellVector (d : ℕ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 fun p => if p.1 = p.2 then (Real.sqrt d : ℂ)⁻¹ else 0

/-- PDF p.42, (9.34): the maximally mixed state; d>0 is imposed wherever used. -/
def maximallyMixed (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := (d : ℂ)⁻¹ • 1

/-- PDF p.42: normalized Choi operator, reference first. -/
def choi {a b : ℕ} (N : Superop (Fin a) (Fin b)) :
    Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ :=
  idTensorSuperop N (pureDensity (bellVector a))

/-- PDF p.42, (9.35): the conditional channel penalty. -/
def channelPenalty {a b : ℕ} (N : Superop (Fin a) (Fin b))
    (rho : Matrix (Fin a) (Fin a) ℂ) : ℝ :=
  vnEntropy (N rho) - channelFormation N rho

/-- PDF p.42, (9.36): the penalty roof with its fixed average input preserved. -/
def constrainedPenalty {a b : ℕ} (N : Superop (Fin a) (Fin b))
    (rho : Matrix (Fin a) (Fin a) ℂ) : ℝ :=
  mixedRoof (channelPenalty N) rho

/-- PDF p.16: reorder A' B' B to (A' B') B for the comparison cut. -/
def relocationCut {A C B : Type} (rho : Matrix (A × (C × B)) (A × (C × B)) ℂ) :
    Matrix ((A × C) × B) ((A × C) × B) ℂ :=
  fun p q => rho (p.1.1, (p.1.2, p.2)) (q.1.1, (q.1.2, q.2))

/-- PDF p.16, (4.5): apply the channel on A inside ((A' A) B'), keeping both memories. -/
def useOutput {a b c d : ℕ} (N : Superop (Fin a) (Fin b))
    (rho : Matrix ((Fin c × Fin a) × Fin d) ((Fin c × Fin a) × Fin d) ℂ) :
    Matrix (Fin c × (Fin d × Fin b)) (Fin c × (Fin d × Fin b)) ℂ :=
  fun p q => N (fun x y => rho ((p.1, x), p.2.1) ((q.1, y), q.2.1)) p.2.2 q.2.2

/-- PDF p.16, (4.6)-(4.7): cq potential with arbitrary, possibly nonuniform classical label. -/
def cqPotential {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (k : ℕ) (p : Fin k → ℝ) (rho : Fin k → Matrix (A × B) (A × B) ℂ) : ℝ :=
  vnEntropy (∑ x, p x • traceLeft (rho x)) - ∑ x, p x * vnEntropy (traceLeft (rho x)) +
    ∑ x, p x * formation (rho x)

/-- PDF p.16, (4.5): one-use potential increment, computed from the input rather than free data. -/
def potentialIncrement {a b c d : ℕ} (N : Superop (Fin a) (Fin b))
    (e : Ensemble ((Fin c × Fin a) × Fin d)) : ℝ :=
  cqPotential e.size e.prob (fun x => useOutput N (e.state x)) -
    cqPotential e.size e.prob e.state

/-- PDF p.18: optimized increment over arbitrary finite positive-dimensional memories. -/
def amortizedPotential {a b : ℕ} (N : Superop (Fin a) (Fin b)) : ℝ :=
  sSup {r | ∃ c d : ℕ, 0 < c ∧ 0 < d ∧
    ∃ e : Ensemble ((Fin c × Fin a) × Fin d), r = potentialIncrement N e}

/-- PDF p.10, (2.15): Bob's readable flag, not an unrecorded classical mixture. -/
def flaggedState {A B : Type} [Fintype A] [Fintype B] (e : Ensemble (A × B)) :
    Matrix (A × (B × Fin e.size)) (A × (B × Fin e.size)) ℂ :=
  fun p q => if p.2.2 = q.2.2 then (e.prob p.2.2 : ℂ) * e.state p.2.2 (p.1, p.2.1) (q.1, q.2.1)
    else 0

/-- PDF p.26, (7.1): linear extension of the depolarizing channel to all operators. -/
def depolarizing (d : ℕ) (p : ℝ) : Superop (Fin d) (Fin d) :=
  fun X => (1 - p) • X + p • (X.trace • maximallyMixed d)

/-- PDF p.30, (8.1): the accepted Bool-indexed damping channel transported to Fin 2.
The basis map sends 0 to false (ground) and 1 to true (excited). No new damping
formula is introduced; both input and output indices use the same basis map. -/
def finDamping (g : ℝ) : Superop (Fin 2) (Fin 2) :=
  fun X i j => QAlgorithms.Papers.Independent.Independent2.P01.damping g
    (fun b c => X (cond b 1 0) (cond c 1 0)) (i.val == 1) (j.val == 1)

/-- PDF p.30, (8.2): a qubit input with population t and coherence z. -/
def qubitInput (t : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((1 - t : ℝ) : ℂ), z; conj z, (t : ℂ)]

/-- PDF p.27, (7.5): Wootters' binary-entropy function of concurrence. -/
def formationFunction (c : ℝ) : ℝ := binEntropy2 ((1 + Real.sqrt (1 - c ^ 2)) / 2)

/-- PDF p.30, (8.3): entropy as a function of a physical qubit determinant. -/
def determinantEntropy (v : ℝ) : ℝ := binEntropy2 ((1 - Real.sqrt (1 - 4 * v)) / 2)

/-- PDF p.27, (7.6): the actual scalar objective, without restricting inputs to pure states. -/
def depolarizingObjective (p r : ℝ) : ℝ :=
  1 - binEntropy2 ((1 + (1 - p) * r) / 2) +
    formationFunction (max (1 - 3 * p / 2) 0 * Real.sqrt (1 - r ^ 2))

/-- PDF p.31, (8.7): diagonal damping penalty, including t=0,1 and g=0,1. -/
def dampingPenalty (g t : ℝ) : ℝ :=
  binEntropy2 ((1 - g) * t) - determinantEntropy ((1 - g) * t * (1 - t))

/-- PDF p.45, (10.12): generalized amplitude damping, with equilibrium excitation n. -/
def thermalChannel (g n : ℝ) : Superop (Fin 2) (Fin 2) :=
  fun X =>
    let flip : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
    (1 - n) • finDamping g X + n • (flip * finDamping g (flip * X * flip) * flip)

/-- PDF p.46, (10.14): the specific thermal source, defined as the normalized Choi state. -/
def thermalState : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  choi (thermalChannel (1 / 2) (1 / 10))

/-- PDF p.52, (11.2): isotropic state in the same normalized Choi convention. -/
def isotropic (p : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  choi (depolarizing 2 p)

/-- PDF p.46, (10.17): output excited population. -/
def thermalPopulation (g n t : ℝ) : ℝ := g * n + (1 - g) * t

/-- PDF p.46, (10.18): pure-input output determinant. -/
def thermalDelta (g n t : ℝ) : ℝ := g * (n * (1 - n) + (1 - g) * (t - n) ^ 2)

/-- PDF p.46, (10.19): nonnegative normalized Choi concurrence. -/
def thermalConcurrence (g n : ℝ) : ℝ :=
  max (Real.sqrt (1 - g) - g * Real.sqrt (n * (1 - n))) 0

/-- PDF p.47, (10.24): conditional thermal penalty on the entire physical domain. -/
def thermalPenalty (g n t u : ℝ) : ℝ :=
  determinantEntropy (thermalDelta g n t + (1 - g) * u) -
    determinantEntropy (thermalConcurrence g n ^ 2 * u)

/-- PDF p.47, (10.25): minimum penalty over the nonempty compact determinant interval. -/
def populationPenalty (g n t : ℝ) : ℝ :=
  sInf ((fun u => thermalPenalty g n t u) '' Set.Icc 0 (t * (1 - t)))

/-- PDF p.47, (10.25): greatest convex minorant on [0,1], evaluated only there. The constant
zero is a minorant for physical parameters, and the set is bounded above pointwise by ell. -/
def convexEnvelope (g n t : ℝ) : ℝ :=
  sSup {r | ∃ f : ℝ → ℝ, ConvexOn ℝ (Set.Icc 0 1) f ∧
    (∀ x ∈ Set.Icc 0 1, f x ≤ populationPenalty g n x) ∧ r = f t}

/-- PDF p.39, (9.14): n-copy state with receiver powers first and sender powers second. -/
def sourcePowersSwapped {a b : ℕ} (n : ℕ)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    Matrix ((Fin n → Fin b) × (Fin n → Fin a))
      ((Fin n → Fin b) × (Fin n → Fin a)) ℂ :=
  fun p q => ∏ i, rho (p.2 i, p.1 i) (q.2 i, q.1 i)

/-- PDF p.39, (9.14): Alice-measured finite-copy correlation; n=1 is included in results. -/
def copyCorrelation {a b : ℕ} (n : ℕ)
    (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) : ℝ :=
  measuredCorrelation (sourcePowersSwapped n rho)

/-- PDF p.73, (F.1): first pair marginal, tracing out the entire second pair. -/
def firstPair {A B C D : Type} [Fintype B] [Fintype D]
    (rho : Matrix ((A × B) × (C × D)) ((A × B) × (C × D)) ℂ) :
    Matrix (A × C) (A × C) ℂ :=
  fun p q => ∑ b, ∑ d, rho ((p.1, b), (p.2, d)) ((q.1, b), (q.2, d))

/-- PDF p.73, (F.1): second pair marginal, tracing out the entire first pair. -/
def secondPair {A B C D : Type} [Fintype A] [Fintype C]
    (rho : Matrix ((A × B) × (C × D)) ((A × B) × (C × D)) ℂ) :
    Matrix (B × D) (B × D) ℂ :=
  fun p q => ∑ a, ∑ c, rho ((a, p.1), (c, p.2)) ((a, q.1), (c, q.2))

/-- PDF p.66: pure two-qubit concurrence 2|det C|, with C the coefficient matrix. -/
def pureConcurrence (v : EuclideanSpace ℂ (Fin 2 × Fin 2)) : ℝ :=
  2 * ‖(Matrix.of fun i j => v (i, j)).det‖

/-- PDF p.66: normalized mixed-state concurrence is the pure convex roof. -/
def concurrence (rho : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  pureRoof pureConcurrence rho

/-- PDF p.55, (12.12): two-round rate function, independently of any operational-rate encoding. -/
def twoRoundRate (p s : ℝ) : ℝ :=
  1 - binEntropy2 ((1 + (1 - p) * s) / 2) + binEntropy2 ((1 + s) / 2) -
    binEntropy2 ((1 + Real.sqrt ((1 - p) ^ 2 + (1 - (1 - p) ^ 2) * s ^ 2)) / 2)

/-- PDF p.56: inverse hyperbolic tangent written by its natural-log formula on (-1,1). -/
def inverseTanh (x : ℝ) : ℝ := Real.log ((1 + x) / (1 - x)) / 2

/-- PDF p.56, (12.14): coefficient of s^2; parameters are fixed before remainder constants. -/
def gainCoefficient (p : ℝ) : ℝ :=
  (1 - (1 - p) ^ 2) / (2 * Real.log 2) * (inverseTanh (1 - p) / (1 - p) - 1)

/-- PDF p.68, (C.1): scalar penalty whose global minimizers optimize U_F. -/
def optimizerPenalty (p r : ℝ) : ℝ :=
  binEntropy2 ((1 + (1 - p) * r) / 2) -
    binEntropy2 ((1 + Real.sqrt (1 - (1 - 3 * p / 2) ^ 2 + (1 - 3 * p / 2) ^ 2 * r ^ 2)) / 2)

/-- PDF p.68, (C.2): continuous extension of atanh(x)/x at zero. -/
def tanhRatio (x : ℝ) : ℝ := if x = 0 then 1 else inverseTanh x / x

/-- PDF p.69: the continuously extended derivative-sign expression at r=0. -/
def optimizerSign (p : ℝ) : ℝ :=
  (1 - 3 * p / 2) ^ 2 * tanhRatio (Real.sqrt (1 - (1 - 3 * p / 2) ^ 2)) - (1 - p) ^ 2

/-- PDF pp.48,69: exact rational lower-certificate intercept. -/
def certificateAlpha : ℝ := 4287673 / 10000000

/-- PDF pp.48,69: exact rational lower-certificate slope. -/
def certificateBeta : ℝ := 7391729 / 10000000

/-- PDF p.69, (D.3): pure-input determinant term for the fixed thermal example. -/
def rectangleC (t : ℝ) : ℝ := 9 / 200 + (t - 1 / 10) ^ 2 / 4

/-- PDF p.69, (D.1): fixed thermal concurrence. -/
def certificateC : ℝ := 1 / Real.sqrt 2 - 3 / 20

/-- PDF p.69, (D.2): certificate residual, not the truth value of a numerical checker. -/
def certificateResidual (t u : ℝ) : ℝ :=
  thermalPenalty (1 / 2) (1 / 10) t u - certificateAlpha - certificateBeta * (t - 1 / 2)

/-! Sanity examples concern definition normalization and ordering, not proofs of the paper results. -/

example {A B : Type} [Fintype B] (rho : Matrix (A × B) (A × B) ℂ) (a a2 : A) :
    traceRight rho a a2 = ∑ b, rho (a, b) (a2, b) := rfl

example {A C B : Type} (L : Superop A C) (rho : Matrix (A × B) (A × B) ℂ)
    (c c2 : C) (b b2 : B) :
    leftApply L rho (c, b) (c2, b2) = L (fun a a2 => rho (a, b) (a2, b2)) c c2 := rfl

example {A C B : Type} (rho : Matrix (A × (C × B)) (A × (C × B)) ℂ)
    (a a2 : A) (c c2 : C) (b b2 : B) :
    relocationCut rho ((a, c), b) ((a2, c2), b2) = rho (a, (c, b)) (a2, (c2, b2)) := rfl

example : determinantEntropy 0 = 0 := by
  simp [determinantEntropy, binEntropy2]

example : determinantEntropy (1 / 4) = 1 := by
  norm_num [determinantEntropy]
  rw [binEntropy2, show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
  exact div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

example : thermalPopulation (1 / 2) (1 / 10) (1 / 2) = 3 / 10 := by
  norm_num [thermalPopulation]

example : thermalDelta (1 / 2) (1 / 10) (1 / 2) = 17 / 200 := by
  norm_num [thermalDelta]

example : tanhRatio 0 = 1 := by simp [tanhRatio]

example : certificateAlpha = 0.4287673 ∧ certificateBeta = 0.7391729 := by
  norm_num [certificateAlpha, certificateBeta]

example {a b : ℕ} (rho : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    (x y : (Fin 0 → Fin b) × (Fin 0 → Fin a)) : sourcePowersSwapped 0 rho x y = 1 := by
  simp [sourcePowersSwapped]

example (p : ℝ) : depolarizing 2 p (maximallyMixed 2) = maximallyMixed 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [depolarizing, maximallyMixed, Matrix.trace, Fin.sum_univ_two] <;> ring

/-- The one-dimensional Bell definition has unit amplitude. -/
example : bellVector 1 (0, 0) = 1 := by simp [bellVector]

/-- A normalized single-Kraus identity instrument exists in every finite dimension. -/
example (a : ℕ) : Nonempty (Instrument a a) := by
  exact ⟨⟨1, 1, fun _ _ => 1, by simp⟩⟩

/-- The adapter's ground-ground entry is exactly the accepted channel's false-false entry. -/
example (g : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    finDamping g X 0 0 = QAlgorithms.Papers.Independent.Independent2.P01.damping g
      (fun b c => X (cond b 1 0) (cond c 1 0)) false false := rfl

/-- The imported square-output branch agrees with its accepted Kraus action. -/
example {I O : Type} [Fintype I] [DecidableEq I] [Fintype O]
    (M : QAlgorithms.CopyMeasurements.QuantumInstrument I O) (x : O)
    (X : Matrix I I ℂ) :
    QAlgorithms.CopyMeasurements.instrumentBranch M x X = krausApply (M.kraus x) X := rfl

/-- PDF p.38: the BE marginal of an ABE purification with association (AB)E. -/
def complementaryMarginal {a b e : ℕ}
    (psi : Matrix ((Fin a × Fin b) × Fin e) ((Fin a × Fin b) × Fin e) ℂ) :
    Matrix (Fin b × Fin e) (Fin b × Fin e) ℂ :=
  fun p q => ∑ x, psi ((x, p.1), p.2) ((x, q.1), q.2)

/-- PDF p.70, (D.6)-(D.7): derivative of H on its open differentiability interval. -/
def determinantEntropyDerivative (v : ℝ) : ℝ :=
  2 * inverseTanh (Real.sqrt (1 - 4 * v)) / (Real.sqrt (1 - 4 * v) * Real.log 2)

end

end QAlgorithms.Papers.Independent.Information100.P08


