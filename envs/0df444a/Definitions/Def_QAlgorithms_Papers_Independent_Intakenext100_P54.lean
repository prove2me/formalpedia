-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P54
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P54
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T06:32:54.725541+00:00
-- url     : https://prove2.me/theorems/f5bb3d96-0fc7-4e70-a163-71e894d347df
-- title:
--   Definitions for Remote preparation of quantum states
-- statement:
--   The objects the formalized statements of *Remote preparation of quantum states* (arXiv:quant-ph/0307100) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `RSPVector`: Normalized vectors in a specified finite register (PDF pp.1–3).
--   - `bar`: Entrywise conjugation in the entanglement basis (PDF pp.2–3).
--   - `randomise`: Averaging unitary conjugations (PDF p.3, equation (1)).
--   - `Randomising`: The operator-order assertion of equation (1), for every density operator (PDF p.3).
--   - `randomisingBound`: The printed randomisation cardinality bound (PDF p.3), with logarithm base two.
--   - `piGood`: Good effects of protocol Pi. Conjugation is on the target alone (PDF p.3).
--   - `piEffect`: Complete POVM alphabet, including the common failure flag (PDF pp.3–4).
--   - `piBranch`: Unnormalized receiver branch after steering and the announced correction (PDF p.4). On a maximally entangled pair the steered operator is the effect's transpose divided by D.
--   - `RSPCode`: One-way finite RSP code with input-independent maximally entangled rank S resource, input-dependent Alice POVM, and fixed CPTP Bob decoder per message (PDF pp.4–5). The source's support costs are log2 K and log2 S.
--   - `RSPCode.branch`: Unnormalized decoded message branch, without conditioning on its probability (PDF p.5).
--   - `RSPCode.output`: Averaged output of a finite one-way code (PDF p.5).
--   - `RSPCode.ExactWithError`: Probabilistic exact preparation: one input-independent success set, exact conditional good outputs, and a uniform failure bound (PDF p.2).
--   - `pureWordVector`: Product target with the source's ordered tensor factors (PDF p.5).
--   - `pureAverageOverlap`: Global average squared fidelity, equation (2), rather than the local criterion (3) (PDF p.5).
--   - `RSPPureAchievable`: One-way achievable rates with both slacks before the blocklength threshold (PDF p.5).
--   - `pureOperational`: Extended nonnegative operational cost: an infeasible rate has value infinity (PDF pp.5–6).
--   - `AuxChannel`: Finite but arbitrarily large classical auxiliary alphabet (PDF p.6, equation (5)).
--   - `auxWeight`: Auxiliary marginal probability (PDF p.6).
--   - `conditionalBob`: Conditional Bob state; a zero-probability auxiliary uses the maximally mixed state. Its entropy is multiplied by zero, so this convention does not affect any information (PDF p.6).
--   - `auxiliaryBobEntropy`: S(B|C), averaged over the classical auxiliary (PDF pp.6,10).
--   - `labelAuxInfo`: I(X;C) for the source's stochastic auxiliary channel (PDF p.6).
--   - `labelBobAuxInfo`: I(X;BC) = I(X;C)+S(B|C)-S(B|X), evaluated from the specified cq state. For pure Bob targets the last term vanishes; for entangled targets it must be retained (PDF pp.6,10).
--   - `rspSingleLetter`: Single-letter optimisation with no unsupported m+1 cardinality restriction. The empty feasible set has infimum infinity (PDF pp.6,10).
--   - `rspMinimumAttained`: Actual attainment whenever the single-letter feasible value is finite; this records "min" rather than merely replacing it with an infimum (PDF pp.6,10).
--   - `BipartiteEnsemble`: Pure bipartite ensemble: the full chosen purification is the target (PDF p.8).
--   - `bobStates`: Receiver marginals of the fixed purifications (PDF pp.8–10).
--   - `BipartiteCode`: General one-way entangled RSP: input-dependent Alice CP instrument, with only its SUM trace preserving; Bob's decoder is arbitrary CPTP (PDF p.8). Padding permits a common finite number L of Kraus operators per branch.
--   - `BipartiteCode.output`: Full joint output, sum_j (M_j^I tensor T_j)(Phi_S); no Alice output is discarded (PDF p.8).
--   - `bipWord`: IID bipartite target, with Alice factors grouped together and Bob factors grouped together (PDF p.8).
--   - `bipAverage`: Global average overlap with the chosen bipartite purification (PDF pp.8–9).
--   - `BipartiteAchievable`: One-way entangled achievable rates with the source's global criterion (PDF pp.8–9).
--   - `bipOperational`: Entangled operational curve, infinity when no finite rate pair is achievable (PDF p.9).
--   - `bobAverageEntropy`: Entropy of the receiver's average state, not the average of the individual entropies (PDF p.9).
--   - `bobHolevo`: Holevo information of the receiver marginal ensemble (PDF p.9).
--   - `piRecord`: Complete receiver record after replacing Pi's failure message uniformly by a good label. The failure flag stays private to Alice (PDF pp.12–13).
--   - `piSimulator`: Linear CPTP simulator with one ACTUAL receiver output specimen as input. Conjugating U, rather than the unknown specimen, makes this a linear channel (PDF p.13).
--   - `piApproxOutput`: Actual averaged output decoded from the uniformly replaced failure record (PDF p.13).
--   - `marginalAverageFidelity`: Bob's global average mixed-state squared fidelity after discarding Alice's output (PDF p.13).
--   - `SymmetricGaussian`: Independent centered real and imaginary coordinates of a symmetric complex Gaussian. Each real coordinate has variance s2/(2D), so the total expected norm square is s2. Definition 22's printed mu_j is read as zero by its immediately preceding prose (PDF p.14).
--   - `momentLog`: Logarithm of a nonnegative exponential moment, including divergence and zero. It never turns a divergent Bochner integral into zero (PDF p.14).
--   - `squaredGaussianRate`: Cramer transform of a squared real centered Gaussian, defined from the moment integral and supremum, not from the asserted closed form (PDF p.14).
--   - `elementaryRate`: Extended endpoint of A3: ln(0) is minus infinity, not Lean's Real.log 0 = 0 (PDF p.14).
--   - `VisibleCode`: Universal visible quantum-classical compression with a pure quantum codeword and a fixed CPTP decoder per classical message (PDF pp.15–16). All code sizes are fixed support sizes.
--   - `VisibleCode.output`: Decoding the jointly visible quantum and classical description (PDF p.15).
-- source:
--   Remote preparation of quantum states, arXiv:quant-ph/0307100v3, https://arxiv.org/abs/quant-ph/0307100v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P53
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P38

/-!
Statements from Bennett, Hayden, Leung, Shor and Winter,
Remote preparation of quantum states, quant-ph/0307100v3.
All logarithms in resource bounds are base two. New definitions are paper-local.
Fidelity, iid probabilities, finite pure ensembles and classical entropy reuse pinned accepted
modules whose exact source bodies were hash-verified before reuse.
Theorem 2 and Lemma 4 use the small-error domains justified by their proofs.
Theorem 5 charges the failure message as well as all good messages.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace QAlgorithms.Papers.Independent.Intakenext100.P54

open QAlgorithms.Papers.Independent.Information100.P03 (PureEnsemble)
open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)
open QAlgorithms.Papers.Independent.Dependency50.P07 (wordProb)
open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)
open QAlgorithms.Papers.Independent.Claimed50.P38 (tensorSuperop)

/-- Normalized vectors in a specified finite register (PDF pp.1–3). -/
abbrev RSPVector (O : Type*) [Fintype O] := {v : EuclideanSpace ℂ O // ‖v‖ = 1}

/-- Entrywise conjugation in the entanglement basis (PDF pp.2–3). -/
def bar {O : Type*} (M : Matrix O O ℂ) : Matrix O O ℂ := fun a b => conj (M a b)

/-- Averaging unitary conjugations (PDF p.3, equation (1)). -/
def randomise {D K : ℕ} (U : Fin K → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  ((K : ℂ)⁻¹) • ∑ k, (U k : Matrix (Fin D) (Fin D) ℂ) * rho *
    (U k : Matrix (Fin D) (Fin D) ℂ)ᴴ

/-- The operator-order assertion of equation (1), for every density operator (PDF p.3). -/
def Randomising {D K : ℕ} (U : Fin K → Matrix.unitaryGroup (Fin D) ℂ) (eps : ℝ) : Prop :=
  ∀ rho : Matrix (Fin D) (Fin D) ℂ, IsDensityMatrix rho →
    (randomise U rho - (((1 - eps) / D : ℝ) : ℂ) • 1).PosSemidef ∧
    ((((1 + eps) / D : ℝ) : ℂ) • 1 - randomise U rho).PosSemidef

/-- The printed randomisation cardinality bound (PDF p.3), with logarithm base two. -/
def randomisingBound (D : ℕ) (eps : ℝ) : ℝ :=
  (10 / eps) ^ 2 * D * Real.logb 2 (20 * D / eps)

/-- Good effects of protocol Pi. Conjugation is on the target alone (PDF p.3). -/
def piGood {D K : ℕ} (U : Fin K → Matrix.unitaryGroup (Fin D) ℂ)
    (eps : ℝ) (psi : RSPVector (Fin D)) (k : Fin K) : Matrix (Fin D) (Fin D) ℂ :=
  ((D : ℂ) / (K * (1 + (eps : ℂ)))) •
    ((U k : Matrix (Fin D) (Fin D) ℂ) * bar (pureDensity psi.val) *
      (U k : Matrix (Fin D) (Fin D) ℂ)ᴴ)

/-- Complete POVM alphabet, including the common failure flag (PDF pp.3–4). -/
def piEffect {D K : ℕ} (U : Fin K → Matrix.unitaryGroup (Fin D) ℂ)
    (eps : ℝ) (psi : RSPVector (Fin D)) : Option (Fin K) → Matrix (Fin D) (Fin D) ℂ
  | some k => piGood U eps psi k
  | none => 1 - ∑ k, piGood U eps psi k

/-- Unnormalized receiver branch after steering and the announced correction (PDF p.4).
On a maximally entangled pair the steered operator is the effect's transpose divided by D. -/
def piBranch {D K : ℕ} (U : Fin K → Matrix.unitaryGroup (Fin D) ℂ)
    (eps : ℝ) (psi : RSPVector (Fin D)) : Option (Fin K) → Matrix (Fin D) (Fin D) ℂ
  | some k => (U k : Matrix (Fin D) (Fin D) ℂ).transpose *
      (((D : ℂ)⁻¹) • (piGood U eps psi k).transpose) *
        ((U k : Matrix (Fin D) (Fin D) ℂ).transpose)ᴴ
  | none => ((D : ℂ)⁻¹) • (piEffect U eps psi none).transpose

/-- Sanity: the failure effect completes precisely the family of good effects. -/
example {D K : ℕ} (U : Fin K → Matrix.unitaryGroup (Fin D) ℂ)
    (eps : ℝ) (psi : RSPVector (Fin D)) :
    piEffect U eps psi none + ∑ k, piEffect U eps psi (some k) = 1 := by
  simp only [piEffect]
  exact sub_add_cancel _ _

/-- One-way finite RSP code with input-independent maximally entangled rank S resource,
input-dependent Alice POVM, and fixed CPTP Bob decoder per message (PDF pp.4–5).
The source's support costs are log2 K and log2 S. -/
structure RSPCode (Input O : Type*) [Fintype O] [DecidableEq O] where
  S : ℕ
  Spos : 0 < S
  K : ℕ
  Kpos : 0 < K
  effect : Input → Fin K → Matrix (Fin S) (Fin S) ℂ
  povm : ∀ i, IsPOVM (effect i)
  decoder : Fin K → Superop (Fin S) O
  channel : ∀ j, IsChannel (decoder j)

/-- Unnormalized decoded message branch, without conditioning on its probability (PDF p.5). -/
def RSPCode.branch {Input O : Type*} [Fintype O] [DecidableEq O]
    (P : RSPCode Input O) (i : Input) (j : Fin P.K) : Matrix O O ℂ :=
  P.decoder j (((P.S : ℂ)⁻¹) • (P.effect i j).transpose)

/-- Averaged output of a finite one-way code (PDF p.5). -/
def RSPCode.output {Input O : Type*} [Fintype O] [DecidableEq O]
    (P : RSPCode Input O) (i : Input) : Matrix O O ℂ := ∑ j, P.branch i j

/-- Probabilistic exact preparation: one input-independent success set, exact conditional good
outputs, and a uniform failure bound (PDF p.2). -/
def RSPCode.ExactWithError {O : Type*} [Fintype O] [DecidableEq O]
    (P : RSPCode (RSPVector O) O) (eps : ℝ) : Prop :=
  ∃ good : Finset (Fin P.K), ∀ psi : RSPVector O,
    (∀ j ∈ good, P.branch psi j = ((P.branch psi j).trace.re : ℂ) • pureDensity psi.val) ∧
    1 - eps ≤ ∑ j ∈ good, (P.branch psi j).trace.re

/-- Product target with the source's ordered tensor factors (PDF p.5). -/
def pureWordVector {d : ℕ} (E : PureEnsemble (Fin d)) (n : ℕ) (w : Fin n → Fin E.count) :
    EuclideanSpace ℂ (Fin n → Fin d) :=
  WithLp.toLp 2 fun x => ∏ t, E.vector (w t) (x t)

/-- Global average squared fidelity, equation (2), rather than the local criterion (3) (PDF p.5). -/
def pureAverageOverlap {d : ℕ} (E : PureEnsemble (Fin d)) (n : ℕ)
    (P : RSPCode (Fin n → Fin E.count) (Fin n → Fin d)) : ℝ :=
  ∑ w, wordProb E.weight n w * (pureDensity (pureWordVector E n w) * P.output w).trace.re

/-- One-way achievable rates with both slacks before the blocklength threshold (PDF p.5). -/
def RSPPureAchievable {d : ℕ} (E : PureEnsemble (Fin d)) (R ent : ℝ) : Prop :=
  0 ≤ R ∧ 0 ≤ ent ∧ ∀ eps : ℝ, 0 < eps → ∀ delta : ℝ, 0 < delta →
    ∃ nzero : ℕ, 0 < nzero ∧ ∀ n ≥ nzero,
      ∃ P : RSPCode (Fin n → Fin E.count) (Fin n → Fin d),
        1 - eps ≤ pureAverageOverlap E n P ∧
        Real.logb 2 P.K / n ≤ R + delta ∧ Real.logb 2 P.S / n ≤ ent + delta

/-- Extended nonnegative operational cost: an infeasible rate has value infinity (PDF pp.5–6). -/
def pureOperational {d : ℕ} (E : PureEnsemble (Fin d)) (R : ℝ) : ℝ≥0∞ :=
  sInf {v | ∃ ent : ℝ, RSPPureAchievable E R ent ∧ v = ENNReal.ofReal ent}

/-- Finite but arbitrarily large classical auxiliary alphabet (PDF p.6, equation (5)). -/
structure AuxChannel (m k : ℕ) where
  prob : Fin m → Fin k → ℝ
  nonneg : ∀ i j, 0 ≤ prob i j
  total : ∀ i, ∑ j, prob i j = 1

/-- Auxiliary marginal probability (PDF p.6). -/
def auxWeight {m k : ℕ} (p : Fin m → ℝ) (c : AuxChannel m k) (j : Fin k) : ℝ :=
  ∑ i, p i * c.prob i j

/-- Conditional Bob state; a zero-probability auxiliary uses the maximally mixed state.
Its entropy is multiplied by zero, so this convention does not affect any information (PDF p.6). -/
def conditionalBob {m k d : ℕ} (p : Fin m → ℝ)
    (rho : Fin m → Matrix (Fin d) (Fin d) ℂ) (c : AuxChannel m k) (j : Fin k) :
    Matrix (Fin d) (Fin d) ℂ :=
  if auxWeight p c j = 0 then ((d : ℂ)⁻¹) • 1
  else ∑ i, ((p i * c.prob i j / auxWeight p c j : ℝ) : ℂ) • rho i

/-- S(B|C), averaged over the classical auxiliary (PDF pp.6,10). -/
def auxiliaryBobEntropy {m k d : ℕ} (p : Fin m → ℝ)
    (rho : Fin m → Matrix (Fin d) (Fin d) ℂ) (c : AuxChannel m k) : ℝ :=
  ∑ j, auxWeight p c j * vnEntropy (conditionalBob p rho c j)

/-- I(X;C) for the source's stochastic auxiliary channel (PDF p.6). -/
def labelAuxInfo {m k : ℕ} (p : Fin m → ℝ) (c : AuxChannel m k) : ℝ :=
  classicalEntropy p - ∑ j, auxWeight p c j *
    classicalEntropy (fun i => p i * c.prob i j / auxWeight p c j)

/-- I(X;BC) = I(X;C)+S(B|C)-S(B|X), evaluated from the specified cq state.
For pure Bob targets the last term vanishes; for entangled targets it must be retained (PDF pp.6,10). -/
def labelBobAuxInfo {m k d : ℕ} (p : Fin m → ℝ)
    (rho : Fin m → Matrix (Fin d) (Fin d) ℂ) (c : AuxChannel m k) : ℝ :=
  labelAuxInfo p c + auxiliaryBobEntropy p rho c - ∑ i, p i * vnEntropy (rho i)

/-- Single-letter optimisation with no unsupported m+1 cardinality restriction.
The empty feasible set has infimum infinity (PDF pp.6,10). -/
def rspSingleLetter {m d : ℕ} (p : Fin m → ℝ)
    (rho : Fin m → Matrix (Fin d) (Fin d) ℂ) (R : ℝ) : ℝ≥0∞ :=
  sInf {v | ∃ k : ℕ, ∃ c : AuxChannel m k,
    labelBobAuxInfo p rho c ≤ R ∧ v = ENNReal.ofReal (auxiliaryBobEntropy p rho c)}

/-- Actual attainment whenever the single-letter feasible value is finite; this records
"min" rather than merely replacing it with an infimum (PDF pp.6,10). -/
def rspMinimumAttained {m d : ℕ} (p : Fin m → ℝ)
    (rho : Fin m → Matrix (Fin d) (Fin d) ℂ) (R : ℝ) : Prop :=
  rspSingleLetter p rho R ≠ ⊤ → ∃ k : ℕ, ∃ c : AuxChannel m k,
    labelBobAuxInfo p rho c ≤ R ∧
    ENNReal.ofReal (auxiliaryBobEntropy p rho c) = rspSingleLetter p rho R

/-- Pure bipartite ensemble: the full chosen purification is the target (PDF p.8). -/
structure BipartiteEnsemble (m a b : ℕ) where
  prob : Fin m → ℝ
  nonneg : ∀ i, 0 ≤ prob i
  total : ∑ i, prob i = 1
  state : Fin m → RSPVector (Fin a × Fin b)

/-- Receiver marginals of the fixed purifications (PDF pp.8–10). -/
def bobStates {m a b : ℕ} (E : BipartiteEnsemble m a b) (i : Fin m) :
    Matrix (Fin b) (Fin b) ℂ := traceLeft (pureDensity (E.state i).val)

/-- General one-way entangled RSP: input-dependent Alice CP instrument, with only its SUM
trace preserving; Bob's decoder is arbitrary CPTP (PDF p.8). Padding permits a common finite
number L of Kraus operators per branch. -/
structure BipartiteCode (Input A B : Type*) [Fintype A] [Fintype B] [DecidableEq B] where
  S : ℕ
  Spos : 0 < S
  K : ℕ
  Kpos : 0 < K
  L : ℕ
  alice : Input → Fin K → Fin L → Matrix A (Fin S) ℂ
  complete : ∀ i, ∑ j, ∑ l, (alice i j l)ᴴ * alice i j l = 1
  bob : Fin K → Superop (Fin S) B
  channel : ∀ j, IsChannel (bob j)

/-- Full joint output, sum_j (M_j^I tensor T_j)(Phi_S); no Alice output is discarded (PDF p.8). -/
def BipartiteCode.output {Input A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (P : BipartiteCode Input A B) (i : Input) : Matrix (A × B) (A × B) ℂ :=
  letI : Nonempty (Fin P.S) := ⟨⟨0, P.Spos⟩⟩
  let s : Fin P.S := ⟨0, P.Spos⟩
  -- The frozen tensor operation has square registers. Extract each rectangular output
  -- coefficient through constant-entry square maps; its matrix-unit expansion is unchanged.
  ∑ j, fun u v =>
    tensorSuperop
      (fun X (_ _ : Fin P.S) => krausApply (P.alice i j) X u.1 v.1)
      (fun X (_ _ : Fin P.S) => P.bob j X u.2 v.2)
      (pureDensity (finiteMaxEntangled (Fin P.S))) (s, s) (s, s)

/-- Coefficient extraction through the imported square tensor operation retains every
matrix unit, including off-diagonal entries of entangled inputs (PDF p.8). -/
example {S A B : Type*} [Fintype S] [DecidableEq S]
    (left : Superop S A) (right : Superop S B)
    (X : Matrix (S × S) (S × S) ℂ) (s : S) (u v : A × B) :
    tensorSuperop (fun Y (_ _ : S) => left Y u.1 v.1)
      (fun Y (_ _ : S) => right Y u.2 v.2) X (s, s) (s, s) =
      ∑ x : S × S, ∑ y : S × S, X x y *
        left (Matrix.single x.1 y.1 1) u.1 v.1 *
        right (Matrix.single x.2 y.2 1) u.2 v.2 := by
  rfl

/-- IID bipartite target, with Alice factors grouped together and Bob factors grouped together
(PDF p.8). -/
def bipWord {m a b : ℕ} (E : BipartiteEnsemble m a b) (n : ℕ) (w : Fin n → Fin m) :
    EuclideanSpace ℂ ((Fin n → Fin a) × (Fin n → Fin b)) :=
  WithLp.toLp 2 fun x => ∏ t, (E.state (w t)).val (x.1 t, x.2 t)

/-- Global average overlap with the chosen bipartite purification (PDF pp.8–9). -/
def bipAverage {m a b : ℕ} (E : BipartiteEnsemble m a b) (n : ℕ)
    (P : BipartiteCode (Fin n → Fin m) (Fin n → Fin a) (Fin n → Fin b)) : ℝ :=
  ∑ w, wordProb E.prob n w * (pureDensity (bipWord E n w) * P.output w).trace.re

/-- One-way entangled achievable rates with the source's global criterion (PDF pp.8–9). -/
def BipartiteAchievable {m a b : ℕ} (E : BipartiteEnsemble m a b) (R ent : ℝ) : Prop :=
  0 ≤ R ∧ 0 ≤ ent ∧ ∀ eps : ℝ, 0 < eps → ∀ delta : ℝ, 0 < delta →
    ∃ nzero : ℕ, 0 < nzero ∧ ∀ n ≥ nzero,
      ∃ P : BipartiteCode (Fin n → Fin m) (Fin n → Fin a) (Fin n → Fin b),
        1 - eps ≤ bipAverage E n P ∧
        Real.logb 2 P.K / n ≤ R + delta ∧ Real.logb 2 P.S / n ≤ ent + delta

/-- Entangled operational curve, infinity when no finite rate pair is achievable (PDF p.9). -/
def bipOperational {m a b : ℕ} (E : BipartiteEnsemble m a b) (R : ℝ) : ℝ≥0∞ :=
  sInf {v | ∃ ent : ℝ, BipartiteAchievable E R ent ∧ v = ENNReal.ofReal ent}

/-- Entropy of the receiver's average state, not the average of the individual entropies (PDF p.9). -/
def bobAverageEntropy {m a b : ℕ} (E : BipartiteEnsemble m a b) : ℝ :=
  vnEntropy (∑ i, (E.prob i : ℂ) • bobStates E i)

/-- Holevo information of the receiver marginal ensemble (PDF p.9). -/
def bobHolevo {m a b : ℕ} (E : BipartiteEnsemble m a b) : ℝ :=
  bobAverageEntropy E - ∑ i, E.prob i * vnEntropy (bobStates E i)

/-- Complete receiver record after replacing Pi's failure message uniformly by a good label.
The failure flag stays private to Alice (PDF pp.12–13). -/
def piRecord {D K : ℕ} (U : Fin K → Matrix.unitaryGroup (Fin D) ℂ)
    (eps : ℝ) (psi : RSPVector (Fin D)) : Matrix (Fin K × Fin D) (Fin K × Fin D) ℂ :=
  fun x y => if x.1 = y.1 then
    (((D : ℂ)⁻¹) • (piGood U eps psi x.1).transpose +
      (((K : ℂ) * D)⁻¹) • (piEffect U eps psi none).transpose) x.2 y.2
    else 0

/-- Linear CPTP simulator with one ACTUAL receiver output specimen as input.
Conjugating U, rather than the unknown specimen, makes this a linear channel (PDF p.13). -/
def piSimulator {D K : ℕ} (U : Fin K → Matrix.unitaryGroup (Fin D) ℂ) :
    Superop (Fin D) (Fin K × Fin D) :=
  fun rho x y => if x.1 = y.1 then
    (((K : ℂ)⁻¹) • (bar (U x.1 : Matrix (Fin D) (Fin D) ℂ) * rho *
      (U x.1 : Matrix (Fin D) (Fin D) ℂ).transpose)) x.2 y.2 else 0

/-- Actual averaged output decoded from the uniformly replaced failure record (PDF p.13). -/
def piApproxOutput {D K : ℕ} (U : Fin K → Matrix.unitaryGroup (Fin D) ℂ)
    (eps : ℝ) (psi : RSPVector (Fin D)) : Matrix (Fin D) (Fin D) ℂ :=
  ∑ k, (U k : Matrix (Fin D) (Fin D) ℂ).transpose *
    (Matrix.of fun a b => piRecord U eps psi (k, a) (k, b)) *
    ((U k : Matrix (Fin D) (Fin D) ℂ).transpose)ᴴ

/-- Bob's global average mixed-state squared fidelity after discarding Alice's output (PDF p.13). -/
def marginalAverageFidelity {m a b : ℕ} (E : BipartiteEnsemble m a b) (n : ℕ)
    (P : BipartiteCode (Fin n → Fin m) (Fin n → Fin a) (Fin n → Fin b)) : ℝ :=
  ∑ w, wordProb E.prob n w * fidelity (traceLeft (pureDensity (bipWord E n w)))
    (traceLeft (P.output w))

/-- Independent centered real and imaginary coordinates of a symmetric complex Gaussian.
Each real coordinate has variance s2/(2D), so the total expected norm square is s2.
Definition 22's printed mu_j is read as zero by its immediately preceding prose (PDF p.14). -/
def SymmetricGaussian {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega)
    (D : ℕ) (s2 : ℝ≥0) (G : Omega → EuclideanSpace ℂ (Fin D)) : Prop :=
  Measurable G ∧
    let coord : (Fin D × Bool) → Omega → ℝ := fun j w =>
      if j.2 then (G w j.1).im else (G w j.1).re
    iIndepFun coord mu ∧
      ∀ j, Measure.map (coord j) mu = gaussianReal 0 (s2 / (2 * D))

/-- Logarithm of a nonnegative exponential moment, including divergence and zero.
It never turns a divergent Bochner integral into zero (PDF p.14). -/
def momentLog (z : ℝ≥0∞) : EReal :=
  if z = ⊤ then ⊤ else if z = 0 then ⊥ else (Real.log z.toReal : EReal)

/-- Cramer transform of a squared real centered Gaussian, defined from the moment integral
and supremum, not from the asserted closed form (PDF p.14). -/
def squaredGaussianRate (s2 : ℝ≥0) (x : ℝ) : EReal :=
  ⨆ y : ℝ, ((y * x : ℝ) : EReal) - momentLog
    (∫⁻ t : ℝ, ENNReal.ofReal (Real.exp (y * t ^ 2)) ∂gaussianReal 0 s2)

/-- Sanity: a divergent moment has infinite logarithm. -/
example : momentLog ⊤ = ⊤ := by simp [momentLog]

/-- Sanity: the unit moment has zero logarithm. -/
example : momentLog 1 = 0 := by simp [momentLog]

/-- Extended endpoint of A3: ln(0) is minus infinity, not Lean's Real.log 0 = 0 (PDF p.14). -/
def elementaryRate (xi : ℝ) : EReal :=
  if xi = -1 then ⊤ else (((xi - Real.log (1 + xi)) / (2 * Real.log 2) : ℝ) : EReal)

/-- Sanity: the left endpoint is infinite. -/
example : elementaryRate (-1) = ⊤ := by simp [elementaryRate]

/-- Universal visible quantum-classical compression with a pure quantum codeword and a fixed
CPTP decoder per classical message (PDF pp.15–16). All code sizes are fixed support sizes. -/
structure VisibleCode (D : ℕ) where
  S : ℕ
  Spos : 0 < S
  K : ℕ
  Kpos : 0 < K
  quantum : RSPVector (Fin D) → RSPVector (Fin S)
  message : RSPVector (Fin D) → Fin K
  decoder : Fin K → Superop (Fin S) (Fin D)
  channel : ∀ j, IsChannel (decoder j)

/-- Decoding the jointly visible quantum and classical description (PDF p.15). -/
def VisibleCode.output {D : ℕ} (P : VisibleCode D) (psi : RSPVector (Fin D)) :
    Matrix (Fin D) (Fin D) ℂ := P.decoder (P.message psi) (pureDensity (P.quantum psi).val)

/-- Sanity: tensor-product word probability on the empty word is one. -/
example {m : ℕ} (p : Fin m → ℝ) (w : Fin 0 → Fin m) : wordProb p 0 w = 1 := by
  simp [wordProb]

/-- Sanity: the auxiliary register's impossible outcome contributes zero conditional entropy. -/
example {m k d : ℕ} (p : Fin m → ℝ) (rho : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (c : AuxChannel m k) (j : Fin k) (h : auxWeight p c j = 0) :
    auxWeight p c j * vnEntropy (conditionalBob p rho c j) = 0 := by rw [h, zero_mul]

/-- Sanity: entrywise conjugation is an involution, including on non-real targets. -/
example {O : Type*} (M : Matrix O O ℂ) : bar (bar M) = M := by
  ext a b
  simp [bar]

/-- Sanity: the invalid empty randomising family is zero; the theorem excludes K = 0. -/
example {D : ℕ} (U : Fin 0 → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : Matrix (Fin D) (Fin D) ℂ) : randomise U rho = 0 := by
  simp [randomise]

/-- Sanity: the record simulator is linear at zero, rather than conjugating its unknown input. -/
example {D K : ℕ} (U : Fin K → Matrix.unitaryGroup (Fin D) ℂ) : piSimulator U 0 = 0 := by
  ext x y
  simp [piSimulator]

/-- Sanity: the empty product target is the unit scalar. -/
example {d : ℕ} (E : PureEnsemble (Fin d)) (w : Fin 0 → Fin E.count) (x : Fin 0 → Fin d) :
    pureWordVector E 0 w x = 1 := by simp [pureWordVector]

/-- Sanity: the rate estimate at the mean is zero. -/
example : elementaryRate 0 = 0 := by simp [elementaryRate]

end QAlgorithms.Papers.Independent.Intakenext100.P54


