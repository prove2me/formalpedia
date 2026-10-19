-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
-- name    : QAlgorithms_Papers_Independent_Information100_P58
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T12:13:13.233794+00:00
-- url     : https://prove2.me/theorems/d18055a4-38cd-47be-a29f-c398abcef0b1
-- title:
--   Definitions for Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback
-- statement:
--   The objects the formalized statements of *Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback* (arXiv:2610.00440) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Distribution`: Probability weights on a finite alphabet; source §2, PDF pp.6–7.
--   - `Word`: Length-n input basis words over d symbols; §2.1, PDF p.7.
--   - `Output`: Output basis words, with one extra flag per coordinate; §2.1, PDF pp.6–7.
--   - `Operator`: Operators on a finite basis; §2, PDF p.6.
--   - `singleErasure`: The one-dimensional orthogonal erasure flag is `none`; Eq.(2.1), PDF p.6. This differs from the frozen Gottesman qubit channel, whose erased block has dimension two.
--   - `erasure`: Tensor-power erasure channel on arbitrary, possibly entangled operators; Eq.(2.3), p.7.
--   - `support`: Surviving coordinates of an output basis word, including the empty sector; p.7.
--   - `patternWeight`: Sector probabilities, with natural powers giving `0^0=1`; Eq.(2.2), p.7.
--   - `binomialWeight`: Binomial survivor probabilities; Eq.(2.2), p.7.
--   - `dimensionSuccess`: Dimension-counting success function, not an operational optimum; Eq.(4.1), p.13.
--   - `cumulativeB`: Cumulative mass and dimension-weighted mass; Eq.(4.11), p.17.
--   - `cumulativeZ`: Dimension-weighted cumulative mass Z_j; Eq.(4.11), PDF p.17.
--   - `messageThreshold`: Real message-size threshold; the finite set is nonempty for `ε<1`, Eq.(4.12), p.17. Only strictly feasible cutoffs occur; all their denominators and numerators are positive.
--   - `reference`: Pure product reference output, Eq.(5.4), p.19.
--   - `auxiliary`: Sector-uniform auxiliary operator for raw weights; Eq.(5.1), p.19. The theorems require probability weights; empty sectors have dimension `d^0=1`.
--   - `testingBeta`: Quantum type-II testing optimum, defined over actual operator effects; Eq.(5.12), p.20. For density operators and `0≤ε<1`, the feasible set is nonempty and compact.
--   - `testingD`: Extended hypothesis-testing divergence in bits, including `-log₂ 0=+∞`; p.20.
--   - `auxiliaryInf`: Infimum over normalized sector weights, not over arbitrary nonnegative weights; p.22.
--   - `optimizer`: Explicit truncated, dimension-weighted optimizer; Eq.(5.23), p.22.
--   - `ScalarFeasible`: Scalar tests and their objective; Eq.(5.21), p.22.
--   - `scalarCost`: Scalar type-II objective, including the empty sector; Eq.(5.21), PDF p.22.
--   - `QuantumCode`: A no-feedback quantum code has arbitrary mixed block inputs and a collective POVM; p.7.
--   - `quantumIndividual`: Individual and uniform-message quantum success; Eq.(2.5), p.7.
--   - `quantumAverage`: Uniform average of all M individual successes; Eq.(2.5), PDF p.7.
--   - `quantumOptimum`: Operational supremum over all legal quantum codes; p.8. For positive parameters, values are nonempty and bounded in `[0,1]`; finite-dimensional compactness gives attainment.
--   - `ClassicalCode`: General randomized classical no-feedback encoders and decoders, §7.2, p.28. All distributions are chosen before the channel pattern and no shared seed is available.
--   - `received`: Classical erasure output for an input word and a survivor set; p.7.
--   - `classicalIndividual`: Individual and uniform-message success of randomized classical codes; pp.28,33.
--   - `classicalAverage`: Equiprobable-message classical success; §7.2, PDF p.28.
--   - `classicalOptimum`: Optimal classical average or worst-message success, including randomized encoders; p.28.
--   - `compatible`: Compatible-message class for a deterministic word code, with repeated words allowed; p.34.
--   - `deterministicIndividual`: Success with uniform guessing in each nonempty compatible class; pp.26,34. The class always contains the true message, so no division by zero occurs.
--   - `deterministicAverage`: Uniform-message success for a fixed word code and compatible-class decoder; PDF p.34.
--   - `Feasible`: Message-size feasibility means existence of a legal code, not just a success budget; p.8.
--   - `capacity`: Non-asymptotic capacity in bits under either error criterion, without a shared seed; p.8. For the theorem parameters the feasible natural message sizes form a nonempty bounded set.
--   - `InputEnsemble`: Finite ensembles with arbitrary probabilities and mixed block inputs; Eq.(5.30), p.23.
--   - `cqOutput`: Joint classical–quantum output operator for any finite label alphabet; Eq.(5.30), p.23.
--   - `cqAuxiliary`: The independent auxiliary `p_X ⊗ σ`, with no message correlation; Eq.(5.30), p.23.
--   - `ensembleInf`: Infimum over every output density matrix for a fixed input ensemble; p.23.
--   - `optimizedConverse`: Fully optimized testing converse, not operational capacity; Eq.(5.30), p.23.
--   - `basisDensity`: Computational-basis density operator, including the unique empty input word; p.45.
--   - `basisEnsembleInf`: Uniform computational-basis ensemble value; Eq.(A.1), p.45.
--   - `firstBit`: Binary labels of the four messages used in §7; p.26.
--   - `secondBit`: The low binary digit y of m-1 in the source one-based labeling; PDF p.26.
--   - `parityBit`: Binary sum x xor y, using Fin 2 addition; Eq.(7.3), PDF p.27.
--   - `tetrahedron`: Tetrahedral density operator in the standard Pauli convention; Eq.(7.1), p.26.
--   - `tetrahedralInput`: Explicit four-carrier product code, with the tetrahedral state on carrier four; Eq.(7.3), p.27.
--   - `tetrahedralValue`: Achievable tetrahedral performance, not the unknown quantum optimum; Eq.(7.6), p.27.
--   - `repeatedParity`: The attaining classical code `(x,y,x xor y,x)`; Eq.(7.8), p.28.
--   - `randomCodingSuccess`: Expected projection-count success of iid random words; Eq.(8.14), p.33.
--   - `collisionBound`: Separate collision-based average-error bound; Eq.(8.16), p.33.
--   - `thresholdBound`: Thresholded maximum-error bound with no factor on the low-survivor tail; Eq.(8.19), p.34.
--   - `normalQuantile`: Gaussian quantile as the inverse standard-normal CDF on `(0,1)`; §8.1, p.30.
--   - `normalCenter`: The two explicit normal-approximation terms; Eqs.(8.1),(8.22), pp.30,35.
--   - `expurgatedBound`: Expurgated finite-code bound, possibly larger than one; Eq.(B.4), p.46.
--   - `binaryRelativeEntropy`: Binary relative entropy in bits, Eq.(8.26), PDF p.36. For 0<q<1 the total-log convention implements the continuous endpoints t=0,1.
--   - `rateMessages`: Integer message count at a fixed real rate, Eqs.(8.27),(8.34), PDF pp.36–37.
--   - `noFeedbackError`: Optimal no-feedback error for each model and criterion; Eq.(8.42), PDF p.40.
--   - `noFeedbackErrorDecay`: Actual negative normalized log error, not an independently chosen exponent; Eq.(8.42). For n>0,p in (0,1),R>0 the all-erased event makes the optimal error positive. The total value at n=0 is irrelevant to limits along atTop.
--   - `criticalRate`: Critical rate below capacity, Eq.(8.39), PDF p.39.
--   - `randomCodingExponent`: Compact random-coding minimization; Eq.(8.40), PDF p.39. The theorem gives attainment as well as its piecewise evaluation.
--   - `expurgatedExponent`: Expurgated exponent with real optimization parameter s; Eq.(8.41), PDF p.39. For d>=2,0<p<1,R>0 this nonempty objective set is bounded above.
-- source:
--   Finite-blocklength classical communication over the quantum erasure channel with and without classical feedback, arXiv:2610.00440v1, https://arxiv.org/abs/2610.00440v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble

/-!
# Finite-blocklength erasure communication: no-feedback and testing statements

Source: arXiv:2610.00440v1. Paper-local definitions use the accepted density,
POVM, Kraus-channel and tensor-superoperator primitives. The output alphabet
adds exactly one orthogonal erasure flag to each input alphabet. Every theorem
below is a statement-only draft. Operational feedback results are explicitly
deferred in this unit's HARD.md and GAPS.json; no scalar formula is used to
stand in for an undefined feedback optimum. Compilation is pending batch handoff.
-/

namespace QAlgorithms.Papers.Independent.Information100.P58

open scoped BigOperators ComplexConjugate Matrix

noncomputable section

/-- Probability weights on a finite alphabet; source §2, PDF pp.6–7. -/
def Distribution (A : Type*) [Fintype A] :=
  {q : A → ℝ // (∀ a, 0 ≤ q a) ∧ ∑ a, q a = 1}

/-- Length-n input basis words over d symbols; §2.1, PDF p.7. -/
abbrev Word (n d : ℕ) := Fin n → Fin d

/-- Output basis words, with one extra flag per coordinate; §2.1, PDF pp.6–7. -/
abbrev Output (n d : ℕ) := Fin n → Option (Fin d)

/-- Operators on a finite basis; §2, PDF p.6. -/
abbrev Operator (A : Type*) := Matrix A A ℂ

/-- The one-dimensional orthogonal erasure flag is `none`; Eq.(2.1), PDF p.6.
This differs from the frozen Gottesman qubit channel, whose erased block has dimension two. -/
def singleErasure (d : ℕ) (p : ℝ) : Superop (Fin d) (Option (Fin d)) :=
  fun X a b => match a, b with
    | some i, some j => (1 - p : ℂ) * X i j
    | none, none => (p : ℂ) * X.trace
    | _, _ => 0

/-- Tensor-power erasure channel on arbitrary, possibly entangled operators; Eq.(2.3), p.7. -/
def erasure (n d : ℕ) (p : ℝ) : Superop (Word n d) (Output n d) :=
  piSuperop (fun _ : Fin n => singleErasure d p)

/-- Surviving coordinates of an output basis word, including the empty sector; p.7. -/
def support {n d : ℕ} (y : Output n d) : Finset (Fin n) :=
  Finset.univ.filter fun i => (y i).isSome

/-- Sector probabilities, with natural powers giving `0^0=1`; Eq.(2.2), p.7. -/
def patternWeight (n : ℕ) (p : ℝ) (S : Finset (Fin n)) : ℝ :=
  (1-p)^S.card * p^(n-S.card)

/-- Binomial survivor probabilities; Eq.(2.2), p.7. -/
def binomialWeight (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  n.choose k * (1-p)^k * p^(n-k)

/-- Dimension-counting success function, not an operational optimum; Eq.(4.1), p.13. -/
def dimensionSuccess (n d : ℕ) (p : ℝ) (M : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), binomialWeight n p k * min 1 ((d:ℝ)^k / M)

/-- Cumulative mass and dimension-weighted mass; Eq.(4.11), p.17. -/
def cumulativeB (n : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (j+1), binomialWeight n p k

/-- Dimension-weighted cumulative mass Z_j; Eq.(4.11), PDF p.17. -/
def cumulativeZ (n d : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (j+1), binomialWeight n p k * (d:ℝ)^k

/-- Real message-size threshold; the finite set is nonempty for `ε<1`, Eq.(4.12), p.17.
Only strictly feasible cutoffs occur; all their denominators and numerators are positive. -/
def messageThreshold (n d : ℕ) (p ε : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ j : ℕ, j ≤ n ∧ ε < cumulativeB n p j ∧
    r = cumulativeZ n d p j / (cumulativeB n p j - ε)}

/-- Pure product reference output, Eq.(5.4), p.19. -/
def reference (n d : ℕ) (p : ℝ) (ψ : EuclideanSpace ℂ (Fin d)) : Operator (Output n d) :=
  erasure n d p (pureDensity (tensorPow n ψ))

/-- Sector-uniform auxiliary operator for raw weights; Eq.(5.1), p.19.
The theorems require probability weights; empty sectors have dimension `d^0=1`. -/
def auxiliary (n d : ℕ) (q : Finset (Fin n) → ℝ) : Operator (Output n d) :=
  Matrix.diagonal fun y => (q (support y) / (d:ℝ)^(support y).card : ℝ)

/-- Quantum type-II testing optimum, defined over actual operator effects; Eq.(5.12), p.20.
For density operators and `0≤ε<1`, the feasible set is nonempty and compact. -/
def testingBeta {A : Type*} [Fintype A] [DecidableEq A]
    (ε : ℝ) (ω σ : Operator A) : ℝ :=
  sInf {v : ℝ | ∃ T : Operator A, IsEffect T ∧ 1-ε ≤ effectProb T ω ∧ v = effectProb T σ}

/-- Extended hypothesis-testing divergence in bits, including `-log₂ 0=+∞`; p.20. -/
def testingD {A : Type*} [Fintype A] [DecidableEq A]
    (ε : ℝ) (ω σ : Operator A) : EReal :=
  if testingBeta ε ω σ = 0 then ⊤ else ((-Real.logb 2 (testingBeta ε ω σ) : ℝ) : EReal)

/-- Infimum over normalized sector weights, not over arbitrary nonnegative weights; p.22. -/
def auxiliaryInf (n d : ℕ) (p ε : ℝ) (ψ : EuclideanSpace ℂ (Fin d)) : EReal :=
  ⨅ q : Distribution (Finset (Fin n)), testingD ε (reference n d p ψ) (auxiliary n d q.val)

/-- Explicit truncated, dimension-weighted optimizer; Eq.(5.23), p.22. -/
def optimizer (n d : ℕ) (p : ℝ) (j : ℕ) (S : Finset (Fin n)) : ℝ :=
  if S.card ≤ j then patternWeight n p S * (d:ℝ)^S.card / cumulativeZ n d p j else 0

/-- Scalar tests and their objective; Eq.(5.21), p.22. -/
def ScalarFeasible (n : ℕ) (p ε : ℝ) (t : Finset (Fin n) → ℝ) : Prop :=
  (∀ S, 0 ≤ t S ∧ t S ≤ 1) ∧ 1-ε ≤ ∑ S, patternWeight n p S * t S

/-- Scalar type-II objective, including the empty sector; Eq.(5.21), PDF p.22. -/
def scalarCost (n d : ℕ) (q t : Finset (Fin n) → ℝ) : ℝ :=
  ∑ S, q S * t S / (d:ℝ)^S.card

/-- A no-feedback quantum code has arbitrary mixed block inputs and a collective POVM; p.7. -/
structure QuantumCode (n d M : ℕ) where
  input : Fin M → Operator (Word n d)
  normalized : ∀ m, IsDensityMatrix (input m)
  decoder : Fin M → Operator (Output n d)
  measurement : IsPOVM decoder

/-- Individual and uniform-message quantum success; Eq.(2.5), p.7. -/
def quantumIndividual {n d M : ℕ} (p : ℝ) (C : QuantumCode n d M) (m : Fin M) : ℝ :=
  effectProb (C.decoder m) (erasure n d p (C.input m))

/-- Uniform average of all M individual successes; Eq.(2.5), PDF p.7. -/
def quantumAverage {n d M : ℕ} (p : ℝ) (C : QuantumCode n d M) : ℝ :=
  (∑ m, quantumIndividual p C m) / M

/-- Operational supremum over all legal quantum codes; p.8. For positive parameters,
values are nonempty and bounded in `[0,1]`; finite-dimensional compactness gives attainment. -/
def quantumOptimum (n d M : ℕ) (p : ℝ) (worst : Bool := false) : ℝ :=
  sSup {v : ℝ | ∃ C : QuantumCode n d M,
    v = if worst then ⨅ m, quantumIndividual p C m else quantumAverage p C}

/-- General randomized classical no-feedback encoders and decoders, §7.2, p.28.
All distributions are chosen before the channel pattern and no shared seed is available. -/
structure ClassicalCode (n d M : ℕ) where
  encoder : Fin M → Distribution (Word n d)
  decoder : Output n d → Distribution (Fin M)

/-- Classical erasure output for an input word and a survivor set; p.7. -/
def received {n d : ℕ} (x : Word n d) (S : Finset (Fin n)) : Output n d :=
  fun i => if i ∈ S then some (x i) else none

/-- Individual and uniform-message success of randomized classical codes; pp.28,33. -/
def classicalIndividual {n d M : ℕ} (p : ℝ) (C : ClassicalCode n d M) (m : Fin M) : ℝ :=
  ∑ S : Finset (Fin n), patternWeight n p S *
    ∑ x : Word n d, (C.encoder m).val x * (C.decoder (received x S)).val m

/-- Equiprobable-message classical success; §7.2, PDF p.28. -/
def classicalAverage {n d M : ℕ} (p : ℝ) (C : ClassicalCode n d M) : ℝ :=
  (∑ m, classicalIndividual p C m) / M

/-- Optimal classical average or worst-message success, including randomized encoders; p.28. -/
def classicalOptimum (n d M : ℕ) (p : ℝ) (worst : Bool := false) : ℝ :=
  sSup {v : ℝ | ∃ C : ClassicalCode n d M,
    v = if worst then ⨅ m, classicalIndividual p C m else classicalAverage p C}

/-- Compatible-message class for a deterministic word code, with repeated words allowed; p.34. -/
def compatible {n d M : ℕ} (C : Fin M → Word n d) (S : Finset (Fin n)) (m : Fin M) :
    Finset (Fin M) := Finset.univ.filter fun j => ∀ i ∈ S, C j i = C m i

/-- Success with uniform guessing in each nonempty compatible class; pp.26,34.
The class always contains the true message, so no division by zero occurs. -/
def deterministicIndividual {n d M : ℕ} (p : ℝ) (C : Fin M → Word n d) (m : Fin M) : ℝ :=
  ∑ S : Finset (Fin n), patternWeight n p S / (compatible C S m).card

/-- Uniform-message success for a fixed word code and compatible-class decoder; PDF p.34. -/
def deterministicAverage {n d M : ℕ} (p : ℝ) (C : Fin M → Word n d) : ℝ :=
  (∑ m, deterministicIndividual p C m) / M

/-- Message-size feasibility means existence of a legal code, not just a success budget; p.8. -/
def Feasible (n d M : ℕ) (p ε : ℝ) (classical worst : Bool) : Prop :=
  0 < M ∧ if classical then
    ∃ C : ClassicalCode n d M, if worst then (∀ m, 1-ε ≤ classicalIndividual p C m)
      else 1-ε ≤ classicalAverage p C
  else ∃ C : QuantumCode n d M, if worst then (∀ m, 1-ε ≤ quantumIndividual p C m)
      else 1-ε ≤ quantumAverage p C

/-- Non-asymptotic capacity in bits under either error criterion, without a shared seed; p.8.
For the theorem parameters the feasible natural message sizes form a nonempty bounded set. -/
def capacity (n d : ℕ) (p ε : ℝ) (classical worst : Bool) : ℝ :=
  Real.logb 2 (sSup {M : ℕ | Feasible n d M p ε classical worst} : ℕ)

/-- Finite ensembles with arbitrary probabilities and mixed block inputs; Eq.(5.30), p.23. -/
structure InputEnsemble (n d L : ℕ) where
  weights : Distribution (Fin L)
  states : Fin L → Operator (Word n d)
  normalized : ∀ x, IsDensityMatrix (states x)

/-- Joint classical–quantum output operator for any finite label alphabet; Eq.(5.30), p.23. -/
def cqOutput {A : Type*} [DecidableEq A] (n d : ℕ) (p : ℝ)
    (q : A → ℝ) (ρ : A → Operator (Word n d)) : Operator (A × Output n d) :=
  fun a b => if a.1 = b.1 then (q a.1 : ℂ) * erasure n d p (ρ a.1) a.2 b.2 else 0

/-- The independent auxiliary `p_X ⊗ σ`, with no message correlation; Eq.(5.30), p.23. -/
def cqAuxiliary {A : Type*} [DecidableEq A] (n d : ℕ)
    (q : A → ℝ) (σ : Operator (Output n d)) : Operator (A × Output n d) :=
  fun a b => if a.1 = b.1 then (q a.1 : ℂ) * σ a.2 b.2 else 0

/-- Infimum over every output density matrix for a fixed input ensemble; p.23. -/
def ensembleInf {A : Type*} [Fintype A] [DecidableEq A] (n d : ℕ) (p ε : ℝ)
    (q : A → ℝ) (ρ : A → Operator (Word n d)) : EReal :=
  ⨅ σ : {σ : Operator (Output n d) // IsDensityMatrix σ},
    testingD ε (cqOutput n d p q ρ) (cqAuxiliary n d q σ.val)

/-- Fully optimized testing converse, not operational capacity; Eq.(5.30), p.23. -/
def optimizedConverse (n d : ℕ) (p ε : ℝ) : EReal :=
  ⨆ L : ℕ, ⨆ E : InputEnsemble n d L, ensembleInf n d p ε E.weights.val E.states

/-- Computational-basis density operator, including the unique empty input word; p.45. -/
def basisDensity {A : Type*} [DecidableEq A] (x : A) : Operator A :=
  fun a b => if a = x ∧ b = x then 1 else 0

/-- Uniform computational-basis ensemble value; Eq.(A.1), p.45. -/
def basisEnsembleInf (n d : ℕ) (p ε : ℝ) : EReal :=
  ensembleInf n d p ε (fun _ : Word n d => ((d:ℝ)^n)⁻¹) basisDensity

/-- Binary labels of the four messages used in §7; p.26. -/
def firstBit (m : Fin 4) : Fin 2 := ⟨m.val / 2, by omega⟩

/-- The low binary digit y of m-1 in the source one-based labeling; PDF p.26. -/
def secondBit (m : Fin 4) : Fin 2 := ⟨m.val % 2, Nat.mod_lt _ (by decide)⟩

/-- Binary sum x xor y, using Fin 2 addition; Eq.(7.3), PDF p.27. -/
def parityBit (m : Fin 4) : Fin 2 := ⟨(firstBit m + secondBit m).val, (firstBit m + secondBit m).isLt⟩

/-- Tetrahedral density operator in the standard Pauli convention; Eq.(7.1), p.26. -/
def tetrahedron (m : Fin 4) : Operator (Fin 2) :=
  let x : ℝ := (-1)^(firstBit m).val / Real.sqrt 3
  let y : ℝ := (-1)^(secondBit m).val / Real.sqrt 3
  let z : ℝ := (-1)^((firstBit m).val+(secondBit m).val) / Real.sqrt 3
  (1/2 : ℂ) • !![1+(z:ℂ), (x:ℂ)-Complex.I*(y:ℂ);
    (x:ℂ)+Complex.I*(y:ℂ), 1-(z:ℂ)]

/-- Explicit four-carrier product code, with the tetrahedral state on carrier four; Eq.(7.3), p.27. -/
def tetrahedralInput (m : Fin 4) : Operator (Word 4 2) :=
  fun a b => (if a 0 = firstBit m ∧ b 0 = firstBit m then 1 else 0) *
    (if a 1 = secondBit m ∧ b 1 = secondBit m then 1 else 0) *
    (if a 2 = parityBit m ∧ b 2 = parityBit m then 1 else 0) *
    tetrahedron m (a 3) (b 3)

/-- Achievable tetrahedral performance, not the unknown quantum optimum; Eq.(7.6), p.27. -/
def tetrahedralValue (p : ℝ) : ℝ :=
  dimensionSuccess 4 2 p 4 - (3-Real.sqrt 6)/2 * p^2 * (1-p)^2

/-- The attaining classical code `(x,y,x xor y,x)`; Eq.(7.8), p.28. -/
def repeatedParity (m : Fin 4) : Word 4 2 :=
  ![firstBit m, secondBit m, parityBit m, firstBit m]

/-- Expected projection-count success of iid random words; Eq.(8.14), p.33. -/
def randomCodingSuccess (n d M : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), binomialWeight n p k * ((d:ℝ)^k / M) *
    (1-(1-((d:ℝ)^k)⁻¹)^M)

/-- Separate collision-based average-error bound; Eq.(8.16), p.33. -/
def collisionBound (n d M : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), binomialWeight n p k * min 1 ((M-1:ℕ)/(2*(d:ℝ)^k))

/-- Thresholded maximum-error bound with no factor on the low-survivor tail; Eq.(8.19), p.34. -/
def thresholdBound (n d M : ℕ) (p r : ℝ) : ℝ :=
  min 1 ((∑ k ∈ (Finset.range (n+1)).filter (fun k : ℕ => (k : ℝ) < r), binomialWeight n p k) +
    (2*(M:ℝ)-1) * ∑ k ∈ (Finset.range (n+1)).filter (fun k : ℕ => r ≤ (k : ℝ)),
      binomialWeight n p k * ((d:ℝ)^k)⁻¹)

/-- Gaussian quantile as the inverse standard-normal CDF on `(0,1)`; §8.1, p.30. -/
def normalQuantile (ε : ℝ) : ℝ :=
  sInf {x : ℝ | ε ≤ ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) x}

/-- The two explicit normal-approximation terms; Eqs.(8.1),(8.22), pp.30,35. -/
def normalCenter (n d : ℕ) (p ε : ℝ) : ℝ :=
  n*(1-p)*Real.logb 2 d + Real.sqrt ((n:ℝ)*p*(1-p))*Real.logb 2 d*normalQuantile ε

/-- Expurgated finite-code bound, possibly larger than one; Eq.(B.4), p.46. -/
def expurgatedBound (n d M : ℕ) (p s : ℝ) : ℝ :=
  (1/2) * (2*(2*(M:ℝ)-1)*(1/(d:ℝ)+(1-1/(d:ℝ))*p^(1/s))^n)^s

/-- Binary relative entropy in bits, Eq.(8.26), PDF p.36.
For 0<q<1 the total-log convention implements the continuous endpoints t=0,1. -/
def binaryRelativeEntropy (t q : ℝ) : ℝ :=
  t * Real.logb 2 (t/q) + (1-t) * Real.logb 2 ((1-t)/(1-q))

/-- Integer message count at a fixed real rate, Eqs.(8.27),(8.34), PDF pp.36–37. -/
def rateMessages (n : ℕ) (R : ℝ) : ℕ :=
  Nat.ceil ((2 : ℝ)^((n : ℝ)*R))

/-- Optimal no-feedback error for each model and criterion; Eq.(8.42), PDF p.40. -/
def noFeedbackError (n d M : ℕ) (p : ℝ) (classical worst : Bool) : ℝ :=
  1 - if classical then classicalOptimum n d M p worst else quantumOptimum n d M p worst

/-- Actual negative normalized log error, not an independently chosen exponent; Eq.(8.42).
For n>0,p in (0,1),R>0 the all-erased event makes the optimal error positive.
The total value at n=0 is irrelevant to limits along atTop. -/
def noFeedbackErrorDecay (d : ℕ) (p R : ℝ) (classical worst : Bool) (n : ℕ) : ℝ :=
  -Real.logb 2 (noFeedbackError n d (rateMessages n R) p classical worst) / (n : ℝ)

/-- Critical rate below capacity, Eq.(8.39), PDF p.39. -/
def criticalRate (d : ℕ) (p : ℝ) : ℝ :=
  (1-p) / ((1-p)+(d : ℝ)*p) * Real.logb 2 d

/-- Compact random-coding minimization; Eq.(8.40), PDF p.39.
The theorem gives attainment as well as its piecewise evaluation. -/
def randomCodingExponent (d : ℕ) (p R : ℝ) : ℝ :=
  sInf {v : ℝ | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    v = binaryRelativeEntropy t (1-p) + max (t*Real.logb 2 d-R) 0}

/-- Expurgated exponent with real optimization parameter s; Eq.(8.41), PDF p.39.
For d>=2,0<p<1,R>0 this nonempty objective set is bounded above. -/
def expurgatedExponent (d : ℕ) (p R : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ s : ℝ, 1 ≤ s ∧
    v = -s * Real.logb 2 (1/(d : ℝ)+(1-1/(d : ℝ))*p^(1/s))-s*R}

example (q : ℝ) : binaryRelativeEntropy 0 q = Real.logb 2 (1/(1-q)) := by
  simp [binaryRelativeEntropy]

example (n : ℕ) : rateMessages n 0 = 1 := by
  simp [rateMessages]

/-! Sanity examples pin actual channel blocks, normalization conventions, and explicit carriers. -/

example (d : ℕ) (p : ℝ) (X : Operator (Fin d)) :
    singleErasure d p X none none = (p:ℂ)*X.trace := by rfl

example (d : ℕ) (X : Operator (Fin d)) (i j : Fin d) :
    singleErasure d 0 X (some i) (some j) = X i j := by simp [singleErasure]

example (n : ℕ) (p : ℝ) : patternWeight n p ∅ = p^n := by simp [patternWeight]

example (m : Fin 4) : repeatedParity m 0 = firstBit m := by simp [repeatedParity]

example (m : Fin 4) : (tetrahedron m).trace = 1 := by
  simp [tetrahedron, Matrix.trace, Fin.sum_univ_two]
  ring

example {A : Type*} [DecidableEq A] (x : A) : basisDensity x x x = 1 := by
  simp [basisDensity]

end

end QAlgorithms.Papers.Independent.Information100.P58


