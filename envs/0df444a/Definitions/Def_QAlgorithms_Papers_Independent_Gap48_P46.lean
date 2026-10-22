-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P46
-- name    : QAlgorithms_Papers_Independent_Gap48_P46
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T05:48:24.62219+00:00
-- url     : https://prove2.me/theorems/a7b6c597-c76b-4c03-9f98-21016c1dde73
-- title:
--   Definitions for On Shor's channel extension and constrained channels
-- statement:
--   The objects the formalized statements of *On Shor's channel extension and constrained channels* (arXiv:quant-ph/0306196) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `states`: PDF p.2: normalized density matrices, including one-dimensional systems.
--   - `shorEnsembleEntropy`: PDF p.3: average output entropy.
--   - `fixedMeanChi`: PDF p.2: fixed-mean chi is defined independently of the entropy-roof identity.
--   - `Constraint`: PDF p.3: nonempty closed state-space subset. Ambient and relative closedness agree because the finite-dimensional state space is closed. Convexity is separate.
--   - `constrainedChiCapacity`: PDF p.3, Eq.(3): capacity optimizes over mean states.
--   - `linearConstraint`: PDF p.3: linear inequality constraint.
--   - `budgetDomain`: PDF pp.3,16: nonnegative feasible budgets, without an artificial upper bound.
--   - `IsOptimalConstrainedEnsemble`: PDF p.3: actual optimality of a feasible ensemble.
--   - `shorEnsembleDistance`: PDF p.4: extended nonnegative distance sum; 0 times infinity contributes 0.
--   - `tensorMarginalConstraint`: PDF p.6: all joint densities with constrained marginals, including entanglement.
--   - `ConstrainedAdditive`: PDF p.6, Eq.(8): additivity for one constraint pair.
--   - `AllConstraints`: PDF pp.6–7: every nonempty closed constraint pair, including nonconvex pairs.
--   - `LinearAdditive`: PDF p.6: all feasible positive-observable linear constraints.
--   - `ChiSubadditive`: PDF p.6, Eq.(9): pointwise chi subadditivity.
--   - `RoofSuperadditive`: PDF p.6, Eq.(10): strong superadditivity of the mixed entropy roof.
--   - `ProductChiAdditive`: PDF p.7: product-state chi additivity for every pair of states.
--   - `ProductRoofAdditive`: PDF p.7: product-state roof additivity for every pair of states.
--   - `flaggedChannelSum`: PDF p.8: block diagonal mixture, allowing different branch output spaces.
--   - `twoBranchFlaggedChannel`: PDF p.9: two-branch direct-sum mixture.
--   - `shor`: PDF pp.10–11, Remark 2: full-algebra extension. None labels failure; some j labels success. The diagonal label blocks alone determine the output.
--   - `dephaseLabel`: PDF p.11: delete off-diagonal classical-label input blocks.
--   - `secondConstraint`: PDF pp.11,13: only the second marginal is constrained.
--   - `maxValue`: PDF pp.11,13,17: optimized value on nonempty bounded feasible sections.
--   - `MaximizesValue`: PDF pp.11,13,17: feasible maximizing point and universal upper bound.
--   - `finiteTilt`: PDF p.11: objective in the finite-d approximation.
--   - `shorTiltObjective`: PDF p.13, Eq.(25): single-channel tilted objective.
--   - `jointTilted`: PDF p.13, Eq.(26): joint tilted objective, with B retained in its feasible domain.
--   - `admissibleTail`: PDF p.13: physical cofinal tail, excluding d=0,1 and q>1.
--   - `extensionSequence`: PDF p.13: unconstrained capacities on the physical tail, zero scalar prefix.
--   - `jointExtensionSequence`: PDF p.13: joint capacities on the physical tail, with the second marginal in B.
--   - `AsymptoticAdditive`: PDF p.13, Theorem 2(ii): both limits exist and satisfy the sum relation.
--   - `GlobalUnconstrained`: PDF p.15: global unconstrained conjecture, quantified over every finite dimension.
--   - `GlobalConstrained`: PDF p.15: global constrained conjecture, including nonconvex closed constraints.
--   - `PartialTraceConstrained`: PDF p.8: global constrained additivity restricted to partial-trace channels.
--   - `sumObservable`: PDF p.15: two-system additive observable.
--   - `allocations`: PDF pp.15–16: feasible allocations; empty local sections are excluded.
--   - `WeakAt`: PDF p.15, Eq.(33): weak allocation identity and attainment.
--   - `GlobalWeak`: PDF p.16: global weak conjecture, every channel pair and feasible positive costs.
--   - `blockObservable`: PDF pp.15–16: additive cost on n copies; the i-th term acts on the i-th factor.
--   - `blockAllocations`: PDF p.16: feasible n-use budget allocations.
--   - `BlockWeak`: PDF p.16: conditional n-channel weak allocation identity, for positive n.
--   - `CostConstrainedCode`: PDF p.15, operational C: finite unassisted collective code, per-codeword additive budget and decoding POVM. Capacity is not defined by an entropy regularization.
--   - `CostConstrainedCode.Reliable`: PDF p.15: uniform decoding error at most epsilon for every message.
--   - `AchievableConstrainedRate`: PDF p.15: asymptotically reliable rates in bits, with integer message counts.
--   - `constrainedOperationalCapacity`: PDF p.15: operational capacity is the supremum of achievable code rates.
--   - `sectionSet`: PDF p.17: feasible equality, upper or lower linear section.
--   - `sectionDomain`: PDF p.17: exactly the budgets with a nonempty section.
--   - `sectionValue`: PDF p.17: optimized section value, with attainment asserted by the theorem.
--   - `singletonMixedEnsemble`: PDF p.2: the one-element ensemble at a given density, witnessing a feasible mean.
-- source:
--   On Shor's channel extension and constrained channels, arXiv:quant-ph/0306196v2, https://arxiv.org/abs/quant-ph/0306196v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

/-!
Holevo and Shirokov, arXiv:quant-ph/0306196v2. References are PDF pages.
Only pinned accepted libraries are imported. The finite mixed ensemble,
its mean, its output Holevo information and its mixed roof are reused from P08;
the operational code carrier is reused from P63. Other new objects are paper-local.
Short names of unrelated accepted concepts are avoided (see ASSESSMENT.json).
Real extrema are used on nonempty bounded value sets; attainment is a conclusion.
Asymptotic sequences use arbitrary zero scalar prefixes before their physical tail.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P46

open scoped Matrix ComplexConjugate ENNReal ComplexOrder
open Filter

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)
open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits)
open QAlgorithms.Papers.Independent.Dependency50.P23 (IsEB)
open QAlgorithms.Papers.Independent.Information100.P08
  (Ensemble ensembleAverage outputHolevo mixedRoof)

variable {I O J K : Type} [Fintype I] [Fintype O] [Fintype J] [Fintype K]
variable [DecidableEq I] [DecidableEq O] [DecidableEq J] [DecidableEq K]

/-- PDF p.2: normalized density matrices, including one-dimensional systems. -/
def states (I : Type) [Fintype I] : Set (Matrix I I ℂ) := {rho | IsDensityMatrix rho}

/-- PDF p.3: average output entropy. -/
def shorEnsembleEntropy (e : Ensemble I) (Phi : Superop I O) : ℝ :=
  ∑ i, e.prob i * vnEntropy (Phi (e.state i))

/-- PDF p.2: fixed-mean chi is defined independently of the entropy-roof identity. -/
def fixedMeanChi (Phi : Superop I O) (rho : Matrix I I ℂ) : ℝ :=
  sSup {v | ∃ e : Ensemble I, (ensembleAverage e) = rho ∧ v = outputHolevo Phi e}

/-- PDF p.3: nonempty closed state-space subset. Ambient and relative closedness
agree because the finite-dimensional state space is closed. Convexity is separate. -/
def Constraint (A : Set (Matrix I I ℂ)) : Prop :=
  A.Nonempty ∧ IsClosed A ∧ A ⊆ states I

/-- PDF p.3, Eq.(3): capacity optimizes over mean states. -/
def constrainedChiCapacity (Phi : Superop I O) (A : Set (Matrix I I ℂ)) : ℝ := sSup (fixedMeanChi Phi '' A)

/-- PDF p.3: linear inequality constraint. -/
def linearConstraint (A : Matrix I I ℂ) (alpha : ℝ) : Set (Matrix I I ℂ) :=
  {rho | IsDensityMatrix rho ∧ effectProb A rho ≤ alpha}

/-- PDF pp.3,16: nonnegative feasible budgets, without an artificial upper bound. -/
def budgetDomain (A : Matrix I I ℂ) : Set ℝ :=
  {alpha | 0 ≤ alpha ∧ (linearConstraint A alpha).Nonempty}

/-- PDF p.3: actual optimality of a feasible ensemble. -/
def IsOptimalConstrainedEnsemble (Phi : Superop I O) (A : Set (Matrix I I ℂ)) (e : Ensemble I) : Prop :=
  (ensembleAverage e) ∈ A ∧ outputHolevo Phi e = constrainedChiCapacity Phi A

/-- PDF p.4: extended nonnegative distance sum; 0 times infinity contributes 0. -/
def shorEnsembleDistance (e : Ensemble I) (Phi : Superop I O) (rho : Matrix I I ℂ) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (e.prob i) * relativeEntropyBits (Phi (e.state i)) (Phi rho)

/-- PDF p.6: all joint densities with constrained marginals, including entanglement. -/
def tensorMarginalConstraint (A : Set (Matrix I I ℂ)) (B : Set (Matrix J J ℂ)) :
    Set (Matrix (I × J) (I × J) ℂ) :=
  {sigma | IsDensityMatrix sigma ∧ traceRight sigma ∈ A ∧ traceLeft sigma ∈ B}

/-- PDF p.6, Eq.(8): additivity for one constraint pair. -/
def ConstrainedAdditive (Phi : Superop I O) (Psi : Superop J K)
    (A : Set (Matrix I I ℂ)) (B : Set (Matrix J J ℂ)) : Prop :=
  constrainedChiCapacity (tensorChannel Phi Psi) (tensorMarginalConstraint A B) = constrainedChiCapacity Phi A + constrainedChiCapacity Psi B

/-- PDF pp.6–7: every nonempty closed constraint pair, including nonconvex pairs. -/
def AllConstraints (Phi : Superop I O) (Psi : Superop J K) : Prop :=
  ∀ A B, Constraint A → Constraint B → ConstrainedAdditive Phi Psi A B

/-- PDF p.6: all feasible positive-observable linear constraints. -/
def LinearAdditive (Phi : Superop I O) (Psi : Superop J K) : Prop :=
  ∀ (A : Matrix I I ℂ) (B : Matrix J J ℂ), A.PosSemidef → B.PosSemidef →
    ∀ alpha ∈ budgetDomain A, ∀ beta ∈ budgetDomain B,
      ConstrainedAdditive Phi Psi (linearConstraint A alpha) (linearConstraint B beta)

/-- PDF p.6, Eq.(9): pointwise chi subadditivity. -/
def ChiSubadditive (Phi : Superop I O) (Psi : Superop J K) : Prop :=
  ∀ sigma ∈ states (I × J), fixedMeanChi (tensorChannel Phi Psi) sigma ≤
    fixedMeanChi Phi (traceRight sigma) + fixedMeanChi Psi (traceLeft sigma)

/-- PDF p.6, Eq.(10): strong superadditivity of the mixed entropy roof. -/
def RoofSuperadditive (Phi : Superop I O) (Psi : Superop J K) : Prop :=
  ∀ sigma ∈ states (I × J), (mixedRoof (fun X => vnEntropy (Phi X))) (traceRight sigma) + (mixedRoof (fun X => vnEntropy (Psi X))) (traceLeft sigma) ≤
    (mixedRoof (fun X => vnEntropy (tensorChannel Phi Psi X))) sigma

/-- PDF p.7: product-state chi additivity for every pair of states. -/
def ProductChiAdditive (Phi : Superop I O) (Psi : Superop J K) : Prop :=
  ∀ rho ∈ states I, ∀ omega ∈ states J,
    fixedMeanChi (tensorChannel Phi Psi) (Matrix.kronecker rho omega) = fixedMeanChi Phi rho + fixedMeanChi Psi omega

/-- PDF p.7: product-state roof additivity for every pair of states. -/
def ProductRoofAdditive (Phi : Superop I O) (Psi : Superop J K) : Prop :=
  ∀ rho ∈ states I, ∀ omega ∈ states J,
    (mixedRoof (fun X => vnEntropy (tensorChannel Phi Psi X))) (Matrix.kronecker rho omega) = (mixedRoof (fun X => vnEntropy (Phi X))) rho + (mixedRoof (fun X => vnEntropy (Psi X))) omega

/-- PDF p.8: block diagonal mixture, allowing different branch output spaces. -/
def flaggedChannelSum {T : Type} [Fintype T] [DecidableEq T] {B : T → Type}
    [∀ t, Fintype (B t)] (q : T → ℝ) (Phi : (t : T) → Superop I (B t)) :
    Superop I (Sigma B) :=
  fun X a b => if h : a.1 = b.1 then
    (q a.1 : ℂ) * Phi a.1 X a.2 (h.symm ▸ b.2) else 0

/-- PDF p.9: two-branch direct-sum mixture. -/
def twoBranchFlaggedChannel (q : ℝ) (Phi : Superop I O) (Psi : Superop I K) : Superop I (O ⊕ K) :=
  fun X a b => match a, b with
    | .inl i, .inl j => (q : ℂ) * Phi X i j
    | .inr i, .inr j => ((1 - q : ℝ) : ℂ) * Psi X i j
    | _, _ => 0

/-- PDF pp.10–11, Remark 2: full-algebra extension. None labels failure;
some j labels success. The diagonal label blocks alone determine the output. -/
def shor (Phi : Superop I O) (E : Matrix I I ℂ) (q : ℝ) (d : ℕ) :
    Superop (I × Fin d) (O ⊕ Option (Fin d)) :=
  fun X a b => match a, b with
    | .inl i, .inl j => ((1 - q : ℝ) : ℂ) * Phi (traceRight X) i j
    | .inr i, .inr j => if i = j then (q : ℂ) *
        (match i with
        | none => ((1 - E) * traceRight X).trace
        | some k => (E * (Matrix.of fun i j => X (i,k) (j,k))).trace) else 0
    | _, _ => 0

/-- PDF p.11: delete off-diagonal classical-label input blocks. -/
def dephaseLabel (d : ℕ) (X : Matrix (I × Fin d) (I × Fin d) ℂ) :
    Matrix (I × Fin d) (I × Fin d) ℂ :=
  fun a b => if a.2 = b.2 then X a b else 0

/-- PDF pp.11,13: only the second marginal is constrained. -/
def secondConstraint (B : Set (Matrix J J ℂ)) : Set (Matrix (I × J) (I × J) ℂ) :=
  {sigma | IsDensityMatrix sigma ∧ traceLeft sigma ∈ B}

/-- PDF pp.11,13,17: optimized value on nonempty bounded feasible sections. -/
def maxValue {X : Type*} (S : Set X) (f : X → ℝ) : ℝ := sSup (f '' S)

/-- PDF pp.11,13,17: feasible maximizing point and universal upper bound. -/
def MaximizesValue {X : Type*} (S : Set X) (f : X → ℝ) (v : ℝ) : Prop :=
  IsGreatest (f '' S) v

/-- PDF p.11: objective in the finite-d approximation. -/
def finiteTilt (Phi : Superop I O) (Psi : Superop J K)
    (E : Matrix I I ℂ) (q : ℝ) (d : ℕ) (sigma : Matrix (I × J) (I × J) ℂ) : ℝ :=
  (1 - q) * fixedMeanChi (tensorChannel Phi Psi) sigma +
    q * Real.logb 2 d * effectProb E (traceRight sigma)

/-- PDF p.13, Eq.(25): single-channel tilted objective. -/
def shorTiltObjective (Phi : Superop I O) (E : Matrix I I ℂ) (lam : ℝ) (rho : Matrix I I ℂ) : ℝ :=
  fixedMeanChi Phi rho + lam * effectProb E rho

/-- PDF p.13, Eq.(26): joint tilted objective, with B retained in its feasible domain. -/
def jointTilted (Phi : Superop I O) (Psi : Superop J K)
    (E : Matrix I I ℂ) (lam : ℝ) (sigma : Matrix (I × J) (I × J) ℂ) : ℝ :=
  fixedMeanChi (tensorChannel Phi Psi) sigma + lam * effectProb E (traceRight sigma)

/-- PDF p.13: physical cofinal tail, excluding d=0,1 and q>1. -/
def admissibleTail (lam : ℝ) (d : ℕ) : Prop := 2 ≤ d ∧ lam ≤ Real.logb 2 d

/-- PDF p.13: unconstrained capacities on the physical tail, zero scalar prefix. -/
def extensionSequence (Phi : Superop I O) (E : Matrix I I ℂ) (lam : ℝ) (d : ℕ) : ℝ :=
  if admissibleTail lam d then
    constrainedChiCapacity (shor Phi E (lam / Real.logb 2 d) d) (states (I × Fin d)) else 0

/-- PDF p.13: joint capacities on the physical tail, with the second marginal in B. -/
def jointExtensionSequence (Phi : Superop I O) (Psi : Superop J K)
    (B : Set (Matrix J J ℂ)) (E : Matrix I I ℂ) (lam : ℝ) (d : ℕ) : ℝ :=
  if admissibleTail lam d then
    constrainedChiCapacity (tensorChannel (shor Phi E (lam / Real.logb 2 d) d) Psi)
      (secondConstraint (I := I × Fin d) B) else 0

/-- PDF p.13, Theorem 2(ii): both limits exist and satisfy the sum relation. -/
def AsymptoticAdditive (Phi : Superop I O) (Psi : Superop J K)
    (B : Set (Matrix J J ℂ)) : Prop :=
  ∀ E, IsEffect E → ∀ lam : ℝ, 0 ≤ lam → ∃ L : ℝ,
    Tendsto (extensionSequence Phi E lam) atTop (nhds L) ∧
    Tendsto (jointExtensionSequence Phi Psi B E lam) atTop (nhds (L + constrainedChiCapacity Psi B))

/-- PDF p.15: global unconstrained conjecture, quantified over every finite dimension. -/
def GlobalUnconstrained : Prop :=
  ∀ (A B C D : Type) [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (Phi : Superop A B) (Psi : Superop C D), IsChannel Phi → IsChannel Psi →
      ConstrainedAdditive Phi Psi (states A) (states C)

/-- PDF p.15: global constrained conjecture, including nonconvex closed constraints. -/
def GlobalConstrained : Prop :=
  ∀ (A B C D : Type) [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (Phi : Superop A B) (Psi : Superop C D), IsChannel Phi → IsChannel Psi →
      AllConstraints Phi Psi

/-- PDF p.8: global constrained additivity restricted to partial-trace channels. -/
def PartialTraceConstrained : Prop :=
  ∀ (A B C D : Type) [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D],
      AllConstraints (traceRight : Superop (A × B) A) (traceRight : Superop (C × D) C)

/-- PDF p.15: two-system additive observable. -/
def sumObservable (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    Matrix (I × J) (I × J) ℂ := Matrix.kronecker A 1 + Matrix.kronecker 1 B

/-- PDF pp.15–16: feasible allocations; empty local sections are excluded. -/
def allocations (A : Matrix I I ℂ) (B : Matrix J J ℂ) (gamma : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ budgetDomain A ∧ p.2 ∈ budgetDomain B ∧ p.1 + p.2 = gamma}

/-- PDF p.15, Eq.(33): weak allocation identity and attainment. -/
def WeakAt (Phi : Superop I O) (Psi : Superop J K)
    (A : Matrix I I ℂ) (B : Matrix J J ℂ) (gamma : ℝ) : Prop :=
  let f := fun p : ℝ × ℝ => constrainedChiCapacity Phi (linearConstraint A p.1) +
    constrainedChiCapacity Psi (linearConstraint B p.2)
  constrainedChiCapacity (tensorChannel Phi Psi) (linearConstraint (sumObservable A B) gamma) =
    maxValue (allocations A B gamma) f ∧ MaximizesValue (allocations A B gamma) f (maxValue (allocations A B gamma) f)

/-- PDF p.16: global weak conjecture, every channel pair and feasible positive costs. -/
def GlobalWeak : Prop :=
  ∀ (A B C D : Type) [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D]
    (Phi : Superop A B) (Psi : Superop C D), IsChannel Phi → IsChannel Psi →
      ∀ (X : Matrix A A ℂ) (Y : Matrix C C ℂ), X.PosSemidef → Y.PosSemidef →
        ∀ gamma ∈ budgetDomain (sumObservable X Y), WeakAt Phi Psi X Y gamma

/-- PDF pp.15–16: additive cost on n copies; the i-th term acts on the i-th factor. -/
def blockObservable (A : Matrix I I ℂ) (n : ℕ) : Matrix (Fin n → I) (Fin n → I) ℂ :=
  fun x y => ∑ i : Fin n, A (x i) (y i) *
    ∏ j ∈ Finset.univ.erase i, if x j = y j then (1 : ℂ) else 0

/-- PDF p.16: feasible n-use budget allocations. -/
def blockAllocations (A : Matrix I I ℂ) (n : ℕ) (alpha : ℝ) : Set (Fin n → ℝ) :=
  {a | (∀ i, a i ∈ budgetDomain A) ∧ ∑ i, a i = (n : ℝ) * alpha}

/-- PDF p.16: conditional n-channel weak allocation identity, for positive n. -/
def BlockWeak (Phi : Superop I O) (A : Matrix I I ℂ) (alpha : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    let S := blockAllocations A n alpha
    let f := fun a : Fin n → ℝ => ∑ i, constrainedChiCapacity Phi (linearConstraint A (a i))
    constrainedChiCapacity (piSuperop (fun _ : Fin n => Phi))
      (linearConstraint (blockObservable A n) ((n : ℝ) * alpha)) = maxValue S f ∧
      MaximizesValue S f (maxValue S f)

/-- PDF p.15, operational C: finite unassisted collective code, per-codeword additive
budget and decoding POVM. Capacity is not defined by an entropy regularization. -/
structure CostConstrainedCode (I O : Type) [Fintype I] [Fintype O] [DecidableEq O]
    (A : Matrix I I ℂ) (alpha : ℝ) (n : ℕ) where
  messages : ℕ
  code : QAlgorithms.Papers.Independent.Information100.P63.Code
    (Fin n → I) (Fin n → O) messages
  cost : ∀ w, effectProb (blockObservable A n) (code.word w) ≤ (n : ℝ) * alpha

/-- PDF p.15: uniform decoding error at most epsilon for every message. -/
def CostConstrainedCode.Reliable (Phi : Superop I O) {A : Matrix I I ℂ} {alpha : ℝ} {n : ℕ}
    (c : CostConstrainedCode I O A alpha n) (epsilon : ℝ) : Prop :=
  ∀ w, 1 - epsilon ≤ effectProb (c.code.measurement w)
    (piSuperop (fun _ : Fin n => Phi) (c.code.word w))

/-- PDF p.15: asymptotically reliable rates in bits, with integer message counts. -/
def AchievableConstrainedRate (Phi : Superop I O) (A : Matrix I I ℂ) (alpha R : ℝ) : Prop :=
  0 ≤ R ∧ ∀ epsilon : ℝ, 0 < epsilon → ∀ delta : ℝ, 0 < delta →
    ∃ N : ℕ, 1 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∃ c : CostConstrainedCode I O A alpha n,
      c.Reliable Phi epsilon ∧ (R - delta) * (n : ℝ) ≤ Real.logb 2 c.messages

/-- PDF p.15: operational capacity is the supremum of achievable code rates. -/
def constrainedOperationalCapacity (Phi : Superop I O) (A : Matrix I I ℂ) (alpha : ℝ) : ℝ :=
  sSup {R | AchievableConstrainedRate Phi A alpha R}

/-- PDF p.17: feasible equality, upper or lower linear section. -/
def sectionSet {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (S : Set V) (l : V →ₗ[ℝ] ℝ) (rel : ℝ → ℝ → Prop) (alpha : ℝ) : Set V :=
  {x | x ∈ S ∧ rel (l x) alpha}

/-- PDF p.17: exactly the budgets with a nonempty section. -/
def sectionDomain {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (S : Set V) (l : V →ₗ[ℝ] ℝ) (rel : ℝ → ℝ → Prop) : Set ℝ :=
  {alpha | (sectionSet S l rel alpha).Nonempty}

/-- PDF p.17: optimized section value, with attainment asserted by the theorem. -/
def sectionValue {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (S : Set V) (F : V → ℝ) (l : V →ₗ[ℝ] ℝ) (rel : ℝ → ℝ → Prop) (alpha : ℝ) : ℝ :=
  maxValue (sectionSet S l rel alpha) F

/-- PDF p.2: the one-element ensemble at a given density, witnessing a feasible mean. -/
def singletonMixedEnsemble (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) : Ensemble I where
  size := 1
  prob := fun _ => 1
  state := fun _ => rho
  nonneg := fun _ => by norm_num
  total := by simp
  density := fun _ => hrho

/-- Sanity: a singleton ensemble has exactly its input mean and zero Holevo information. -/
example (rho : Matrix I I ℂ) (hrho : IsDensityMatrix rho) (Phi : Superop I O) :
    ensembleAverage (singletonMixedEnsemble rho hrho) = rho ∧
    outputHolevo Phi (singletonMixedEnsemble rho hrho) = 0 := by
  constructor
  · change (∑ _ : Fin 1, (1 : ℝ) • rho) = rho
    simp
  · change vnEntropy (Phi (∑ _ : Fin 1, (1 : ℝ) • rho)) -
      (∑ _ : Fin 1, (1 : ℝ) * vnEntropy (Phi rho)) = 0
    simp

/-- Sanity: the imported code carries normalized input states and a positive message count. -/
example {A : Matrix I I ℂ} {alpha : ℝ} {n : ℕ}
    (c : CostConstrainedCode I O A alpha n) (w : Fin c.messages) :
    0 < c.messages ∧ IsDensityMatrix (c.code.word w) :=
  ⟨c.code.positive, c.code.state w⟩

/-- Sanity: a singleton feasible set has its objective value. -/
example {X : Type*} (x : X) (f : X → ℝ) : maxValue {x} f = f x := by
  simp [maxValue]

/-- Sanity: cross-sector output coherences of Shor's map vanish. -/
example (Phi : Superop I O) (E : Matrix I I ℂ) (q : ℝ) (d : ℕ)
    (X : Matrix (I × Fin d) (I × Fin d) ℂ) (i : O) (j : Option (Fin d)) :
    shor Phi E q d X (.inl i) (.inr j) = 0 := rfl

/-- Sanity: the zero-copy additive observable is zero. The results use positive n. -/
example (A : Matrix I I ℂ) : blockObservable A 0 = 0 := by
  ext x y
  simp [blockObservable]

/-- Sanity: the prefix does not evaluate capacities at d=0 or d=1. -/
example (Phi : Superop I O) (E : Matrix I I ℂ) (lam : ℝ) :
    extensionSequence Phi E lam 0 = 0 ∧ extensionSequence Phi E lam 1 = 0 := by
  simp [extensionSequence, admissibleTail]

end QAlgorithms.Papers.Independent.Gap48.P46


