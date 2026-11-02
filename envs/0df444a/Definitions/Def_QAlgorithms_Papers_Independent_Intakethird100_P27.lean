-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P27
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P27
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T08:13:15.057397+00:00
-- url     : https://prove2.me/theorems/c467f677-b53b-4d8e-b827-a2265bddba4e
-- title:
--   Definitions for Quantum rate distortion coding with auxiliary resources
-- statement:
--   The objects the formalized statements of *Quantum rate distortion coding with auxiliary resources* (arXiv:1212.5316) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `DistortionSource`: PDF pp.3--4: a normalized source purification, with reference isomorphic to A, and an arbitrary positive distortion observable on the reference and B. The source density is the actual A marginal, traceLeft (pureDensity psi).
--   - `IidRegister`: PDF p.4: n copies of a register. Only positive n enter operational codes.
--   - `testOutput`: PDF p.4: the single-letter output includes the untouched purifying reference.
--   - `observableDistortion`: PDF p.4: the expectation of delta; no upper bound delta <= I is imposed.
--   - `letterMarginal`: PDF p.4: one-letter reference/reconstruction marginal, tracing all other letters jointly. The kept and forgotten coordinates form a bijective partition.
--   - `averageDistortion`: PDF p.4: average distortion from the actual n-letter reference/output state. The total formula is zero at n=0; every code and block minimum uses n>=1.
--   - `LossyAssistance`: PDF pp.4,6--7: the three distinct allowed auxiliary-resource models.
--   - `LossyCode`: PDF pp.3--4,6--7: actual CPTP encoding and decoding with one quantum message W, one dephased classical message M, and an independent shared resource. The latter two registers are constrained to dimension one when unavailable. Rectangular CPTP maps include arbitrary local scratch systems and discarding.
--   - `LossyCode.Allowed`: PDF pp.4,6: availability constraints, independent of the source and distortion. Unlimited forward classical communication supplies no prior entanglement.
--   - `LossyCode.initial`: PDF pp.4,7: iid purification tensor an independent shared density matrix. The outer register is R^n; Alice owns A^n and the first shared half.
--   - `LossyCode.output`: PDF pp.4,7: actual encoding, forward transmission of MW, and decoding with Bob's resource half; all off-diagonal R^n blocks are preserved.
--   - `LossyAchievable`: PDF p.4, (8): vanishing rate/distortion slack, for all sufficiently large positive blocklengths. The code is selected before any reference indices. No entropic bound occurs in this operational definition.
--   - `rateDistortion`: PDF p.4: infimum over operationally achievable qubit rates. ENNReal keeps infeasibility at infinity and makes zero-weight time-sharing endpoints exact.
--   - `sourceFidelity`: PDF p.4, (7): source-dependent entanglement fidelity, for an arbitrary unit purification rather than only a maximally mixed qubit source.
--   - `iidChannelOutput`: PDF p.6, (16): arbitrary block channel applied to the actual iid purification.
--   - `formationBlockValue`: PDF p.6, (14): normalized block formation infimum over exactly the feasible CPTP maps. For positive k, empty feasible sets have value infinity, never the real sInf default. At k=0 the total expression is zero and is never used.
--   - `isotropicEntropy`: PDF p.8: Bell-error probability vector and its Shannon entropy in bits. Zero probabilities contribute zero, including at D=0.
--   - `purificationValues`: PDF pp.3,10, (3),(22): costs of all finite bipartite purifications, with arbitrary positive ancillary dimensions. The actual AB marginal is fixed.
--   - `purificationCost`: PDF p.3, (3): entanglement of purification, taking a genuine infimum over all finite extensions. The density matrices used in the bound are normalized.
--   - `purificationBlockValue`: PDF pp.4,17, (9),(50): normalized block purification objective, over all feasible block channels rather than just tensor powers of a one-letter channel.
--   - `regularizedPurification`: PDF p.17, (50): the regularized expression; positive blocklengths only. The convexity theorem below asserts actual convergence as well as convexity.
--   - `isotropicStrategyCost`: PDF p.10, (22) and footnote 2: use the accepted isotropic state with local dimension 2 and Bell overlap 1-D, so its eigenvalues are 1-D,D/3,D/3,D/3. Use E_p only up to 3/4; a constant reconstruction costs zero thereafter. Mixture distortions are restricted to [0,1].
--   - `isotropicConvexUpper`: PDF p.10, Remark 5 and footnote 2: all finite time-sharing mixtures whose average distortion is at most D. This is a lower convex envelope, not a sampled plot, and no numerical assertion about evaluating E_p is made.
--   - `outputWithSide`: PDF p.14: apply N to A in R,(A,B), preserving all R and B coherences.
--   - `conditionalOutputInformation`: PDF pp.3,14: I(R;C|B), from the four actual channel-output marginals.
-- source:
--   Quantum rate distortion coding with auxiliary resources, arXiv:1212.5316v3, https://arxiv.org/abs/1212.5316v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P37

/-!
Statements from Wilde--Datta--Hsieh--Winter, arXiv:1212.5316v3.
All new definitions are confined to this paper. Registers are finite nonempty
basis types in the results. Entropies and message costs are in bits. Operational
rates are independent infima over actual CPTP codes, taking value infinity below
feasible distortion. Compilation is pending the mechanical batch handoff.
The entropy-duality and redistribution nodes reuse accepted results in items.json.
Seven other nodes are explicitly deferred in HARD.md and GAPS.json.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P27

open Filter
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P19
  (first marginalRB mutualInformation bipartiteBlock epr)
open QAlgorithms.Papers.Independent.Information100.P08 (formation)
open QAlgorithms.Papers.Independent.Gap48.P20 (redistributionMarginal)
open QAlgorithms.Papers.Independent.Bridge50.P37 (isotropicState normalizedEntangledProjection)

/-- PDF pp.3--4: a normalized source purification, with reference isomorphic to
A, and an arbitrary positive distortion observable on the reference and B.
The source density is the actual A marginal, traceLeft (pureDensity psi). -/
structure DistortionSource (A B : Type) [Fintype A] [Fintype B] where
  psi : EuclideanSpace ℂ (A × A)
  normalized : ‖psi‖ = 1
  delta : Matrix (A × B) (A × B) ℂ
  positive : delta.PosSemidef

/-- PDF p.4: n copies of a register. Only positive n enter operational codes. -/
abbrev IidRegister (A : Type) (n : ℕ) := Fin n → A

/-- PDF p.4: the single-letter output includes the untouched purifying reference. -/
def testOutput {A B : Type} [Fintype A] [Fintype B]
    (S : DistortionSource A B) (N : Superop A B) : Matrix (A × B) (A × B) ℂ :=
  idTensorSuperop N (pureDensity S.psi)

/-- PDF p.4: the expectation of delta; no upper bound delta <= I is imposed. -/
def observableDistortion {A B : Type} [Fintype A] [Fintype B]
    (S : DistortionSource A B) (N : Superop A B) : ℝ :=
  effectProb S.delta (testOutput S N)

/-- PDF p.4: one-letter reference/reconstruction marginal, tracing all other
letters jointly. The kept and forgotten coordinates form a bijective partition. -/
def letterMarginal {A B : Type} {n : ℕ}
    [Fintype A] [Fintype B] (X : Matrix (IidRegister A n × IidRegister B n)
      (IidRegister A n × IidRegister B n) ℂ) (i : Fin n) : Matrix (A × B) (A × B) ℂ :=
  redistributionMarginal X (fun p => (p.1 i, p.2 i))
    (fun p => fun j : {j : Fin n // j ≠ i} => (p.1 j.1, p.2 j.1))

/-- PDF p.4: average distortion from the actual n-letter reference/output state.
The total formula is zero at n=0; every code and block minimum uses n>=1. -/
def averageDistortion {A B : Type} [Fintype A] [Fintype B]
    (S : DistortionSource A B) {n : ℕ}
    (X : Matrix (IidRegister A n × IidRegister B n) (IidRegister A n × IidRegister B n) ℂ) : ℝ :=
  (∑ i : Fin n, effectProb S.delta (letterMarginal X i)) / (n : ℝ)

/-- PDF pp.4,6--7: the three distinct allowed auxiliary-resource models. -/
inductive LossyAssistance where
  | unassisted
  | entanglement
  | classical
  deriving DecidableEq

/-- PDF pp.3--4,6--7: actual CPTP encoding and decoding with one quantum message
W, one dephased classical message M, and an independent shared resource.
The latter two registers are constrained to dimension one when unavailable.
Rectangular CPTP maps include arbitrary local scratch systems and discarding. -/
structure LossyCode (A B : Type) [Fintype A] [Fintype B] (n : ℕ) where
  quantumDim : ℕ
  classicalDim : ℕ
  sharedDim : ℕ
  quantum_positive : 0 < quantumDim
  classical_positive : 0 < classicalDim
  shared_positive : 0 < sharedDim
  resource : Matrix (Fin sharedDim × Fin sharedDim) (Fin sharedDim × Fin sharedDim) ℂ
  resource_density : IsDensityMatrix resource
  encoder : Superop (IidRegister A n × Fin sharedDim) (Fin classicalDim × Fin quantumDim)
  decoder : Superop ((Fin classicalDim × Fin quantumDim) × Fin sharedDim) (IidRegister B n)
  encoder_channel : IsChannel encoder
  decoder_channel : IsChannel decoder
  classical_message : ∀ X m m' w w', m ≠ m' → encoder X (m, w) (m', w') = 0

/-- PDF pp.4,6: availability constraints, independent of the source and distortion.
Unlimited forward classical communication supplies no prior entanglement. -/
def LossyCode.Allowed {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (P : LossyCode A B n) : LossyAssistance → Prop
  | .unassisted => P.classicalDim = 1 ∧ P.sharedDim = 1
  | .entanglement => P.classicalDim = 1
  | .classical => P.sharedDim = 1

/-- PDF pp.4,7: iid purification tensor an independent shared density matrix.
The outer register is R^n; Alice owns A^n and the first shared half. -/
def LossyCode.initial {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (P : LossyCode A B n) (S : DistortionSource A B) :
    Matrix (IidRegister A n × ((IidRegister A n × Fin P.sharedDim) × Fin P.sharedDim))
      (IidRegister A n × ((IidRegister A n × Fin P.sharedDim) × Fin P.sharedDim)) ℂ :=
  fun p q =>
    (∏ i, pureDensity S.psi (p.1 i, p.2.1.1 i) (q.1 i, q.2.1.1 i)) *
      P.resource (p.2.1.2, p.2.2) (q.2.1.2, q.2.2)

/-- PDF pp.4,7: actual encoding, forward transmission of MW, and decoding with
Bob's resource half; all off-diagonal R^n blocks are preserved. -/
def LossyCode.output {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (P : LossyCode A B n) (S : DistortionSource A B) :
    Matrix (IidRegister A n × IidRegister B n) (IidRegister A n × IidRegister B n) ℂ :=
  idTensorSuperop (P.decoder ∘ first P.encoder) (P.initial S)

/-- PDF p.4, (8): vanishing rate/distortion slack, for all sufficiently large
positive blocklengths. The code is selected before any reference indices.
No entropic bound occurs in this operational definition. -/
def LossyAchievable {A B : Type} [Fintype A] [Fintype B]
    (S : DistortionSource A B) (a : LossyAssistance) (rate D : ℝ) : Prop :=
  0 ≤ rate ∧ 0 ≤ D ∧ ∀ eps > (0 : ℝ), ∀ slack > (0 : ℝ), ∃ n0 : ℕ,
    ∀ n ≥ n0, 1 ≤ n → ∃ P : LossyCode A B n, P.Allowed a ∧
      Real.logb 2 (P.quantumDim : ℝ) ≤ (n : ℝ) * (rate + slack) ∧
      averageDistortion S (P.output S) ≤ D + eps

/-- PDF p.4: infimum over operationally achievable qubit rates. ENNReal keeps
infeasibility at infinity and makes zero-weight time-sharing endpoints exact. -/
def rateDistortion {A B : Type} [Fintype A] [Fintype B]
    (S : DistortionSource A B) (a : LossyAssistance) (D : ℝ) : ℝ≥0∞ :=
  ⨅ (r : ℝ) (_ : LossyAchievable S a r D), ENNReal.ofReal r

/-- PDF p.4, (7): source-dependent entanglement fidelity, for an arbitrary unit
purification rather than only a maximally mixed qubit source. -/
def sourceFidelity {R A : Type} [Fintype R] [Fintype A]
    (v : EuclideanSpace ℂ (R × A)) (N : Superop A A) : ℝ :=
  (∑ i, ∑ j, conj (v i) * idTensorSuperop N (pureDensity v) i j * v j).re

/-- PDF p.6, (16): arbitrary block channel applied to the actual iid purification. -/
def iidChannelOutput {A B : Type} [Fintype A] [Fintype B]
    (S : DistortionSource A B) (k : ℕ) (N : Superop (IidRegister A k) (IidRegister B k)) :
    Matrix (IidRegister A k × IidRegister B k) (IidRegister A k × IidRegister B k) ℂ :=
  idTensorSuperop N (bipartiteBlock k (pureDensity S.psi))

/-- PDF p.6, (14): normalized block formation infimum over exactly the feasible
CPTP maps. For positive k, empty feasible sets have value infinity, never the
real sInf default. At k=0 the total expression is zero and is never used. -/
def formationBlockValue {A B : Type} [Fintype A] [Fintype B]
    (S : DistortionSource A B) (D : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((k : ℝ)⁻¹) *
    ⨅ (N : Superop (IidRegister A k) (IidRegister B k))
      (_ : IsChannel N ∧ averageDistortion S (iidChannelOutput S k N) ≤ D),
        ENNReal.ofReal (formation (iidChannelOutput S k N))

/-- PDF p.8: Bell-error probability vector and its Shannon entropy in bits.
Zero probabilities contribute zero, including at D=0. -/
def isotropicEntropy (D : ℝ) : ℝ :=
  let p : Fin 4 → ℝ := ![1 - D, D / 3, D / 3, D / 3];
  -(∑ i, p i * Real.logb 2 (p i))

/-- PDF pp.3,10, (3),(22): costs of all finite bipartite purifications, with
arbitrary positive ancillary dimensions. The actual AB marginal is fixed. -/
def purificationValues {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) : Set ℝ≥0∞ :=
  {r | ∃ (u v : ℕ) (_ : 0 < u) (_ : 0 < v)
      (psi : EuclideanSpace ℂ ((A × Fin u) × (B × Fin v))),
    ‖psi‖ = 1 ∧
    redistributionMarginal (pureDensity psi) (fun p => (p.1.1, p.2.1))
      (fun p => (p.1.2, p.2.2)) = rho ∧
    r = ENNReal.ofReal (vnEntropy (traceRight (pureDensity psi)))}

/-- PDF p.3, (3): entanglement of purification, taking a genuine infimum over
all finite extensions. The density matrices used in the bound are normalized. -/
def purificationCost {A B : Type} [Fintype A] [Fintype B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ≥0∞ :=
  sInf (purificationValues rho)

/-- PDF pp.4,17, (9),(50): normalized block purification objective, over all
feasible block channels rather than just tensor powers of a one-letter channel. -/
def purificationBlockValue {A B : Type} [Fintype A] [Fintype B]
    (S : DistortionSource A B) (D : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((k : ℝ)⁻¹) *
    ⨅ (N : Superop (IidRegister A k) (IidRegister B k))
      (_ : IsChannel N ∧ averageDistortion S (iidChannelOutput S k N) ≤ D),
        purificationCost (iidChannelOutput S k N)

/-- PDF p.17, (50): the regularized expression; positive blocklengths only.
The convexity theorem below asserts actual convergence as well as convexity. -/
def regularizedPurification {A B : Type} [Fintype A] [Fintype B]
    (S : DistortionSource A B) (D : ℝ) : ℝ≥0∞ :=
  liminf (fun k => purificationBlockValue S D (k + 1)) atTop

/-- PDF p.10, (22) and footnote 2: use the accepted isotropic state with local
dimension 2 and Bell overlap 1-D, so its eigenvalues are 1-D,D/3,D/3,D/3.
Use E_p only up to 3/4; a constant reconstruction costs zero thereafter.
Mixture distortions are restricted to [0,1]. -/
def isotropicStrategyCost (D : ℝ) : ℝ≥0∞ :=
  if D ≤ 3 / 4 then purificationCost (isotropicState 2 (1 - D)) else 0

/-- PDF p.10, Remark 5 and footnote 2: all finite time-sharing mixtures whose
average distortion is at most D. This is a lower convex envelope, not a sampled
plot, and no numerical assertion about evaluating E_p is made. -/
def isotropicConvexUpper (D : ℝ) : ℝ≥0∞ :=
  sInf {r | ∃ (m : ℕ) (_ : 0 < m) (p d : Fin m → ℝ),
    (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧
    (∀ i, 0 ≤ d i ∧ d i ≤ 1) ∧ (∑ i, p i * d i) ≤ D ∧
    r = ∑ i, ENNReal.ofReal (p i) * isotropicStrategyCost (d i)}

/-- PDF p.14: apply N to A in R,(A,B), preserving all R and B coherences. -/
def outputWithSide {R A B C : Type} (N : Superop A C)
    (phi : EuclideanSpace ℂ (R × (A × B))) :
    Matrix (R × (C × B)) (R × (C × B)) ℂ :=
  idTensorSuperop (first N) (pureDensity phi)

/-- PDF pp.3,14: I(R;C|B), from the four actual channel-output marginals. -/
def conditionalOutputInformation {R A B C : Type}
    [Fintype R] [Fintype A] [Fintype B] [Fintype C]
    (N : Superop A C) (phi : EuclideanSpace ℂ (R × (A × B))) : ℝ :=
  let X := outputWithSide N phi
  vnEntropy (marginalRB X) + vnEntropy (traceLeft X) -
    vnEntropy (traceLeft (traceLeft X)) - vnEntropy X

/-- Small sanity example: the zero-length helper has zero average distortion.
Every operational theorem excludes this blocklength. -/

example {A B : Type} [Fintype A] [Fintype B] (S : DistortionSource A B)
    (X : Matrix (IidRegister A 0 × IidRegister B 0) (IidRegister A 0 × IidRegister B 0) ℂ) :
    averageDistortion S X = 0 := by
  simp [averageDistortion]

example {A : Type} [Fintype A] (S : DistortionSource A A) :
    testOutput S (fun X => X) = pureDensity S.psi := by
  ext p q
  rfl

example {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (P : LossyCode A B n) : P.Allowed .classical ↔ P.sharedDim = 1 := Iff.rfl

example {A B : Type} [Fintype A] [Fintype B] {n : ℕ}
    (P : LossyCode A B n) : P.Allowed .unassisted → P.sharedDim = 1 := by
  exact And.right

example : isotropicEntropy 0 = 0 := by
  norm_num [isotropicEntropy, Fin.sum_univ_four]
  change -((0 : ℝ) * Real.logb 2 0) + -(0 * Real.logb 2 0) = 0
  simp

example : isotropicStrategyCost 1 = 0 := by
  norm_num [isotropicStrategyCost]

example : isotropicState 2 1 = normalizedEntangledProjection (Fin 2) := by
  simp [isotropicState]

example {R A B : Type} [Fintype A] (phi : EuclideanSpace ℂ (R × (A × B))) :
    outputWithSide (fun X => X) phi = pureDensity phi := by
  ext p q
  rfl

end QAlgorithms.Papers.Independent.Intakethird100.P27


