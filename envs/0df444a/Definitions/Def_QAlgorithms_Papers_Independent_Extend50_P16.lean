-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P16
-- name    : QAlgorithms_Papers_Independent_Extend50_P16
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T17:01:58.412373+00:00
-- url     : https://prove2.me/theorems/6188a30d-0b85-4c3a-bb21-21db7b65242f
-- title:
--   Definitions for Cost of quantum entanglement simplified
-- statement:
--   The objects the formalized statements of *Cost of quantum entanglement simplified* (arXiv:2007.14270) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BipMat`: PDF pp.2,11: finite matrices in a fixed product basis, with A first.
--   - `LoewnerLE`: PDF p.11, Definition 1: Loewner comparison, rather than entrywise order.
--   - `extendedLogTwo`: PDF pp.3,11,24: base-two logarithm retaining both extended endpoints.
--   - `logTwoReal`: PDF p.3: finite scalar specialization; only nonnegative arguments are used.
--   - `HasFiniteKrausSum`: PDF pp.2,13: in finite dimensions CP is precisely a finite Kraus sum; there is no trace-preserving condition on the Kraus family here.
--   - `IsCPPTChannel`: PDF pp.2,13: CPTP, and the partial-transpose conjugate is CP. This is complete PPT preservation, not preservation of PPT inputs alone.
--   - `exactPptPreparationCost`: PDF pp.3,8: exact deterministic one-shot operational preparation cost. The infimum of an empty finite-cost set is +infinity in EReal.
--   - `costRate`: PDF p.8, (S2): positive blocklengths only, with extended costs retained.
--   - `exactCost`: PDF pp.3,8, (4),(S2): operational asymptotic cost is the limsup, not κ-entanglement by definition.
--   - `KappaFeasible`: PDF p.11, Definition 1: one auxiliary positive operator S for both inequalities.
--   - `kappaEntanglement`: PDF p.11, (S1): independently defined conic entanglement measure.
--   - `bipartiteLogNegativity`: PDF p.8, (S4): logarithmic negativity in bits.
--   - `sdpMap`: PDF p.15, (S16): the concrete map Ψ(S)=diag(T_B(S),T_B(S)).
--   - `sdpC`: PDF p.15, (S16): C=diag(T_B(rho),-T_B(rho)), constructed from rho.
--   - `sdpD`: PDF p.15, (S16): the standard-form objective matrix D is the identity.
--   - `kappaSdpValue`: PDF pp.13,15, (S12),(S15)-(S16): objective of the constructed SDP. The nonnegative extended infimum retains the empty-feasible-set convention.
--   - `convexityFirst`: PDF pp.4,21, (S84): the first fixed two-qubit state rho_1=Phi_2.
--   - `convexitySecond`: PDF pp.4,21, (S85): rho_2=(|00><00|+|11><11|)/2.
--   - `convexityAverage`: PDF pp.4,21, (S86): the actual average of the two specified states.
--   - `monogamyVector`: PDF pp.4,21, (S89): the normalized vector across the cut A:BC.
--   - `monogamyWhole`: PDF p.21: the pure density of the fixed three-qubit vector, cut A:BC.
--   - `monogamyAB`: PDF p.21, (S92): computed AB marginal, tracing C out of the fixed state.
--   - `monogamyAC`: PDF p.21, (S93): computed AC marginal, tracing B out of the same state.
--   - `antisymmetricFirst`: PDF p.22, Appendix E (S2): first unit antisymmetric two-qutrit vector.
--   - `antisymmetricSecond`: PDF p.22, Appendix E (S3): second unit antisymmetric two-qutrit vector.
--   - `antisymmetricFamily`: PDF p.22, Appendix F (S1): the specified rank-two family; 0<=p<=1 is required when it is called a density operator.
--   - `rankTwoAntisymmetricState`: PDF pp.4,22, (15), Appendix E (S1): the equally weighted state rho_v.
--   - `maxRains`: PDF p.22, Appendix E (S4), citing [27]: max-Rains quantity. Its unlogged form is inf{||T_B(X)||_1 : X >= rho}; see [27], arXiv:1601.07940v4, PDF p.2, (9). No normalized-state constraint is put on X.
--   - `leastEigenvalue`: PDF p.8, (S5): least eigenvalue of a finite Hermitian matrix, written as the infimum of its unit-vector Rayleigh quotients. Used only on Hermitian matrices in positive dimension; that set is nonempty and bounded below.
--   - `binegativity`: PDF p.8, (S5): modulus of the partial transpose, transposed back. The outer transpose is after the modulus.
--   - `priorUpperBound`: PDF p.8, (S5): prior upper-bound quantity Z; the dimension factor is d_A*d_B.
--   - `exactDistillable`: PDF pp.4,22: deterministic exact distillation, the counterpart of Appendix A's exact preparation. A sequence uses every positive blocklength; the achieved asymptotic yield is its extended liminf, with positive output ranks.
-- source:
--   Cost of quantum entanglement simplified, arXiv:2007.14270v1, https://arxiv.org/abs/2007.14270v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80

/-!
Statements from Wang and Wilde, arXiv:2007.14270v1. Page numbers are PDF pages.
The local matrix model is used only for the source's finite-dimensional results.
General separable-space nodes are explicitly deferred in HARD.md and GAPS.json.
Operational preparation and distillation are defined through actual C-PPT-P maps;
κ-entanglement is independently defined by its positive-operator optimization.
All entanglement values are extended real numbers. Compilation is pending handoff.
The second-party transpose, maximally entangled resource and grouped matrix powers
are imported from pinned accepted modules; no result from those papers is assumed.
Other similarly named accepted objects have different domains or meanings; the
extended logarithm and paper-specific optimizations below retain distinct names.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P16

open QAlgorithms Filter
open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)
open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)
open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)
open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.2,11: finite matrices in a fixed product basis, with A first. -/
abbrev BipMat (A B : Type*) := Matrix (A × B) (A × B) ℂ

/-- PDF p.11, Definition 1: Loewner comparison, rather than entrywise order. -/
def LoewnerLE {I : Type*} [Fintype I] (X Y : Matrix I I ℂ) : Prop :=
  (Y - X).PosSemidef

/-- PDF pp.3,11,24: base-two logarithm retaining both extended endpoints. -/
def extendedLogTwo (x : ℝ≥0∞) : EReal :=
  ENNReal.log x * (((Real.log 2)⁻¹ : ℝ) : EReal)

/-- PDF p.3: finite scalar specialization; only nonnegative arguments are used. -/
def logTwoReal (x : ℝ) : EReal := extendedLogTwo (ENNReal.ofReal x)

/-- PDF pp.2,13: in finite dimensions CP is precisely a finite Kraus sum;
there is no trace-preserving condition on the Kraus family here. -/
def HasFiniteKrausSum {I J : Type*} [Fintype I] [Fintype J] (P : Superop I J) : Prop :=
  ∃ (m : ℕ) (K : Fin m → Matrix J I ℂ), ∀ X, P X = krausApply K X

/-- PDF pp.2,13: CPTP, and the partial-transpose conjugate is CP.
This is complete PPT preservation, not preservation of PPT inputs alone. -/
def IsCPPTChannel {A B C D : Type*} [Fintype A] [Fintype B]
    [Fintype C] [Fintype D] (P : Superop (A × B) (C × D)) : Prop :=
  IsChannel P ∧ HasFiniteKrausSum (fun X => partialTranspose (P (partialTranspose X)))

/-- PDF pp.3,8: exact deterministic one-shot operational preparation cost.
The infimum of an empty finite-cost set is +infinity in EReal. -/
def exactPptPreparationCost {A B : Type*} [Fintype A] [Fintype B] (rho : BipMat A B) : EReal :=
  sInf {v : EReal | ∃ d : ℕ, 0 < d ∧
    ∃ P : Superop (Fin d × Fin d) (A × B),
      IsCPPTChannel P ∧ P (maximallyEntangled d) = rho ∧
        v = logTwoReal d}

/-- PDF p.8, (S2): positive blocklengths only, with extended costs retained. -/
def costRate {A B : Type*} [Fintype A] [Fintype B] (rho : BipMat A B)
    (n : ℕ) : EReal :=
  ((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * exactPptPreparationCost (groupedPower rho (n + 1))

/-- PDF pp.3,8, (4),(S2): operational asymptotic cost is the limsup,
not κ-entanglement by definition. -/
def exactCost {A B : Type*} [Fintype A] [Fintype B] (rho : BipMat A B) : EReal :=
  Filter.limsup (costRate rho) Filter.atTop

/-- PDF p.11, Definition 1: one auxiliary positive operator S for both inequalities. -/
def KappaFeasible {A B : Type*} [Fintype A] [Fintype B]
    (rho S : BipMat A B) : Prop :=
  S.PosSemidef ∧ LoewnerLE (-partialTranspose S) (partialTranspose rho) ∧
    LoewnerLE (partialTranspose rho) (partialTranspose S)

/-- PDF p.11, (S1): independently defined conic entanglement measure. -/
def kappaEntanglement {A B : Type*} [Fintype A] [Fintype B] (rho : BipMat A B) : EReal :=
  sInf {v : EReal | ∃ S : BipMat A B, KappaFeasible rho S ∧
    v = logTwoReal S.trace.re}

/-- PDF p.8, (S4): logarithmic negativity in bits. -/
def bipartiteLogNegativity {A B : Type*} [Fintype A] [Fintype B]
    (rho : BipMat A B) : EReal :=
  logTwoReal (traceNorm (partialTranspose rho))

/-- PDF p.15, (S16): the concrete map Ψ(S)=diag(T_B(S),T_B(S)). -/
def sdpMap {A B : Type*} (S : BipMat A B) :
    Matrix (Bool × (A × B)) (Bool × (A × B)) ℂ :=
  fun p q => if p.1 = q.1 then partialTranspose S p.2 q.2 else 0

/-- PDF p.15, (S16): C=diag(T_B(rho),-T_B(rho)), constructed from rho. -/
def sdpC {A B : Type*} (rho : BipMat A B) :
    Matrix (Bool × (A × B)) (Bool × (A × B)) ℂ :=
  fun p q => if p.1 = q.1 then
    if p.1 = false then partialTranspose rho p.2 q.2
    else -partialTranspose rho p.2 q.2 else 0

/-- PDF p.15, (S16): the standard-form objective matrix D is the identity. -/
def sdpD (A B : Type*) [DecidableEq A] [DecidableEq B] : BipMat A B := 1

/-- PDF pp.13,15, (S12),(S15)-(S16): objective of the constructed SDP.
The nonnegative extended infimum retains the empty-feasible-set convention. -/
def kappaSdpValue {A B : Type*} [Fintype A] [Fintype B] (rho : BipMat A B) : ℝ≥0∞ :=
  sInf {s : ℝ≥0∞ | ∃ S : BipMat A B, S.PosSemidef ∧
    LoewnerLE (sdpC rho) (sdpMap S) ∧
      s = ENNReal.ofReal ((sdpD A B * S).trace.re)}

/-- PDF pp.4,21, (S84): the first fixed two-qubit state rho_1=Phi_2. -/
def convexityFirst : BipMat (Fin 2) (Fin 2) := maximallyEntangled 2

/-- PDF pp.4,21, (S85): rho_2=(|00><00|+|11><11|)/2. -/
def convexitySecond : BipMat (Fin 2) (Fin 2) :=
  fun p q => if p = q ∧ p.1 = p.2 then (1 / 2 : ℂ) else 0

/-- PDF pp.4,21, (S86): the actual average of the two specified states. -/
def convexityAverage : BipMat (Fin 2) (Fin 2) :=
  (1 / 2 : ℂ) • (convexityFirst + convexitySecond)

/-- PDF pp.4,21, (S89): the normalized vector across the cut A:BC. -/
def monogamyVector : EuclideanSpace ℂ (Fin 2 × (Fin 2 × Fin 2)) :=
  WithLp.toLp 2 fun p =>
    if p = (0, (0, 0)) ∨ p = (0, (1, 1)) then (1 / 2 : ℂ)
    else if p = (1, (1, 0)) then ((Real.sqrt 2 / 2 : ℝ) : ℂ) else 0

/-- PDF p.21: the pure density of the fixed three-qubit vector, cut A:BC. -/
def monogamyWhole : BipMat (Fin 2) (Fin 2 × Fin 2) := pureDensity monogamyVector

/-- PDF p.21, (S92): computed AB marginal, tracing C out of the fixed state. -/
def monogamyAB : BipMat (Fin 2) (Fin 2) :=
  fun p q => ∑ c : Fin 2, monogamyWhole (p.1, (p.2, c)) (q.1, (q.2, c))

/-- PDF p.21, (S93): computed AC marginal, tracing B out of the same state. -/
def monogamyAC : BipMat (Fin 2) (Fin 2) :=
  fun p q => ∑ b : Fin 2, monogamyWhole (p.1, (b, p.2)) (q.1, (b, q.2))

/-- PDF p.22, Appendix E (S2): first unit antisymmetric two-qutrit vector. -/
def antisymmetricFirst : EuclideanSpace ℂ (Fin 3 × Fin 3) :=
  WithLp.toLp 2 fun p => if p = (0, 1) then ((Real.sqrt 2)⁻¹ : ℂ)
    else if p = (1, 0) then -((Real.sqrt 2)⁻¹ : ℂ) else 0

/-- PDF p.22, Appendix E (S3): second unit antisymmetric two-qutrit vector. -/
def antisymmetricSecond : EuclideanSpace ℂ (Fin 3 × Fin 3) :=
  WithLp.toLp 2 fun p => if p = (0, 2) then ((Real.sqrt 2)⁻¹ : ℂ)
    else if p = (2, 0) then -((Real.sqrt 2)⁻¹ : ℂ) else 0

/-- PDF p.22, Appendix F (S1): the specified rank-two family; 0<=p<=1
is required when it is called a density operator. -/
def antisymmetricFamily (p : ℝ) : BipMat (Fin 3) (Fin 3) :=
  (p : ℂ) • pureDensity antisymmetricFirst +
    ((1 - p : ℝ) : ℂ) • pureDensity antisymmetricSecond

/-- PDF pp.4,22, (15), Appendix E (S1): the equally weighted state rho_v. -/
def rankTwoAntisymmetricState : BipMat (Fin 3) (Fin 3) := antisymmetricFamily (1 / 2)

/-- PDF p.22, Appendix E (S4), citing [27]: max-Rains quantity.
Its unlogged form is inf{||T_B(X)||_1 : X >= rho}; see [27],
arXiv:1601.07940v4, PDF p.2, (9). No normalized-state constraint is put on X. -/
def maxRains {A B : Type*} [Fintype A] [Fintype B] (rho : BipMat A B) : EReal :=
  extendedLogTwo (sInf {t : ℝ≥0∞ | ∃ X : BipMat A B, LoewnerLE rho X ∧
    t = ENNReal.ofReal (traceNorm (partialTranspose X))})

/-- PDF p.8, (S5): least eigenvalue of a finite Hermitian matrix, written
as the infimum of its unit-vector Rayleigh quotients. Used only on Hermitian
matrices in positive dimension; that set is nonempty and bounded below. -/
def leastEigenvalue {I : Type*} [Fintype I] [Nonempty I] (X : Matrix I I ℂ) : ℝ :=
  sInf {r : ℝ | ∃ v : EuclideanSpace ℂ I, ‖v‖ = 1 ∧
    r = (∑ i, ∑ j, conj (v i) * X i j * v j).re}

/-- PDF p.8, (S5): modulus of the partial transpose, transposed back.
The outer transpose is after the modulus. -/
def binegativity {A B : Type*} [Fintype A] [Fintype B] (rho : BipMat A B) : BipMat A B :=
  partialTranspose (cfc Real.sqrt ((partialTranspose rho)ᴴ * partialTranspose rho))

/-- PDF p.8, (S5): prior upper-bound quantity Z; the dimension factor is d_A*d_B. -/
def priorUpperBound {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (rho : BipMat A B) : ℝ :=
  traceNorm (partialTranspose rho) +
    ((Fintype.card A * Fintype.card B : ℕ) : ℝ) * max 0 (-leastEigenvalue (binegativity rho))

/-- PDF pp.4,22: deterministic exact distillation, the counterpart of
Appendix A's exact preparation. A sequence uses every positive blocklength;
the achieved asymptotic yield is its extended liminf, with positive output ranks. -/
def exactDistillable {A B : Type*} [Fintype A] [Fintype B] (rho : BipMat A B) : EReal :=
  sSup {v : EReal | ∃ d : ℕ → ℕ,
    (∀ n, 0 < d n ∧ ∃ P : Superop
      ((Fin (n + 1) → A) × (Fin (n + 1) → B)) (Fin (d n) × Fin (d n)),
      IsCPPTChannel P ∧ P (groupedPower rho (n + 1)) = maximallyEntangled (d n)) ∧
    v = Filter.liminf (fun n =>
      (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : EReal) * logTwoReal (d n))) Filter.atTop}

/-! Small sanity checks for the local model. -/

example {A B : Type*} (X : BipMat A B) :
    partialTranspose (partialTranspose X) = X := rfl

example : extendedLogTwo 1 = 0 := by simp [extendedLogTwo]

example : maximallyEntangled 1 (0, 0) (0, 0) = 1 := by
  simp [QAlgorithms.Papers.Independent.Dependency50.P41.maximallyEntangled,
    finiteMaxEntangled, pureDensity]

example {A B : Type*} (rho : BipMat A B) (p q : (Fin 0 → A) × (Fin 0 → B)) :
    groupedPower rho 0 p q = 1 := by simp [QAlgorithms.Papers.Independent.Information100.P80.groupedPower]

example {A B : Type*} (rho : BipMat A B) (p q : A × B) :
    sdpC rho (true, p) (true, q) = -partialTranspose rho p q := rfl

example {A B : Type*} (S : BipMat A B) (p q : A × B) :
    sdpMap S (false, p) (true, q) = 0 := rfl

end QAlgorithms.Papers.Independent.Extend50.P16


