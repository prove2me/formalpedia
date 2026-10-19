-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
-- name    : QAlgorithms_Papers_Independent_Information100_P27
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T10:16:04.737766+00:00
-- url     : https://prove2.me/theorems/237bdebd-2f87-4762-b176-77031722ce70
-- title:
--   Definitions for Static classical-quantum- entanglement trade-offs: an entropic converse and single-letter characterizations
-- statement:
--   The objects the formalized statements of *Static classical-quantum- entanglement trade-offs: an entropic converse and single-letter characterizations* (arXiv:2609.23298) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsProbability`: PDF p.6: a finite probability distribution, allowing zero weights.
--   - `average`: PDF pp.6,39: average of a finite family of operators.
--   - `IsPureFamily`: PDF p.39: purity of every conditional environmental state.
--   - `memoryEnvironment`: PDF p.39, (8.48): marginal on the memory and environment.
--   - `labelInformation`: PDF pp.39,75: I(T;Y) as a Holevo quantity for classical Y.
--   - `memoryScore`: PDF p.39: alpha I(T;E) - I(T;Y), evaluated on the extension (8.48).
--   - `bottleneckValues`: PDF p.39: all unrestricted-memory scores, over every positive finite dimension.
--   - `bottleneck`: PDF p.39, (8.51): unrestricted bottleneck, without an upper dimension bound. For valid data and alpha nonnegative the value set is nonempty and bounded above by alpha H(Y). A constant one-dimensional memory is admissible.
--   - `shannon`: PDF p.37: classical entropy in bits, with 0 log 0 = 0.
--   - `efficientScore`: PDF p.37, (8.39): efficient objective with its own environmental family.
--   - `efficientValues`: PDF p.37, (8.40): finite probability ensembles with the prescribed mean.
--   - `efficientSupport`: PDF p.37, (8.40): efficient optimum. Valid data give a nonempty bounded set: one outcome q=p is feasible, and every objective is at most log2 |Y|.
--   - `coherence`: PDF p.36: relative entropy of coherence as an entropy difference.
--   - `schur`: PDF p.33, (8.12): the Schur channel applied entry by entry.
--   - `correlation`: PDF p.32, (8.3): correlation matrix computed from r. Uses require positive diagonal.
--   - `matrixScore`: PDF p.35, (8.28): matrix support objective.
--   - `productDephasing`: PDF pp.41,44: product binary dephasing, preserving the arbitrary reference. Each differing qubit contributes one factor gamma to an operator entry.
--   - `blockDephase`: PDF p.44: complete qubit pinching, preserving reference off-diagonal entries.
--   - `completeCoherence`: PDF p.44, (9.18): complete coherence relative to the qubit blocks.
--   - `perturbation`: PDF p.45, (9.26): complex off-diagonal perturbation of diag(p,1-p).
--   - `qubitDephasing`: PDF p.41, (9.1): one-qubit binary dephasing.
--   - `qubitTheta`: PDF p.42, (9.9): qubit matrix defined without division at q=0,1.
--   - `qubitEntropy`: PDF p.42, (9.11): entropy of the qubit matrix.
--   - `qubitScore`: PDF p.42, (9.12): scalar matrix objective.
--   - `witnessMemory`: PDF pp.43,73: explicit nonorthogonal unit-vector memory witness.
--   - `witnessInstrument`: PDF pp.43,73: a one-outcome basis-copying instrument with discarded memory.
--   - `binaryPinching`: PDF p.78: binary pinching by a Hermitian unitary involution.
--   - `pinchingProduction`: PDF p.78, (E.1): full real interpolation used for the derivative at 1. The density hypothesis is full rank, so the relevant neighborhood is positive definite.
--   - `Config`: PDF p.57: configurations for possibly unequal component dimensions.
--   - `Subconfig`: PDF p.57: subset configurations; the empty subset has one configuration.
--   - `mergeConfig`: PDF p.57: combine complementary subset configurations.
--   - `subsetMemory`: PDF p.57: partial trace outside J, retaining the unrestricted quantum memory.
--   - `subsetEntropy`: PDF p.57: H(A_J|X), with classical X represented by a probability ensemble.
--   - `subsetMemoryEntropy`: PDF p.57: H(FA_J|X).
--   - `subsetPolynomial`: PDF pp.57-58, (B.14)-(B.15): full real Bernoulli-subset polynomial.
--   - `conditionalMemoryEntropy`: PDF p.57: H(F|X).
--   - `singleEntropySum`: PDF p.57: sum_i H(A_i) for unconditional marginals (no conditioning on X).
--   - `extensionEnvironmentInformation`: PDF p.77: I(Z;E|T) for the source extension (D.122).
--   - `extensionLabelInformation`: PDF p.77: I(Z;Y|T) for the same extension.
-- source:
--   Static classical-quantum-entanglement trade-offs: an entropic converse and single-letter characterizations, arXiv:2609.23298v1, https://arxiv.org/abs/2609.23298v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement

/-! Paper-local interfaces for arXiv:2609.23298v1. Unstated nodes are in GAPS.json.
Operational capacity is not defined by its proposed entropic characterization. -/

noncomputable section

open scoped ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Information100.P27

/-- PDF p.6: a finite probability distribution, allowing zero weights. -/
def IsProbability {Y : Type} [Fintype Y] (p : Y → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- PDF pp.6,39: average of a finite family of operators. -/
def average {Y D : Type} [Fintype Y] (p : Y → ℝ)
    (a : Y → Matrix D D ℂ) : Matrix D D ℂ :=
  ∑ i, (p i : ℂ) • a i

/-- PDF p.39: purity of every conditional environmental state. -/
def IsPureFamily {Y E : Type} [Fintype E] (e : Y → Matrix E E ℂ) : Prop :=
  ∀ i, ∃ v : EuclideanSpace ℂ E, IsState v ∧ e i = pureDensity v

/-- PDF p.39, (8.48): marginal on the memory and environment. -/
def memoryEnvironment {Y T E : Type} [Fintype Y] (p : Y → ℝ)
    (e : Y → Matrix E E ℂ) (tau : Y → Matrix T T ℂ) : Matrix (T × E) (T × E) ℂ :=
  average p (fun i => Matrix.kronecker (tau i) (e i))

/-- PDF pp.39,75: I(T;Y) as a Holevo quantity for classical Y. -/
def labelInformation {Y T : Type} [Fintype Y] [Fintype T] (p : Y → ℝ)
    (tau : Y → Matrix T T ℂ) : ℝ :=
  vnEntropy (average p tau) - ∑ i, p i * vnEntropy (tau i)

/-- PDF p.39: alpha I(T;E) - I(T;Y), evaluated on the extension (8.48). -/
def memoryScore {Y T E : Type} [Fintype Y] [Fintype T] [Fintype E]
    (alpha : ℝ) (p : Y → ℝ) (e : Y → Matrix E E ℂ)
    (tau : Y → Matrix T T ℂ) : ℝ :=
  alpha * (vnEntropy (average p tau) + vnEntropy (average p e) -
    vnEntropy (memoryEnvironment p e tau)) - labelInformation p tau

/-- PDF p.39: all unrestricted-memory scores, over every positive finite dimension. -/
def bottleneckValues {Y E : Type} [Fintype Y] [Fintype E]
    (alpha : ℝ) (p : Y → ℝ) (e : Y → Matrix E E ℂ) : Set ℝ :=
  {v | ∃ m : ℕ, 0 < m ∧ ∃ tau : Y → Matrix (Fin m) (Fin m) ℂ,
    (∀ i, IsDensityMatrix (tau i)) ∧ v = memoryScore alpha p e tau}

/-- PDF p.39, (8.51): unrestricted bottleneck, without an upper dimension bound.
For valid data and alpha nonnegative the value set is nonempty and bounded above
by alpha H(Y). A constant one-dimensional memory is admissible. -/
def bottleneck {Y E : Type} [Fintype Y] [Fintype E]
    (alpha : ℝ) (p : Y → ℝ) (e : Y → Matrix E E ℂ) : ℝ :=
  sSup (bottleneckValues alpha p e)

/-- PDF p.37: classical entropy in bits, with 0 log 0 = 0. -/
def shannon {Y : Type} [Fintype Y] (q : Y → ℝ) : ℝ :=
  -∑ i, q i * Real.logb 2 (q i)

/-- PDF p.37, (8.39): efficient objective with its own environmental family. -/
def efficientScore {Y E : Type} [Fintype Y] [Fintype E]
    (mu : ℝ) (e : Y → Matrix E E ℂ) (q : Y → ℝ) : ℝ :=
  shannon q - (1 + mu) * vnEntropy (average q e)

/-- PDF p.37, (8.40): finite probability ensembles with the prescribed mean. -/
def efficientValues {Y E : Type} [Fintype Y] [Fintype E]
    (mu : ℝ) (p : Y → ℝ) (e : Y → Matrix E E ℂ) : Set ℝ :=
  {v | ∃ k : ℕ, ∃ w : Fin k → ℝ, ∃ q : Fin k → Y → ℝ,
    IsProbability w ∧ (∀ x, IsProbability (q x)) ∧
    (∀ i, ∑ x, w x * q x i = p i) ∧ v = ∑ x, w x * efficientScore mu e (q x)}

/-- PDF p.37, (8.40): efficient optimum. Valid data give a nonempty bounded set:
one outcome q=p is feasible, and every objective is at most log2 |Y|. -/
def efficientSupport {Y E : Type} [Fintype Y] [Fintype E]
    (mu : ℝ) (p : Y → ℝ) (e : Y → Matrix E E ℂ) : ℝ :=
  sSup (efficientValues mu p e)

/-- PDF p.36: relative entropy of coherence as an entropy difference. -/
def coherence {D : Type} [Fintype D] (theta : Matrix D D ℂ) : ℝ :=
  vnEntropy (Matrix.diagonal fun i => theta i i) - vnEntropy theta

/-- PDF p.33, (8.12): the Schur channel applied entry by entry. -/
def schur {D : Type} (G theta : Matrix D D ℂ) : Matrix D D ℂ :=
  fun i j => G i j * theta i j

/-- PDF p.32, (8.3): correlation matrix computed from r. Uses require positive diagonal. -/
def correlation {D : Type} (r : Matrix D D ℂ) : Matrix D D ℂ :=
  fun i j => r i j / (Real.sqrt ((r i i).re * (r j j).re) : ℂ)

/-- PDF p.35, (8.28): matrix support objective. -/
def matrixScore {D : Type} [Fintype D] (mu : ℝ) (G theta : Matrix D D ℂ) : ℝ :=
  vnEntropy (Matrix.diagonal fun i => theta i i) + mu * vnEntropy theta - (1 + mu) * vnEntropy (schur G theta)

/-- PDF pp.41,44: product binary dephasing, preserving the arbitrary reference.
Each differing qubit contributes one factor gamma to an operator entry. -/
def productDephasing {R : Type} (n : ℕ) (gamma : ℝ)
    (theta : Matrix (Qubits n × R) (Qubits n × R) ℂ) :
    Matrix (Qubits n × R) (Qubits n × R) ℂ :=
  fun a b => ((gamma ^ ((Finset.univ.filter fun i : Fin n => a.1 i ≠ b.1 i).card) : ℝ) : ℂ) *
    theta a b

/-- PDF p.44: complete qubit pinching, preserving reference off-diagonal entries. -/
def blockDephase {R : Type} (n : ℕ)
    (theta : Matrix (Qubits n × R) (Qubits n × R) ℂ) :
    Matrix (Qubits n × R) (Qubits n × R) ℂ :=
  fun a b => if a.1 = b.1 then theta a b else 0

/-- PDF p.44, (9.18): complete coherence relative to the qubit blocks. -/
def completeCoherence {R : Type} [Fintype R] (n : ℕ)
    (theta : Matrix (Qubits n × R) (Qubits n × R) ℂ) : ℝ :=
  vnEntropy (blockDephase n theta) - vnEntropy theta

/-- PDF p.45, (9.26): complex off-diagonal perturbation of diag(p,1-p). -/
def perturbation (p : ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(p : ℂ), z; conj z, ((1 - p : ℝ) : ℂ)]

/-- PDF p.41, (9.1): one-qubit binary dephasing. -/
def qubitDephasing (gamma : ℝ) (theta : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then theta i j else (gamma : ℂ) * theta i j

/-- PDF p.42, (9.9): qubit matrix defined without division at q=0,1. -/
def qubitTheta (q t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  perturbation q ((t * Real.sqrt (q * (1 - q)) : ℝ) : ℂ)

/-- PDF p.42, (9.11): entropy of the qubit matrix. -/
def qubitEntropy (q t : ℝ) : ℝ :=
  binEntropy2 ((1 + Real.sqrt ((2 * q - 1) ^ 2 + 4 * q * (1 - q) * t ^ 2)) / 2)

/-- PDF p.42, (9.12): scalar matrix objective. -/
def qubitScore (gamma mu q t : ℝ) : ℝ :=
  binEntropy2 q + mu * qubitEntropy q t - (1 + mu) * qubitEntropy q (gamma * t)

/-- PDF pp.43,73: explicit nonorthogonal unit-vector memory witness. -/
def witnessMemory (t : ℝ) (i : Fin 2) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (fun j => if i = 0 then (if j = 0 then 1 else 0)
    else (if j = 0 then (t : ℂ) else (Real.sqrt (1-t^2) : ℂ)))

/-- PDF pp.43,73: a one-outcome basis-copying instrument with discarded memory. -/
def witnessInstrument (t : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ :=
  fun o i => if o.1 = i then witnessMemory t i o.2 else 0

/-- PDF p.78: binary pinching by a Hermitian unitary involution. -/
def binaryPinching {D : Type} [Fintype D] (J theta : Matrix D D ℂ) : Matrix D D ℂ :=
  (2 : ℂ)⁻¹ • (theta + J * theta * J)

/-- PDF p.78, (E.1): full real interpolation used for the derivative at 1.
The density hypothesis is full rank, so the relevant neighborhood is positive definite. -/
def pinchingProduction {D : Type} [Fintype D] (J theta : Matrix D D ℂ) (t : ℝ) : ℝ :=
  let zeta := binaryPinching J theta
  vnEntropy zeta - vnEntropy (zeta + (t : ℂ) • (theta - zeta))

/-- PDF p.57: configurations for possibly unequal component dimensions. -/
abbrev Config {n : ℕ} (d : Fin n → ℕ) := (i : Fin n) → Fin (d i)

/-- PDF p.57: subset configurations; the empty subset has one configuration. -/
abbrev Subconfig {n : ℕ} (d : Fin n → ℕ) (J : Finset (Fin n)) :=
  (i : {i : Fin n // i ∈ J}) → Fin (d i.1)

/-- PDF p.57: combine complementary subset configurations. -/
def mergeConfig {n : ℕ} {d : Fin n → ℕ} (J : Finset (Fin n))
    (a : Subconfig d J) (c : Subconfig d (Finset.univ \ J)) : Config d :=
  fun i => if h : i ∈ J then a ⟨i, h⟩ else c ⟨i, by simp [h]⟩

/-- PDF p.57: partial trace outside J, retaining the unrestricted quantum memory. -/
def subsetMemory {n f : ℕ} {d : Fin n → ℕ}
    (rho : Matrix (Fin f × Config d) (Fin f × Config d) ℂ) (J : Finset (Fin n)) :
    Matrix (Fin f × Subconfig d J) (Fin f × Subconfig d J) ℂ :=
  fun a b => ∑ c : Subconfig d (Finset.univ \ J),
    rho (a.1, mergeConfig J a.2 c) (b.1, mergeConfig J b.2 c)

/-- PDF p.57: H(A_J|X), with classical X represented by a probability ensemble. -/
def subsetEntropy {n f m : ℕ} {d : Fin n → ℕ} (p : Fin m → ℝ)
    (rho : Fin m → Matrix (Fin f × Config d) (Fin f × Config d) ℂ)
    (J : Finset (Fin n)) : ℝ :=
  ∑ x, p x * vnEntropy (traceLeft (subsetMemory (rho x) J))

/-- PDF p.57: H(FA_J|X). -/
def subsetMemoryEntropy {n f m : ℕ} {d : Fin n → ℕ} (p : Fin m → ℝ)
    (rho : Fin m → Matrix (Fin f × Config d) (Fin f × Config d) ℂ)
    (J : Finset (Fin n)) : ℝ :=
  ∑ x, p x * vnEntropy (subsetMemory (rho x) J)

/-- PDF pp.57-58, (B.14)-(B.15): full real Bernoulli-subset polynomial. -/
def subsetPolynomial {n f m : ℕ} {d : Fin n → ℕ} (p : Fin m → ℝ)
    (rho : Fin m → Matrix (Fin f × Config d) (Fin f × Config d) ℂ)
    (keepMemory : Bool) (r : ℝ) : ℝ :=
  ∑ J : Finset (Fin n), r ^ J.card * (1 - r) ^ (n - J.card) *
    (if keepMemory then subsetMemoryEntropy p rho J else subsetEntropy p rho J)

/-- PDF p.57: H(F|X). -/
def conditionalMemoryEntropy {n f m : ℕ} {d : Fin n → ℕ} (p : Fin m → ℝ)
    (rho : Fin m → Matrix (Fin f × Config d) (Fin f × Config d) ℂ) : ℝ :=
  ∑ x, p x * vnEntropy (traceRight (rho x))

/-- PDF p.57: sum_i H(A_i) for unconditional marginals (no conditioning on X). -/
def singleEntropySum {n f m : ℕ} {d : Fin n → ℕ} (p : Fin m → ℝ)
    (rho : Fin m → Matrix (Fin f × Config d) (Fin f × Config d) ℂ) : ℝ :=
  ∑ i : Fin n, vnEntropy (traceLeft (subsetMemory (average p rho) {i}))

/-- PDF p.77: I(Z;E|T) for the source extension (D.122). -/
def extensionEnvironmentInformation {Y T Z E : Type} [Fintype Y] [Fintype T]
    [Fintype Z] [Fintype E] (p : Y → ℝ) (e : Y → Matrix E E ℂ)
    (tau : Y → Matrix (T × Z) (T × Z) ℂ) : ℝ :=
  vnEntropy (average p tau) +
    vnEntropy (memoryEnvironment p e (fun i => traceRight (tau i))) -
    vnEntropy (average p (fun i => traceRight (tau i))) -
    vnEntropy (memoryEnvironment p e tau)

/-- PDF p.77: I(Z;Y|T) for the same extension. -/
def extensionLabelInformation {Y T Z : Type} [Fintype Y] [Fintype T] [Fintype Z]
    (p : Y → ℝ) (tau : Y → Matrix (T × Z) (T × Z) ℂ) : ℝ :=
  labelInformation p tau - labelInformation p (fun i => traceRight (tau i))

/-! Sanity examples for the local definitions. -/

example {D : Type} (theta : Matrix D D ℂ) (i : D) :
    (Matrix.diagonal fun j => theta j j) i i = theta i i := by
  simp

example {D : Type} (G theta : Matrix D D ℂ) (i j : D) :
    schur G theta i j = G i j * theta i j := rfl

example {D : Type} (a : Unit → Matrix D D ℂ) :
    average (fun _ : Unit => (1 : ℝ)) a = a () := by
  simp [average]

example {R : Type} (theta : Matrix (Qubits 1 × R) (Qubits 1 × R) ℂ)
    (a : Qubits 1) (u v : R) : blockDephase 1 theta (a,u) (a,v) = theta (a,u) (a,v) := by
  simp [blockDephase]

example (gamma : ℝ) (theta : Matrix (Fin 2) (Fin 2) ℂ) :
    qubitDephasing gamma theta 0 0 = theta 0 0 := by
  simp [qubitDephasing]

example (p : ℝ) : perturbation p 0 0 1 = 0 := rfl

example (t : ℝ) : witnessInstrument t (0,0) 0 = 1 := by
  simp [witnessInstrument, witnessMemory]

example (q : ℝ) : qubitTheta q 0 = perturbation q 0 := by
  simp [qubitTheta]

example {D : Type} [Fintype D] (J : Matrix D D ℂ) :
    binaryPinching J 0 = 0 := by
  simp [binaryPinching]

example {n : ℕ} {d : Fin n → ℕ} (J : Finset (Fin n)) (a : Subconfig d J)
    (c : Subconfig d (Finset.univ \ J)) (i : Fin n) (h : i ∈ J) :
    mergeConfig J a c i = a ⟨i,h⟩ := by
  simp [mergeConfig, h]

end QAlgorithms.Papers.Independent.Information100.P27


