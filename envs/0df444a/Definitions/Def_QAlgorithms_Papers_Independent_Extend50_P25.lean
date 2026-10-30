-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P25
-- name    : QAlgorithms_Papers_Independent_Extend50_P25
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T20:14:00.555749+00:00
-- url     : https://prove2.me/theorems/07d4fc7e-7eb0-4631-9ede-ed7ddb070870
-- title:
--   Definitions for Asymptotic performance of port-based teleportation
-- statement:
--   The objects the formalized statements of *Asymptotic performance of port-based teleportation* (arXiv:1809.10751) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Ports`: Bob's N labelled d-dimensional ports (1809.10751v2, PDF p.11).
--   - `portBranch`: Effect-conditioned port output, tracing out Alice, the input and all other Bob ports. PDF pp.11,16,51, Eq. (7.3). The effect rather than its square root is legitimate because all of Alice's systems are traced out. The resource is fixed independently of X.
--   - `PBTProtocol`: Physical deterministic PBT data (PDF pp.9,11). Alice's finite space A includes purifications and classical flags; Bob can only retain the announced port.
--   - `PBTProtocol.channel`: The channel actually implemented by a PBT protocol (PDF p.11).
--   - `pbtFidelity`: Squared entanglement fidelity against identity (PDF p.9), reusing the frozen qudit normalized-Choi overlap. The d=0 totalization is excluded by all statements.
--   - `diamondError`: Full stabilized trace norm error against identity, without a factor 1/2 (PDF p.9). Reuse the frozen diamond norm on the linearized map; all physical channels are already linear. d=0 is a harmless totalization excluded from every theorem using this definition.
--   - `pbtOptimalFidelity`: Constructed optimum over BOTH resources and POVMs, including every finite Alice ancilla (PDF p.11). For d,N>0 the attainable set is nonempty and contained in [0,1].
--   - `optimalDiamondError`: Constructed minimum diamond error over the same physical model (PDF p.11). For d,N>0 the attainable set is nonempty and contained in [0,2].
--   - `portProjector`: The physical EPR projector on the input and port i, identity on all other ports. PDF p.17, Lemma 3.6.
--   - `eprResource`: N maximally entangled d-by-d pairs (PDF pp.11–13).
--   - `standardMeasurement`: PGM for the physical EPR ensemble, completed uniformly on its kernel (PDF p.12). The completion is irrelevant on ensemble support.
--   - `standardFidelity`: Fidelity of the constructed standard PGM/EPR protocol (PDF pp.4,12).
--   - `HeraldedProtocol`: Physical probabilistic PBT data: failure plus N success effects, and a success subchannel p_i id for each successful port (PDF p.13).
--   - `HeraldedProtocol.success`: Total heralded success probability (PDF p.13).
--   - `pbtOptimalSuccess`: Optimize the actual heralded physical model, including resource and POVM (PDF p.13).
--   - `eprSuccess`: Optimize the measurement only, with exactly N EPR pairs as resource (PDF p.13).
--   - `BobSymmetric`: Symmetric Werner marginal: diagonal-unitary AND permutation invariance, without a restriction to the totally symmetric subspace (PDF pp.14–15).
--   - `SymmetricPurification`: Unit pure resource with simultaneous port-permutation invariance and conjugate-U on Alice, U on Bob, plus its symmetric Werner marginal (PDF p.15, Proposition 3.3). Replacing U by its conjugate gives the equivalent source convention.
--   - `conjugateChannel`: Simultaneous conjugation of channel input and output (PDF pp.14–16).
--   - `ConvexInvariantCost`: The convex invariant channel costs explicitly allowed after Lemma 3.2 and Proposition 3.4 (PDF pp.14,16); no claim of exact preservation is imposed.
--   - `NoWorse`: Full conclusion of no-worse performance (PDF pp.14–16).
--   - `SchurDiagram`: Bounded row-tuples representing partitions of n into at most d rows (PDF p.9). The bound alpha_i<=n is automatic mathematically and ensures a concrete finite type.
--   - `diagramWeylDimension`: Source Eq.(2.3), PDF p.10: evaluate the frozen Weyl dimension formula on the actual padded rows. The row adapter is zero beyond the d allowed rows.
--   - `spechtDimension`: Specht dimension, hook-length formula rewritten as on PDF p.20, proof of (4.8).
--   - `schurMass`: The actual Schur–Weyl probability mass, Eq. (4.1), PDF p.18.
--   - `fluctuation`: Centered Schur–Weyl fluctuations, Eq. (4.3), PDF p.18.
--   - `normalCoordinates`: Independent standard real Gaussian coordinates (PDF p.9).
--   - `gueMatrix`: Concrete GUE matrix: diagonal variance 1, off-diagonal real/imaginary variance 1/2. PDF p.9.
--   - `gueZero`: Traceless GUE as the trace-centered pushforward, PDF p.9.
--   - `gueSpectrum`: Ordered eigenvalues of the concrete Hermitian traceless GUE matrix (PDF pp.9,18). The frozen spectral API sorts increasingly; Fin.rev restores the source's order.
--   - `expectedLargest`: Expected largest eigenvalue for the precise GUE normalization in the paper.
--   - `dirichletFirst`: First Dirichlet eigenvalue on the ordered simplex, intrinsically Euclidean. PDF pp.6,39,45. Coordinates z in R^(d-1) map to (z,1-sum z); their Gram matrix is I+11^T and inverse is I-11^T/d. Its constant volume factor sqrt(d) cancels in the Rayleigh quotient. Taking C_c^infinity functions gives the H_0^1 infimum. At d=1 the domain is the zero-dimensional point, its boundary is empty, and its lowest eigenvalue is 0.
--   - `profileSimplex`: Closed ordered probability simplex in the coordinates x=(z,1-sum z). PDF pp.39,42: the affine hyperplane carries its induced Euclidean metric.
--   - `sampledProfileWeight`: Unnormalized sampled profile, PDF p.43, Eq.(6.25). Only the restriction of a to the simplex is used; N>0 is required in the theorem.
--   - `sampledProfileMass`: The normalized q(mu)=eta_N a(mu/N)^2/N^(d-1) in Eq.(6.25), PDF p.43. The normalizing sum is constructed, and is eventually positive for source profiles.
--   - `sampledProfileFidelity`: Fidelity F_a of the sampled resource profile with its source measurement, PDF pp.43,56: substitute q=c*p into Eq.(3.6). The inner sum is exactly over partitions obtained by adding one box to alpha; there is no optimization over a.
--   - `profileEnergy`: Intrinsic Dirichlet energy integral of the source's normalized profile, PDF pp.42,45: sqrt(d) is the coordinate volume Jacobian, and I-11^T/d is the inverse metric. Derivatives within the closed simplex express C2 up to its boundary.
--   - `dimensionCoefficient`: Explicit coefficient appearing in the proof of Theorem 1.5, PDF p.47.
--   - `smoothMaxInformation`: Relative smoothing of max-mutual information in bits, specialized to phi+. PDF p.48. A single extended-real infimum flattens the three nested minimizations: subnormalized rho within purified distance eps, normalized sigma_B, and lambda with rho <= 2^lambda rho_A tensor sigma_B. EReal avoids junk real infima for empty or unbounded sets. The overlap condition is exactly P(phi+,rho)<=eps for 0<=eps<1.
--   - `communicatedChannel`: Entanglement-assisted encoding and decoding, with identity on Bob's retained ancilla during encoding (PDF p.50). d0 counts transmitted dimension only.
--   - `IsQC`: A qc-channel has output diagonal in the fixed classical basis (PDF p.50).
--   - `binaryRoot`: Binary root fidelity b(x,y), without a further outer square root (PDF p.52).
--   - `portOperatorNorm`: Euclidean complex operator norm, using Mathlib's bundled map rather than the real Bloch-matrix norm in Information100.P23 (PDF p.18).
--   - `gammaInterval`: Maximum of adjacent exponents from i through j-1 (PDF p.20). Only i<j is used; this range is then nonempty. NNReal encodes nonnegativity.
-- source:
--   Asymptotic performance of port-based teleportation, arXiv:1809.10751v2, https://arxiv.org/abs/1809.10751v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_ChannelDiamondNorm
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Defs_TensorPermutationRepresentations
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P65
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P25

open QAlgorithms MeasureTheory
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
open scoped BigOperators ComplexConjugate Matrix ComplexOrder

/-- Bob's N labelled d-dimensional ports (1809.10751v2, PDF p.11). -/
abbrev Ports (d N : ℕ) := Fin N → Fin d

/-- Effect-conditioned port output, tracing out Alice, the input and all other Bob ports.
PDF pp.11,16,51, Eq. (7.3). The effect rather than its square root is legitimate because
all of Alice's systems are traced out. The resource is fixed independently of X. -/
def portBranch {d N : ℕ} {A : Type*} [Fintype A]
    (rho : Op (A × Ports d N)) (E : Op (Fin d × A)) (i : Fin N) :
    Superop (Fin d) (Fin d) :=
  fun X y z => ∑ a, ∑ b, ∑ u : A, ∑ v : A,
    ∑ s : Ports d N, ∑ t : Ports d N,
      if s i = y ∧ t i = z ∧ (∀ j, j ≠ i → s j = t j) then
        E (b,v) (a,u) * X a b * rho (u,s) (v,t) else 0

/-- Physical deterministic PBT data (PDF pp.9,11). Alice's finite space A includes
purifications and classical flags; Bob can only retain the announced port. -/
structure PBTProtocol (d N : ℕ) (A : Type*) [Fintype A] [DecidableEq A] where
  resource : Op (A × Ports d N)
  resource_state : IsDensityMatrix resource
  measurement : Fin N → Op (Fin d × A)
  measurement_povm : IsPOVM measurement

/-- The channel actually implemented by a PBT protocol (PDF p.11). -/
def PBTProtocol.channel {d N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (P : PBTProtocol d N A) : Superop (Fin d) (Fin d) :=
  fun X => ∑ i, portBranch P.resource (P.measurement i) i X

/-- Squared entanglement fidelity against identity (PDF p.9), reusing the frozen
qudit normalized-Choi overlap. The d=0 totalization is excluded by all statements. -/
def pbtFidelity (d : ℕ) (Phi : Superop (Fin d) (Fin d)) : ℝ :=
  if hd : 0 < d then QAlgorithms.QuditFidelity.entanglementFidelity d hd Phi else 0

/-- Full stabilized trace norm error against identity, without a factor 1/2 (PDF p.9).
Reuse the frozen diamond norm on the linearized map; all physical channels are already
linear. d=0 is a harmless totalization excluded from every theorem using this definition. -/
def diamondError (d : ℕ) (Phi : Superop (Fin d) (Fin d)) : ℝ :=
  if hd : 0 < d then
    QAlgorithms.IntrinsicLearning.diamondNorm d hd
      (QAlgorithms.Papers.Independent.Support50.P22.linearExtension Phi - LinearMap.id)
  else 0

/-- Constructed optimum over BOTH resources and POVMs, including every finite Alice
ancilla (PDF p.11). For d,N>0 the attainable set is nonempty and contained in [0,1]. -/
def pbtOptimalFidelity (d N : ℕ) : ℝ :=
  sSup {v | ∃ m : ℕ, ∃ P : PBTProtocol d N (Fin m), v = pbtFidelity d P.channel}

/-- Constructed minimum diamond error over the same physical model (PDF p.11).
For d,N>0 the attainable set is nonempty and contained in [0,2]. -/
def optimalDiamondError (d N : ℕ) : ℝ :=
  sInf {v | ∃ m : ℕ, ∃ P : PBTProtocol d N (Fin m), v = diamondError d P.channel}

/-- The physical EPR projector on the input and port i, identity on all other ports.
PDF p.17, Lemma 3.6. -/
def portProjector (d N : ℕ) (i : Fin N) : Op (Fin d × Ports d N) :=
  fun x y => if x.1 = x.2 i ∧ y.1 = y.2 i ∧ (∀ j, j ≠ i → x.2 j = y.2 j)
    then (d : ℂ)⁻¹ else 0

/-- N maximally entangled d-by-d pairs (PDF pp.11–13). -/
def eprResource (d N : ℕ) : Op (Ports d N × Ports d N) :=
  fun x y => if x.1 = x.2 ∧ y.1 = y.2 then ((d : ℂ)^N)⁻¹ else 0

/-- PGM for the physical EPR ensemble, completed uniformly on its kernel (PDF p.12).
The completion is irrelevant on ensemble support. -/
def standardMeasurement (d N : ℕ) : Fin N → Op (Fin d × Ports d N) :=
  let S := ∑ i : Fin N, portProjector d N i
  let R := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) S
  fun i => R * portProjector d N i * R + (N : ℂ)⁻¹ • (1 - R * S * R)

/-- Fidelity of the constructed standard PGM/EPR protocol (PDF pp.4,12). -/
def standardFidelity (d N : ℕ) : ℝ :=
  pbtFidelity d (fun X => ∑ i : Fin N,
    portBranch (eprResource d N) (standardMeasurement d N i) i X)

/-- Physical probabilistic PBT data: failure plus N success effects, and a success
subchannel p_i id for each successful port (PDF p.13). -/
structure HeraldedProtocol (d N : ℕ) (A : Type*) [Fintype A] [DecidableEq A] where
  resource : Op (A × Ports d N)
  resource_state : IsDensityMatrix resource
  successEffect : Fin N → Op (Fin d × A)
  failureEffect : Op (Fin d × A)
  success_positive : ∀ i, (successEffect i).PosSemidef
  failure_positive : failureEffect.PosSemidef
  complete : failureEffect + ∑ i, successEffect i = 1
  weight : Fin N → ℝ
  weight_nonnegative : ∀ i, 0 ≤ weight i
  exact_success : ∀ i X, portBranch resource (successEffect i) i X = (weight i : ℂ) • X

/-- Total heralded success probability (PDF p.13). -/
def HeraldedProtocol.success {d N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (P : HeraldedProtocol d N A) : ℝ := ∑ i, P.weight i

/-- Optimize the actual heralded physical model, including resource and POVM (PDF p.13). -/
def pbtOptimalSuccess (d N : ℕ) : ℝ :=
  sSup {p | ∃ m : ℕ, ∃ P : HeraldedProtocol d N (Fin m), p = P.success}

/-- Optimize the measurement only, with exactly N EPR pairs as resource (PDF p.13). -/
def eprSuccess (d N : ℕ) : ℝ :=
  sSup {p | ∃ P : HeraldedProtocol d N (Ports d N),
    P.resource = eprResource d N ∧ p = P.success}

/-- Symmetric Werner marginal: diagonal-unitary AND permutation invariance,
without a restriction to the totally symmetric subspace (PDF pp.14–15). -/
def BobSymmetric {d N : ℕ} (rho : Op (Ports d N)) : Prop :=
  (∀ U : Matrix.unitaryGroup (Fin d) ℂ,
    conjSuperop (QAlgorithms.Papers.Independent.Information100.P63.tensorPower N (U : Op (Fin d))) rho = rho) ∧
  (∀ pi : Equiv.Perm (Fin N), conjSuperop (QAlgorithms.Schur.tensorPermutation d N pi) rho = rho)

/-- Unit pure resource with simultaneous port-permutation invariance and conjugate-U
on Alice, U on Bob, plus its symmetric Werner marginal (PDF p.15, Proposition 3.3).
Replacing U by its conjugate gives the equivalent source convention. -/
def SymmetricPurification {d N : ℕ} (rho : Op (Ports d N × Ports d N)) : Prop :=
  ∃ psi : EuclideanSpace ℂ (Ports d N × Ports d N), ‖psi‖ = 1 ∧
    rho = pureDensity psi ∧ BobSymmetric (traceLeft rho) ∧
    (∀ pi : Equiv.Perm (Fin N),
      (Matrix.kronecker (QAlgorithms.Schur.tensorPermutation d N pi) (QAlgorithms.Schur.tensorPermutation d N pi)).mulVec psi = psi) ∧
    (∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      (Matrix.kronecker (QAlgorithms.Papers.Independent.Information100.P63.tensorPower N (fun i j => conj ((U : Op (Fin d)) i j)))
        (QAlgorithms.Papers.Independent.Information100.P63.tensorPower N (U : Op (Fin d)))).mulVec psi = psi)

/-- Simultaneous conjugation of channel input and output (PDF pp.14–16). -/
def conjugateChannel {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (Phi : Superop (Fin d) (Fin d)) : Superop (Fin d) (Fin d) :=
  fun X => conjSuperop (U : Op (Fin d)) (Phi (conjSuperop ((U : Op (Fin d))ᴴ) X))

/-- The convex invariant channel costs explicitly allowed after Lemma 3.2 and
Proposition 3.4 (PDF pp.14,16); no claim of exact preservation is imposed. -/
def ConvexInvariantCost {d : ℕ} (J : Superop (Fin d) (Fin d) → ℝ) : Prop :=
  (∀ Phi Psi, IsChannel Phi → IsChannel Psi → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    J (fun X => (t : ℂ) • Phi X + ((1-t : ℝ) : ℂ) • Psi X) ≤
      t * J Phi + (1-t) * J Psi) ∧
  (∀ U Phi, IsChannel Phi → J (conjugateChannel U Phi) = J Phi)

/-- Full conclusion of no-worse performance (PDF pp.14–16). -/
def NoWorse {d : ℕ} (new old : Superop (Fin d) (Fin d)) : Prop :=
  pbtFidelity d old ≤ pbtFidelity d new ∧ diamondError d new ≤ diamondError d old ∧
    ∀ J, ConvexInvariantCost J → J new ≤ J old

/-- Bounded row-tuples representing partitions of n into at most d rows (PDF p.9).
The bound alpha_i<=n is automatic mathematically and ensures a concrete finite type. -/
def SchurDiagram (d n : ℕ) :=
  {a : Fin d → Fin (n+1) // (∑ i, (a i).val) = n ∧
    ∀ i j, i ≤ j → (a j).val ≤ (a i).val}

/-- Finite padded Young diagrams, with a decidable constraint predicate (PDF p.9). -/
instance schurDiagramFintype (d n : ℕ) : Fintype (SchurDiagram d n) := by
  classical
  unfold SchurDiagram
  infer_instance

/-- Source Eq.(2.3), PDF p.10: evaluate the frozen Weyl dimension formula
on the actual padded rows. The row adapter is zero beyond the d allowed rows. -/
def diagramWeylDimension {d n : ℕ} (a : SchurDiagram d n) : ℝ :=
  QAlgorithms.Papers.Independent.Information100.P65.weylDimension
    (fun i => if h : i < d then (a.val ⟨i,h⟩).val else 0) d

/-- Specht dimension, hook-length formula rewritten as on PDF p.20, proof of (4.8). -/
def spechtDimension {d n : ℕ} (a : SchurDiagram d n) : ℝ :=
  (n.factorial : ℝ) * diagramWeylDimension a *
    (∏ i : Fin d, ((d - 1 - i.val).factorial : ℝ)) /
    (∏ i : Fin d, (((a.val i).val + d - 1 - i.val).factorial : ℝ))

/-- The actual Schur–Weyl probability mass, Eq. (4.1), PDF p.18. -/
def schurMass {d n : ℕ} (a : SchurDiagram d n) : ℝ :=
  spechtDimension a * diagramWeylDimension a / (d : ℝ)^n

/-- Centered Schur–Weyl fluctuations, Eq. (4.3), PDF p.18. -/
def fluctuation {d n : ℕ} (a : SchurDiagram d n) (i : Fin d) : ℝ :=
  (((a.val i).val : ℝ) - (n : ℝ)/d) / Real.sqrt ((n : ℝ)/d)

/-- Independent standard real Gaussian coordinates (PDF p.9). -/
def normalCoordinates (I : Type*) [Fintype I] : Measure (I → ℝ) :=
  Measure.pi (fun _ : I => ProbabilityTheory.gaussianReal 0 1)

/-- Concrete GUE matrix: diagonal variance 1, off-diagonal real/imaginary variance 1/2.
PDF p.9. -/
def gueMatrix (d : ℕ) (x : (Fin d × Fin d) → ℝ) : Op (Fin d) :=
  fun i j => if i = j then (x (i,i) : ℂ)
    else if i < j then ((x (i,j) : ℂ) + Complex.I * (x (j,i) : ℂ)) / (Real.sqrt 2 : ℂ)
    else ((x (j,i) : ℂ) - Complex.I * (x (i,j) : ℂ)) / (Real.sqrt 2 : ℂ)

/-- Traceless GUE as the trace-centered pushforward, PDF p.9. -/
def gueZero (d : ℕ) (x : (Fin d × Fin d) → ℝ) : Op (Fin d) :=
  gueMatrix d x - ((gueMatrix d x).trace / (d : ℂ)) • (1 : Op (Fin d))

/-- Ordered eigenvalues of the concrete Hermitian traceless GUE matrix (PDF pp.9,18).
The frozen spectral API sorts increasingly; Fin.rev restores the source's order. -/
def gueSpectrum (d : ℕ) (x : (Fin d × Fin d) → ℝ) (j : Fin d) : ℝ :=
  ascEigenvalues (gueZero d x) (Fin.cast (Fintype.card_fin d).symm (Fin.rev j))

/-- Expected largest eigenvalue for the precise GUE normalization in the paper. -/
def expectedLargest (d : ℕ) (hd : 0 < d) : ℝ :=
  ∫ x, gueSpectrum d x ⟨0,hd⟩ ∂normalCoordinates (Fin d × Fin d)

/-- First Dirichlet eigenvalue on the ordered simplex, intrinsically Euclidean.
PDF pp.6,39,45. Coordinates z in R^(d-1) map to (z,1-sum z); their Gram matrix
is I+11^T and inverse is I-11^T/d. Its constant volume factor sqrt(d) cancels in
the Rayleigh quotient. Taking C_c^infinity functions gives the H_0^1 infimum. At d=1 the
domain is the zero-dimensional point, its boundary is empty, and its lowest eigenvalue is 0. -/
def dirichletFirst (d : ℕ) : ℝ :=
  let point := fun z : EuclideanSpace ℝ (Fin (d-1)) => fun i : Fin d =>
    if h : i.val < d-1 then z ⟨i.val,h⟩ else 1 - ∑ j, z j
  let domain : Set (EuclideanSpace ℝ (Fin (d-1))) :=
    {z | (∀ i, 0 < point z i) ∧ ∀ i j, i < j → point z j < point z i}
  let energy := fun (f : EuclideanSpace ℝ (Fin (d-1)) → ℝ) z =>
    ‖fderiv ℝ f z‖^2 -
      (∑ i : Fin (d-1), (fderiv ℝ f z)
        (WithLp.toLp 2 (fun j => if j = i then (1 : ℝ) else 0)))^2 / (d : ℝ)
  sInf {v : ℝ | ∃ f : EuclideanSpace ℝ (Fin (d-1)) → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ domain ∧
    Integrable (fun z => f z ^ 2) ∧ Integrable (energy f) ∧
    (∫ z, f z ^ 2) = 1 ∧ v = ∫ z, energy f z}

/-- Closed ordered probability simplex in the coordinates x=(z,1-sum z).
PDF pp.39,42: the affine hyperplane carries its induced Euclidean metric. -/
def profileSimplex (d : ℕ) : Set (EuclideanSpace ℝ (Fin (d-1))) :=
  let point := fun z : EuclideanSpace ℝ (Fin (d-1)) => fun i : Fin d =>
    if h : i.val < d-1 then z ⟨i.val,h⟩ else 1 - ∑ j, z j
  {z | (∀ i, 0 ≤ point z i) ∧ ∀ i j, i < j → point z j ≤ point z i}

/-- Unnormalized sampled profile, PDF p.43, Eq.(6.25). Only the restriction of a
to the simplex is used; N>0 is required in the theorem. -/
def sampledProfileWeight (d N : ℕ) (a : EuclideanSpace ℝ (Fin (d-1)) → ℝ)
    (mu : SchurDiagram d N) : ℝ :=
  a (WithLp.toLp 2 (fun i : Fin (d-1) =>
    (((mu.val ⟨i.val, by omega⟩).val : ℝ) / (N : ℝ)))) ^ 2

/-- The normalized q(mu)=eta_N a(mu/N)^2/N^(d-1) in Eq.(6.25), PDF p.43.
The normalizing sum is constructed, and is eventually positive for source profiles. -/
def sampledProfileMass (d N : ℕ) (a : EuclideanSpace ℝ (Fin (d-1)) → ℝ)
    (mu : SchurDiagram d N) : ℝ :=
  sampledProfileWeight d N a mu / ∑ nu : SchurDiagram d N, sampledProfileWeight d N a nu

/-- Fidelity F_a of the sampled resource profile with its source measurement,
PDF pp.43,56: substitute q=c*p into Eq.(3.6). The inner sum is exactly over
partitions obtained by adding one box to alpha; there is no optimization over a. -/
def sampledProfileFidelity (d N : ℕ) (a : EuclideanSpace ℝ (Fin (d-1)) → ℝ) : ℝ :=
  (∑ alpha : SchurDiagram d (N-1),
    (∑ mu : SchurDiagram d N,
      if ∃ j : Fin d, ∀ i : Fin d,
        (mu.val i).val = (alpha.val i).val + (if i = j then 1 else 0)
      then Real.sqrt (sampledProfileMass d N a mu) else 0)^2) / (d : ℝ)^2

/-- Intrinsic Dirichlet energy integral of the source's normalized profile,
PDF pp.42,45: sqrt(d) is the coordinate volume Jacobian, and I-11^T/d is the
inverse metric. Derivatives within the closed simplex express C2 up to its boundary. -/
def profileEnergy (d : ℕ) (a : EuclideanSpace ℝ (Fin (d-1)) → ℝ) : ℝ :=
  Real.sqrt (d : ℝ) * ∫ z in profileSimplex d,
    (‖fderivWithin ℝ a (profileSimplex d) z‖^2 -
      (∑ i : Fin (d-1), (fderivWithin ℝ a (profileSimplex d) z)
        (WithLp.toLp 2 (fun j => if j = i then (1 : ℝ) else 0)))^2 / (d : ℝ))

example (d N : ℕ) (mu : SchurDiagram d N) :
    sampledProfileMass d N (fun _ => 0) mu = 0 := by
  simp [sampledProfileMass, sampledProfileWeight]

/-- Explicit coefficient appearing in the proof of Theorem 1.5, PDF p.47. -/
def dimensionCoefficient (d : ℕ) : ℝ :=
  ((d : ℝ)-1)/2 * (Real.sqrt (((d : ℝ)+1)/2) + 1)^2 * (d : ℝ) *
    ((d : ℝ)*((d : ℝ)-1)/Real.sqrt 2 + Real.sqrt ((d : ℝ)*((d : ℝ)-1)) + Real.sqrt 2)

/-- Relative smoothing of max-mutual information in bits, specialized to phi+.
PDF p.48. A single extended-real infimum flattens the three nested minimizations:
subnormalized rho within purified distance eps, normalized sigma_B, and lambda with
rho <= 2^lambda rho_A tensor sigma_B. EReal avoids junk real infima for empty or
unbounded sets. The overlap condition is exactly P(phi+,rho)<=eps for 0<=eps<1. -/
def smoothMaxInformation (d : ℕ) (eps : ℝ) : EReal :=
  sInf {v : EReal | ∃ rho : Op (Fin d × Fin d), rho.PosSemidef ∧ rho.trace.re ≤ 1 ∧
    1 - eps^2 ≤ (∑ i : Fin d, ∑ j : Fin d, rho (i,i) (j,j)).re / (d : ℝ) ∧
    ∃ sigma : Op (Fin d), IsDensityMatrix sigma ∧ ∃ t : ℝ,
    (((Real.rpow 2 t : ℝ) : ℂ) •
      Matrix.kronecker (fun i j => ∑ k : Fin d, rho (i,k) (j,k)) sigma - rho).PosSemidef ∧
    v = (t : EReal)}

/-- Entanglement-assisted encoding and decoding, with identity on Bob's retained
ancilla during encoding (PDF p.50). d0 counts transmitted dimension only. -/
def communicatedChannel {d d0 a b : ℕ} (rho : Op (Fin a × Fin b))
    (E : Superop (Fin d × Fin a) (Fin d0))
    (D : Superop (Fin d0 × Fin b) (Fin d)) : Superop (Fin d) (Fin d) :=
  fun X => D (fun y z =>
    E (fun u v => X u.1 v.1 * rho (u.2,y.2) (v.2,z.2)) y.1 z.1)

/-- A qc-channel has output diagonal in the fixed classical basis (PDF p.50). -/
def IsQC {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]
    (E : Superop A B) : Prop :=
  IsChannel E ∧ ∀ X i j, i ≠ j → E X i j = 0

/-- Binary root fidelity b(x,y), without a further outer square root (PDF p.52). -/
def binaryRoot (x y : ℝ) : ℝ :=
  Real.sqrt (x*y) + Real.sqrt ((1-x)*(1-y))

/-- Euclidean complex operator norm, using Mathlib's bundled map rather than
the real Bloch-matrix norm in Information100.P23 (PDF p.18). -/
def portOperatorNorm {A : Type*} [Fintype A] (T : Op A) : ℝ := by
  classical
  exact ‖Matrix.toEuclideanCLM (𝕜 := ℂ) T‖

/- Sanity checks for the constructed objects. No theorem proof is part of this draft. -/

example {A B : Type*} (X : Op A) (Y : Op B) (a c : A) (b e : B) :
    Matrix.kronecker X Y (a,b) (c,e) = X a c * Y b e := rfl

example {d N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (P : PBTProtocol d N A) (X : Op (Fin d)) :
    P.channel X = ∑ i, portBranch P.resource (P.measurement i) i X := rfl

example {d N : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (P : HeraldedProtocol d N A) : P.success = ∑ i, P.weight i := rfl

example {d : ℕ} (U : Op (Fin d)) : QAlgorithms.Papers.Independent.Information100.P63.tensorPower 0 U = 1 := by
  ext x y
  simp [QAlgorithms.Papers.Independent.Information100.P63.tensorPower,
    Matrix.one_apply, Subsingleton.elim x y]

example (x : (Fin 1 × Fin 1) → ℝ) : gueZero 1 x = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [gueZero, gueMatrix, Matrix.trace, Matrix.one_apply]

example : binaryRoot 0 0 = 1 := by norm_num [binaryRoot]

example (Phi : Superop (Fin 0) (Fin 0)) : pbtFidelity 0 Phi = 0 := by
  simp [pbtFidelity]

example : dimensionCoefficient 1 = 0 := by
  norm_num [dimensionCoefficient]

/-- Maximum of adjacent exponents from i through j-1 (PDF p.20).
Only i<j is used; this range is then nonempty. NNReal encodes nonnegativity. -/
def gammaInterval (d : ℕ) (gamma : Fin (d-1) → NNReal) (i j : Fin d) : ℝ :=
  ((Finset.univ.filter (fun k : Fin (d-1) => i.val ≤ k.val ∧ k.val < j.val)).sup gamma : NNReal)

end QAlgorithms.Papers.Independent.Extend50.P25


