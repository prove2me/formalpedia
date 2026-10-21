-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P32
-- name    : QAlgorithms_Papers_Independent_Claimed50_P32
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T10:24:16.663597+00:00
-- url     : https://prove2.me/theorems/ed2f3998-1ee8-4d36-a5a0-5d3983a737ed
-- title:
--   Definitions for On approximation of quantum channels
-- statement:
--   The objects the formalized statements of *On approximation of quantum channels* (arXiv:0711.2245) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `TraceOperator`: Full complex trace-class domain in a chosen complete basis, PDF p.2. No positivity or normalization is imposed on this domain.
--   - `TraceSubstate`: Positive trace-at-most-one operators, PDF p.2; inherits trace-norm topology. The frozen P35.Substate is finite-dimensional and excludes zero, so it does not model this paper's T1(H). Positivity itself is imported, not redefined.
--   - `stateOperator`: A normalized state as an element of the full trace-class space, PDF pp.2--3.
--   - `CanonicalOperation`: Quantum operations, PDF p.4. The accepted predicate includes complex linearity on all trace-class inputs, positivity of every finite amplification, and trace nonincrease. The value on non-trace-class arrays is fixed to zero solely to make the representation unique; those arrays are outside the domain. The frozen P14.Operation is only the raw function type; its underlying type is reused here as QAlgorithms.Superop, with the imported operation predicate.
--   - `evaluate`: Evaluate an operation on a state in the genuine trace-class domain, PDF pp.4,6. Nuclearity of the result is a clause of the operation predicate.
--   - `StrongChannel`: Channels carry the subspace strong topology, PDF pp.4,6. The imported predicate is complete positivity and trace preservation on the full trace-class domain, including every finite matrix amplification.
--   - `evaluationImage`: Image of a set of operations under evaluation at a fixed input, PDF p.9. All image points are positive with trace at most one; compactness may equivalently be tested in that subspace or in the full trace-class space.
--   - `IsEnergyOperator`: A positive Hamiltonian with discrete spectrum of finite multiplicity escaping to infinity, PDF p.10, expressed in its complete eigenbasis. Finite dimensional Hamiltonians are included. A zero energy level is allowed.
--   - `spectralMeanEnergy`: Extended mean energy of a positive trace-class input, PDF pp.10,13. Only positive operators are used in energy constraints; infinity is retained. Unlike P01.Hamiltonian.meanEnergy, this accepts subnormalized outputs, including zero, so it cannot use that normalized-state-only interface.
--   - `boundedAmplification`: Energy amplification (12), PDF p.10: the homogeneous inequality at every finite-energy state. This explicitly defines the zero-input-energy boundary, where the printed quotient has no value.
--   - `finiteProjection`: Orthogonal projection onto a finite orthonormal family, PDF pp.7,24. Orthonormality is imposed wherever this formula is used as a projection.
--   - `matrixElement`: Matrix element of a trace-class operator in Hilbert vectors, PDF p.24. On nuclear inputs the row pairings and outer Hilbert pairing converge.
--   - `finiteCompression`: Finite-rank compression P X P, PDF p.7. For an orthonormal family v, P is its orthogonal range projector. The finite expression avoids products of unrestricted infinite arrays.
--   - `projectedMass`: Trace of P X for a finite-rank orthogonal projector, PDF p.24.
--   - `traceTail`: Uniform-tail quantity Tr((I-P)X), PDF p.24. Positivity of X and orthonormality of v are imposed in its compactness application.
--   - `jointMarginalSet`: The marginal-constrained joint set, PDF p.24. The tensor symbol in the paper denotes this set, rather than elementary tensors or their convex hull. Partial traces are over the completed Hilbert factors with bases I and J.
-- source:
--   On approximation of quantum channels, arXiv:0711.2245v1, https://arxiv.org/abs/0711.2245v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08

/-!
Shirokov--Holevo, arXiv:0711.2245v1, topology and compactness statements.
Countable nonempty basis types describe arbitrary nonzero separable complex
Hilbert spaces, including finite dimensions. Nuclear coefficients and their
trace norm are reused from the pinned accepted library. No operator-norm
subspace topology is used. Entropy/roof nodes requiring the missing complete
trace-class Banach/barycenter interface are explicitly deferred in HARD.md.
Compilation is pending the separately authorized batch handoff.
-/

noncomputable section

open Filter
open scoped Topology ENNReal NNReal BigOperators

namespace QAlgorithms.Papers.Independent.Claimed50.P32

namespace Nuclear

export QAlgorithms.Papers.Independent.Dependency50.P33
  (IsTraceClass traceSize State IsTraceClassChannel)

end Nuclear

namespace Operators

export QAlgorithms.Papers.Independent.Frontier18.P08
  (PositiveTraceClass operatorTrace IsQuantumOperation HasFullSupport
    partialTraceFirst partialTraceSecond)

end Operators

open QAlgorithms.RealRegisters (Hilbert)

/-- Full complex trace-class domain in a chosen complete basis, PDF p.2.
No positivity or normalization is imposed on this domain. -/
abbrev TraceOperator (I : Type) :=
  {X : Matrix I I ℂ // Nuclear.IsTraceClass X}

/-- Trace-norm topology, PDF p.2: initial topology of distances to every
trace-class centre. These distances are finite on the specified domain. -/
instance traceOperatorTopology (I : Type) : TopologicalSpace (TraceOperator I) :=
  TopologicalSpace.induced
    (fun X : TraceOperator I => fun Y : TraceOperator I =>
      Nuclear.traceSize (X.val - Y.val)) inferInstance

/-- Positive trace-at-most-one operators, PDF p.2; inherits trace-norm topology.
The frozen P35.Substate is finite-dimensional and excludes zero, so it does not
model this paper's T1(H). Positivity itself is imported, not redefined. -/
abbrev TraceSubstate (I : Type) :=
  {X : TraceOperator I // Operators.PositiveTraceClass X.val ∧
    Operators.operatorTrace X.val ≤ 1}

/-- A normalized state as an element of the full trace-class space, PDF pp.2--3. -/
def stateOperator {I : Type} (rho : Nuclear.State I) : TraceOperator I :=
  ⟨rho.coefficients, rho.density.1⟩

/-- Quantum operations, PDF p.4. The accepted predicate includes complex
linearity on all trace-class inputs, positivity of every finite amplification,
and trace nonincrease. The value on non-trace-class arrays is fixed to zero
solely to make the representation unique; those arrays are outside the domain.
The frozen P14.Operation is only the raw function type; its underlying type is
reused here as QAlgorithms.Superop, with the imported operation predicate. -/
structure CanonicalOperation (I J : Type) where
  act : QAlgorithms.Superop I J
  operation : Operators.IsQuantumOperation act
  outside : ∀ X, ¬ Nuclear.IsTraceClass X → act X = 0

/-- Evaluate an operation on a state in the genuine trace-class domain,
PDF pp.4,6. Nuclearity of the result is a clause of the operation predicate. -/
def evaluate {I J : Type} (Phi : CanonicalOperation I J) (rho : Nuclear.State I) :
    TraceOperator J :=
  ⟨Phi.act rho.coefficients, Phi.operation.1 rho.coefficients rho.density.1⟩

/-- Strong topology of operations, PDF p.6: pointwise trace-norm convergence
on every input state. The topology is specified before asserting metrizability. -/
instance operationTopology (I J : Type) : TopologicalSpace (CanonicalOperation I J) :=
  TopologicalSpace.induced
    (fun Phi : CanonicalOperation I J => fun rho : Nuclear.State I => evaluate Phi rho)
    inferInstance

/-- Channels carry the subspace strong topology, PDF pp.4,6.
The imported predicate is complete positivity and trace preservation on the
full trace-class domain, including every finite matrix amplification. -/
abbrev StrongChannel (I J : Type) :=
  {Phi : CanonicalOperation I J // Nuclear.IsTraceClassChannel Phi.act}

/-- Image of a set of operations under evaluation at a fixed input, PDF p.9.
All image points are positive with trace at most one; compactness may equivalently
be tested in that subspace or in the full trace-class space. -/
def evaluationImage {I J : Type} (F : Set (CanonicalOperation I J))
    (sigma : Nuclear.State I) : Set (TraceOperator J) :=
  (fun Phi => evaluate Phi sigma) '' F

/-- A positive Hamiltonian with discrete spectrum of finite multiplicity
escaping to infinity, PDF p.10, expressed in its complete eigenbasis. Finite
dimensional Hamiltonians are included. A zero energy level is allowed. -/
def IsEnergyOperator {I : Type} (energy : I → ℝ≥0) : Prop :=
  ∀ R : ℝ, {i : I | (energy i : ℝ) ≤ R}.Finite

/-- Extended mean energy of a positive trace-class input, PDF pp.10,13.
Only positive operators are used in energy constraints; infinity is retained.
Unlike P01.Hamiltonian.meanEnergy, this accepts subnormalized outputs, including
zero, so it cannot use that normalized-state-only interface. -/
def spectralMeanEnergy {I : Type} (energy : I → ℝ≥0) (X : TraceOperator I) : ℝ≥0∞ :=
  ∑' i, (energy i : ℝ≥0∞) * ENNReal.ofReal (X.val i i).re

/-- Energy amplification (12), PDF p.10: the homogeneous inequality at every
finite-energy state. This explicitly defines the zero-input-energy boundary,
where the printed quotient has no value. -/
def boundedAmplification {I J : Type} (energyIn : I → ℝ≥0)
    (energyOut : J → ℝ≥0) (k : ℝ) : Set (StrongChannel I J) :=
  {Phi | ∀ rho : Nuclear.State I,
    spectralMeanEnergy energyIn (stateOperator rho) < ⊤ →
    spectralMeanEnergy energyOut (evaluate Phi.val rho) ≤
      ENNReal.ofReal k * spectralMeanEnergy energyIn (stateOperator rho)}

/-- Orthogonal projection onto a finite orthonormal family, PDF pp.7,24.
Orthonormality is imposed wherever this formula is used as a projection. -/
def finiteProjection {I : Type} {n : ℕ} (v : Fin n → Hilbert I)
    (u : Hilbert I) : Hilbert I :=
  ∑ a, (inner ℂ (v a) u) • v a

/-- Matrix element of a trace-class operator in Hilbert vectors, PDF p.24.
On nuclear inputs the row pairings and outer Hilbert pairing converge. -/
def matrixElement {I : Type} (X : TraceOperator I) (u v : Hilbert I) : ℂ :=
  ∑' i, star (u i) * (∑' j, X.val i j * v j)

/-- Finite-rank compression P X P, PDF p.7. For an orthonormal family v,
P is its orthogonal range projector. The finite expression avoids products of
unrestricted infinite arrays. -/
def finiteCompression {I : Type} {n : ℕ} (v : Fin n → Hilbert I)
    (X : TraceOperator I) : Matrix I I ℂ :=
  fun i j => ∑ a, ∑ b,
    v a i * matrixElement X (v a) (v b) * star (v b j)

/-- Trace of P X for a finite-rank orthogonal projector, PDF p.24. -/
def projectedMass {I : Type} {n : ℕ} (X : TraceOperator I)
    (v : Fin n → Hilbert I) : ℝ :=
  (∑ a, matrixElement X (v a) (v a)).re

/-- Uniform-tail quantity Tr((I-P)X), PDF p.24. Positivity of X and
orthonormality of v are imposed in its compactness application. -/
def traceTail {I : Type} {n : ℕ} (X : TraceOperator I)
    (v : Fin n → Hilbert I) : ℝ :=
  Operators.operatorTrace X.val - projectedMass X v

/-- The marginal-constrained joint set, PDF p.24. The tensor symbol in the
paper denotes this set, rather than elementary tensors or their convex hull.
Partial traces are over the completed Hilbert factors with bases I and J. -/
def jointMarginalSet {I J : Type} (A : Set (TraceSubstate I)) (B : Set (TraceSubstate J)) :
    Set (TraceSubstate (I × J)) :=
  {C | (∃ a ∈ A, Operators.partialTraceSecond C.val.val = a.val.val) ∧
    (∃ b ∈ B, Operators.partialTraceFirst C.val.val = b.val.val)}

/-! Sanity examples: boundary conventions for the concrete local definitions. -/

example {I J : Type} (Phi : StrongChannel I J) :
    Nuclear.IsTraceClassChannel Phi.val.act := Phi.property

example {I : Type} (rho : Nuclear.State I) :
    (stateOperator rho).val = rho.coefficients := rfl

example {I J : Type} (Phi : CanonicalOperation I J) (X : Matrix I I ℂ)
    (h : ¬ Nuclear.IsTraceClass X) : Phi.act X = 0 := Phi.outside X h

example {I : Type} (X : TraceOperator I) :
    spectralMeanEnergy (fun _ : I => (0 : ℝ≥0)) X = 0 := by
  simp [spectralMeanEnergy]

example {I : Type} (v : Fin 0 → Hilbert I) (u : Hilbert I) :
    finiteProjection v u = 0 := by
  simp [finiteProjection]

example {I : Type} (v : Fin 0 → Hilbert I) (X : TraceOperator I) :
    finiteCompression v X = 0 := by
  funext i j
  simp [finiteCompression]

example {I : Type} (v : Fin 0 → Hilbert I) (X : TraceOperator I) :
    traceTail X v = Operators.operatorTrace X.val := by
  simp [traceTail, projectedMass]

example {I J : Type} (B : Set (TraceSubstate J)) :
    jointMarginalSet (∅ : Set (TraceSubstate I)) B = ∅ := by
  ext C
  simp [jointMarginalSet]

end QAlgorithms.Papers.Independent.Claimed50.P32


