-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12
-- name    : QAlgorithms_Papers_Independent_Dependency50_P12
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T13:40:32.255122+00:00
-- url     : https://prove2.me/theorems/a4318067-4879-4199-936d-0e53a6583bb6
-- title:
--   Definitions for The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones
-- statement:
--   The objects the formalized statements of *The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones* (arXiv:2608.27330) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsCone`: Definition 2.7, PDF pp.8--9: a nonempty convex cone, including its vertex.
--   - `edge`: Definition 2.7, PDF p.8: E(C)=C intersect -C.
--   - `adMap`: Section 2.1, PDF p.5: the adjoint endomorphism of the real Lie algebra.
--   - `expAd`: Definition 2.8, PDF p.9: exp(ad x), evaluated through its exponential series. Finite dimension and the usual Hausdorff vector-space topology ensure convergence; no independent normed additive or module structure is introduced.
--   - `IsLieWedge`: Definition 2.8, PDF p.9: closed Lie wedge with invariance only under its edge.
--   - `LeviSplitting`: Section 2.1.1 and Section 4.1, PDF pp.6,20: a selected Levi complement and the solvable radical, with their genuine complementary-subspace condition.
--   - `coords`: Section 4.1, PDF p.20: the coordinate isomorphism (S,R) maps to S+R.
--   - `piS`: Definition 4.1, PDF p.20: the Levi projection, determined by the splitting.
--   - `piR`: Section 2.1.1, PDF p.6: linear radical coordinate; it need not be physical.
--   - `radicalSlice`: Definition 4.1, PDF p.20: radical slice as a subset of the radical itself.
--   - `quotientCone`: Definition 4.1, PDF p.20: image cone; no closedness is built into this definition.
--   - `projectedEdge`: Lemma 4.3, PDF p.21: the projected edge, distinguished from the base lineality.
--   - `fiber`: Definition 4.1, PDF p.20: actual fiber at a base point, also defined off the base.
--   - `fiberGraph`: Proposition 4.8, PDF p.25: graph in the FULL product, not in C times r.
--   - `reconstructLeviFibers`: Equation (39), PDF p.25: reconstruction from the supplied fibers.
--   - `candidateEdge`: Equation (38), PDF p.25: candidate edge computed before D5 or D6 is assumed.
--   - `slice`: Equation (33), PDF p.24: a translated fiber, as a subset of g.
--   - `AdmissibleLeviFibers`: Proposition 4.8, PDF pp.24--25: exactly D1--D6; no given wedge or edge is input. Fibers outside C have no significance and are never compared there.
--   - `FiberProperties`: Lemma 4.6, PDF p.23: all five fiber properties, including strict-positive equality.
--   - `QuotientProperties`: Lemma 4.3, PDF p.21: projected edge is a closed Lie subalgebra and acts on C.
--   - `FCC`: Proposition 4.7, PDF p.24: FCC, together with membership of its target base.
--   - `ReconstructionResult`: Proposition 4.8, PDF p.25: every reconstruction conclusion and uniqueness.
--   - `contingent`: Definition 2.9, PDF p.9: Bouligand tangent cone with positive scalars. This avoids Mathlib's bilateral scalar tangent cone.
--   - `fiberDerivative`: Equation (48), PDF p.29: derivative through the tangent of the entire graph.
--   - `action`: Equation (3), PDF p.6: the actual action of s on its radical ideal.
--   - `Super`: Sections 2.2 and 2.4, PDF pp.7,10: full superoperator matrix in matrix units. The accepted P26 convention makes multiplication composition and Choi output-first.
--   - `superOfAction`: Coordinate wrapper for a specified action on operators; no matrix is assumed.
--   - `dissipatorMap`: Section 2.4, PDF p.10: actual rank-one dissipator in matrix-unit coordinates.
--   - `coherentMap`: Section 2.4, PDF p.10: actual Hamiltonian action with its minus-i sign.
--   - `Hamiltonian`: Lemma 2.13, PDF p.11: Hamiltonian generators with the scalar gauge fixed.
--   - `LK`: Section 2.2, PDF p.7: ambient Hermiticity-preserving trace-annihilating action.
--   - `UnitalDissipator`: Remark 2.18, PDF p.13: a physical unital dissipator has zero Hamiltonian part.
--   - `sigma`: Section 2.4 and Example 4.15, PDF pp.10,28: standard Pauli operators, with false and true corresponding to the computational indices 0 and 1.
--   - `pauliBasis`: Example 4.15, PDF p.28: Hilbert--Schmidt orthonormal Pauli basis.
--   - `sigmaMinus`: Remark 2.18, PDF p.13, and Section 5, PDF p.33: sigma-minus=|1><0|.
--   - `blochQ`: Sections 2.2 and 4.4, PDF pp.8,27--28: Bloch linear coefficient of a generator.
--   - `blochB`: Sections 2.2 and 4.4, PDF pp.8,27--28: inhomogeneous Bloch coefficient.
--   - `blochLift`: Example 4.15, PDF p.28: the actual affine-generator action, including translation.
--   - `pauliKossakowskiMatrix`: Canonical normalized Pauli Kossakowski matrix, PDF pp.13,28. The imaginary antisymmetric part uses the actual Bloch translation.
--   - `fullQubitBase`: Example 4.15, PDF pp.27--28: full-cone base in the affine Levi splitting.
--   - `fullQubitFiber`: Example 4.15, PDF pp.27--28: full fiber with radical coordinates (lambda,b).
--   - `radialBase`: Example 4.15, PDF p.28: anisotropic traceless base point S_t.
--   - `gaussianA`: Section 6.3, PDF pp.38--39: finite first-moment drift matrix only.
--   - `gaussianD`: Section 6.3, PDF p.38: diffusion matrix in the [Q,P]=i convention.
--   - `ccrOmega`: Section 6.3, PDF p.38: CCR symplectic matrix for the Q,P ordering.
--   - `gaussianCP`: Section 6.3, PDF pp.38--39: infinitesimal moment-level CP matrix.
--   - `Hurwitz`: Section 2.5, PDF p.13: Hurwitz means strictly negative real parts of all eigenvalues.
--   - `projectionExample`: Remark 4.5, PDF p.22: the concrete three-dimensional closed cone.
--   - `yzProjection`: Remark 4.5, PDF p.22: projection retaining y and z.
--   - `PolyhedralCone`: Remark 4.5, PDF p.22: polyhedral cone, expressed by finitely many closed homogeneous half-spaces; coefficients are actual real linear functionals.
--   - `closedConicalHull`: Section 3.1, PDF pp.15--17: closed conical hull formed by intersection. The ambient full space belongs to the defining family, including for empty input.
--   - `minimalWedge`: Definition 3.2, PDF p.15: minimal LOCAL wedge, not the global tangent wedge.
--   - `edgeOrbit`: Proposition 3.5, PDF pp.16--17: the finite-product group orbit of the edge. Since the edge is symmetric, inverses are included through exp(ad(-X)).
--   - `orbitStep`: Proposition 3.5, PDF pp.16--17: one whole orbit-and-closed-hull step.
--   - `wedgeStage`: Proposition 3.5, PDF pp.16--17: actual recursive iteration from the input cone.
--   - `reachability`: Definition 3.4, PDF p.16: closure of finite positive-time products in the ambient superoperator space, not closure inside an immersed subgroup.
--   - `globalTangentWedge`: Definition 3.4, PDF p.16: tangent wedge of the closed semigroup, equivalently those X whose positive-time exponential belongs to it for every nonnegative time.
--   - `affineAlgebra`: Section 6.1, PDF p.37: homogeneous-coordinate model of aff(R^n). Only the last row is constrained; translations occupy the last column.
--   - `gellMann`: Example 1.1 and Appendix A.4, PDF pp.3,44: standard raw Gell--Mann basis.
--   - `gellMannBasis`: Appendix A.4, PDF p.44: default orthonormal Gell--Mann coordinates.
--   - `qutritJump1`: Example 1.1, PDF p.3: first actual rank-one jump.
--   - `qutritJump2`: Example 1.1, PDF p.3: second actual rank-one jump.
--   - `conditionalProjection`: Appendix A.4, PDF p.44: orthogonal compression away from the UNNORMALIZED maximally entangled vector sum_i |ii>. The factor 1/d is indispensable.
--   - `compressedGeneratorChoi`: Example 1.1, PDF p.3: conditional Choi matrix in the accepted output-first unnormalized convention, retained as a full d^2 by d^2 matrix including its kernel.
--   - `cascadeG`: Section 4.6.1, PDF p.31: independently actuable cascaded qutrit rays.
--   - `cascadeDrift`: Section 4.6.1, PDF p.31: selected simultaneous generator, distinct from the multi-ray control specification.
--   - `pauliDepolarizingGenerator`: Section 4.6.2, PDF p.32: unit-rate pauliDepolarizingGenerator noise, independently switchable.
--   - `qubitControl`: Section 4.6.2, PDF p.32: the three Hamiltonian control directions.
--   - `depolarizingG`: Section 4.6.2, PDF p.32: signed Hamiltonian rays and one positive noise ray.
--   - `depolarizingFiber`: Section 4.6.2, PDF p.32: fiber using the central pauliDepolarizingGenerator coordinate.
--   - `tensor2`: Section 5, PDF p.33: ordered tensor product A on the first qubit, B on the second.
--   - `twoQubitH`: Section 5, PDF p.33: Hamiltonians sigma_A,i tensor I_B divided by two.
--   - `modulatedJ0`: Section 5, PDF p.33: actual projector-modulated jump J0.
--   - `modulatedJ1`: Section 5, PDF p.33: actual projector-modulated jump J1.
--   - `crossSuper`: Equation (53), PDF p.33: bilinear cross-superoperator, with half anticommutator.
--   - `nilradical`: Section 2.1, PDF p.6: maximal nilpotent ideal, formed in the complete lattice of ideals; the supremum here is lattice-theoretic, not a real sSup.
--   - `affineRadical`: Corollary 2.6, PDF p.8: scalar linear part plus arbitrary translations. This is the semidirect radical, not a central direct sum.
--   - `affineTranslations`: Corollary 2.6 and Section 6.1, PDF pp.8,37: pure translations.
--   - `affineIdentity`: Section 6.1, PDF p.37: identity on the linear coordinates, zero homogeneous row.
--   - `momentMap`: Section 6.3, PDF pp.38--39: faithful finite Gaussian moment representation on (q,p,Vqq,Vqp,Vpp,1). Covariance evolves by A V+V A^T+D.
--   - `squeezeMoment`: Section 6.3, PDF p.39: one-sided squeezing ray.
--   - `dampingMoment`: Section 6.3, PDF p.39: one-sided amplitude damping moment pair.
--   - `gaussianG`: Section 6.3, PDF p.39: two independently actuable one-sided moment rays.
--   - `squeezeMatrices`: Section 6.3, PDF p.39: the specified two quadratic Hamiltonian drift matrices.
--   - `gaussianExtensionG`: Section 6.3, PDF p.39: signed quadratic controls and nonzero one-sided damping.
--   - `pointedHamiltonianCone`: Remark 4.14, PDF p.27: fixed pointed Lie-generating Hamiltonian cone in su(2).
--   - `constantCounterexample`: Remark 4.14(1), PDF p.27: actual first counterexample cone.
--   - `varyingCounterexample`: Remark 4.14(2), PDF p.27: conical hull of FOUR generators, not a union of cones.
--   - `centralFiber`: Remark 4.14, PDF p.27: central-coordinate fiber in su(2) direct-sum R L_D.
--   - `depolarizingProjection`: Remark 4.14, PDF p.27: Levi projection in the concrete reductive model. Tr(Q_D)=-12, so this subtracts precisely the central coordinate.
--   - `euclideanJ`: Section 6.4, PDF pp.39--40: rotation generator, in homogeneous Euclidean coordinates.
--   - `euclideanPx`: Section 6.4, PDF pp.39--40: x translation.
--   - `euclideanPy`: Section 6.4, PDF pp.39--40: y translation.
--   - `euclideanAlgebra`: Section 6.4, PDF pp.39--40: actual e(2), whose TRUE Levi factor is zero.
--   - `quadrant`: Equation (62), PDF p.40: the positive quadrant in the translation ideal.
--   - `euclideanCandidate`: Section 6.4, PDF p.40: the assembled candidate with reversible rotations.
--   - `rotatePlane`: Section 6.4, PDF p.40: ordinary rotation action on the translation plane.
--   - `translationSlice`: Section 6.4, PDF p.40: translation slice of any candidate, without mislabelling so(2) as a semisimple Levi factor.
--   - `absoluteEpigraph`: Section 6.4, PDF pp.39--40: varying fibers over a subspace in the abelian example.
--   - `dephasingG`: Remark 6.4, PDF p.40: bidirectional x control and independently switchable z noise.
--   - `dephasingCandidate`: Remark 6.4, PDF p.40: the declared one-noise-ray candidate.
--   - `dephasingOrbitCone`: Equation (64), PDF p.40: full conic orbit closure, allowing all yz jump directions.
--   - `fixedDephasingOrbit`: Remark 6.4, PDF p.40: unit-total-rate orbit in the yz plane.
--   - `yzNoise`: Remark 6.4, PDF p.40: a REAL yz Kossakowski block in raw Pauli coordinates. The factor two converts it to the accepted orthonormal Pauli basis.
--   - `dephasingRadicalSlice`: Remark 6.4, PDF p.40: radical slice of the actual generated local wedge, expressed in ambient coordinates without choosing a Levi complement.
--   - `twoQubitG`: Section 5, PDF p.33: signed primary controls and two INDEPENDENT unit noise rays.
--   - `twoQubitControl`: Section 5, PDF p.33: the actual primary control algebra.
--   - `twoQubitWords`: Equation (54), PDF p.34: the exact ordered recursive words; zero-based Lean indices. The certificate representative E=2 D1 is used only here.
--   - `adjointRotations`: Equation (56), PDF p.34: the three standard adjoint rotation matrices.
--   - `modulatedOrbit`: Section 5.2, PDF pp.35--36: one independently rotatable dissipative orbit. The determinant-one restriction is SU(2), not a common linked rotation of both rays.
--   - `controlConjugation`: Equation (61), PDF p.36: actual control conjugation of a superoperator.
--   - `controlAverage`: Equation (61), PDF p.36: Bochner average with a specified normalized Haar measure. Integrability is asserted in the theorem, never replaced by the integral's junk value.
--   - `SimultaneouslyTriangularizable`: Section 3.2, PDF p.18: simultaneous upper triangularization of a complex matrix representation. Real Lie representations into complex matrices are exactly the restrictions of the complexified representations used by the source.
--   - `AdjointCompletelyReducible`: Section 3.2, PDF p.18: complete reducibility of the actual adjoint module.
--   - `ActionCoupled`: Section 3.2, PDF p.18: action coupling requires the actual nonzero action and nontrivial components in BOTH factors.
-- source:
--   The Geometry of Dissipative Complexity: A Levi-Type Decomposition Theorem for Markovian Quantum Dynamics via Lie Wedges and Invariant Cones, arXiv:2608.27330v1, https://arxiv.org/abs/2608.27330v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P59
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

/-! Statement draft for arXiv:2608.27330v1. The accepted P59 module is
imported only for its audited definitions, not as an unreviewed chunk.
All new interfaces below belong to this paper. Compilation is pending. -/

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius
open Set

namespace QAlgorithms.Papers.Independent.Dependency50.P12

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] Classical.propDecidable Classical.decEq

namespace Coordinates

section Cones

variable {A : Type*} [AddCommGroup A] [Module ℝ A]

/-- Definition 2.7, PDF pp.8--9: a nonempty convex cone, including its vertex. -/
def IsCone (C : Set A) : Prop :=
  0 ∈ C ∧ Convex ℝ C ∧ ∀ a : ℝ, 0 ≤ a → ∀ x ∈ C, a • x ∈ C

/-- Definition 2.7, PDF p.8: E(C)=C intersect -C. -/
def edge (C : Set A) : Set A := {x | x ∈ C ∧ -x ∈ C}

end Cones

variable {A : Type*} [LieRing A] [LieAlgebra ℝ A]
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
  [T2Space A] [FiniteDimensional ℝ A]

/-- Section 2.1, PDF p.5: the adjoint endomorphism of the real Lie algebra. -/
def adMap (x : A) : Module.End ℝ A := LieAlgebra.ad ℝ A x

/-- Definition 2.8, PDF p.9: exp(ad x), evaluated through its exponential
series. Finite dimension and the usual Hausdorff vector-space topology ensure
convergence; no independent normed additive or module structure is introduced. -/
def expAd (x y : A) : A :=
  ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • ((adMap x) ^ n) y

/-- Definition 2.8, PDF p.9: closed Lie wedge with invariance only under its edge. -/
def IsLieWedge (W : Set A) : Prop :=
  IsClosed W ∧ IsCone W ∧ ∀ x ∈ edge W, expAd x '' W ⊆ W

/-- Section 2.1.1 and Section 4.1, PDF pp.6,20: a selected Levi complement
and the solvable radical, with their genuine complementary-subspace condition. -/
structure LeviSplitting (A : Type*) [LieRing A] [LieAlgebra ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    [T2Space A] [FiniteDimensional ℝ A] where
  s : LieSubalgebra ℝ A
  r : LieIdeal ℝ A
  radical_eq : r = LieAlgebra.radical ℝ A
  semisimple : LieAlgebra.radical ℝ s = ⊥
  complementary : IsCompl s.toSubmodule r.toSubmodule

/-- Section 4.1, PDF p.20: the coordinate isomorphism (S,R) maps to S+R. -/
def coords (D : LeviSplitting A) : (D.s × D.r) ≃ₗ[ℝ] A :=
  Submodule.prodEquivOfIsCompl D.s.toSubmodule D.r.toSubmodule D.complementary

/-- Definition 4.1, PDF p.20: the Levi projection, determined by the splitting. -/
def piS (D : LeviSplitting A) (x : A) : D.s := ((coords D).symm x).1

/-- Section 2.1.1, PDF p.6: linear radical coordinate; it need not be physical. -/
def piR (D : LeviSplitting A) (x : A) : D.r := ((coords D).symm x).2

/-- Definition 4.1, PDF p.20: radical slice as a subset of the radical itself. -/
def radicalSlice (D : LeviSplitting A) (W : Set A) : Set D.r :=
  {R | (R : A) ∈ W}

/-- Definition 4.1, PDF p.20: image cone; no closedness is built into this definition. -/
def quotientCone (D : LeviSplitting A) (W : Set A) : Set D.s := piS D '' W

/-- Lemma 4.3, PDF p.21: the projected edge, distinguished from the base lineality. -/
def projectedEdge (D : LeviSplitting A) (W : Set A) : Set D.s := piS D '' edge W

/-- Definition 4.1, PDF p.20: actual fiber at a base point, also defined off the base. -/
def fiber (D : LeviSplitting A) (W : Set A) (S : D.s) : Set D.r :=
  {R | (S : A) + (R : A) ∈ W}

/-- Proposition 4.8, PDF p.25: graph in the FULL product, not in C times r. -/
def fiberGraph (D : LeviSplitting A) (C : Set D.s) (F : D.s → Set D.r) :
    Set (D.s × D.r) := {p | p.1 ∈ C ∧ p.2 ∈ F p.1}

/-- Equation (39), PDF p.25: reconstruction from the supplied fibers. -/
def reconstructLeviFibers (D : LeviSplitting A) (C : Set D.s) (F : D.s → Set D.r) : Set A :=
  {x | ∃ S ∈ C, ∃ R ∈ F S, x = (S : A) + (R : A)}

/-- Equation (38), PDF p.25: candidate edge computed before D5 or D6 is assumed. -/
def candidateEdge (D : LeviSplitting A) (C : Set D.s) (F : D.s → Set D.r) : Set A :=
  {x | ∃ S ∈ edge C, ∃ R, R ∈ F S ∧ -R ∈ F (-S) ∧ x = (S : A) + (R : A)}

/-- Equation (33), PDF p.24: a translated fiber, as a subset of g. -/
def slice (D : LeviSplitting A) (F : D.s → Set D.r) (S : D.s) : Set A :=
  (fun R : D.r => (S : A) + (R : A)) '' F S

/-- Proposition 4.8, PDF pp.24--25: exactly D1--D6; no given wedge or edge is input.
Fibers outside C have no significance and are never compared there. -/
def AdmissibleLeviFibers (D : LeviSplitting A) (C : Set D.s) (F : D.s → Set D.r) : Prop :=
  IsCone C ∧
  (∀ S ∈ C, (F S).Nonempty ∧ IsClosed (F S) ∧ Convex ℝ (F S)) ∧
  (∀ S ∈ C, ∀ T ∈ C, ∀ R ∈ F S, ∀ Q ∈ F T, R + Q ∈ F (S + T)) ∧
  (∀ a : ℝ, 0 ≤ a → ∀ S ∈ C, ∀ R ∈ F S, a • R ∈ F (a • S)) ∧
  IsClosed (fiberGraph D C F) ∧
  (∀ X ∈ candidateEdge D C F, expAd (piS D X) '' C ⊆ C) ∧
  (∀ X ∈ candidateEdge D C F, ∀ S ∈ C,
    expAd X '' slice D F S ⊆ slice D F (expAd (piS D X) S))

/-- Lemma 4.6, PDF p.23: all five fiber properties, including strict-positive equality. -/
def FiberProperties (D : LeviSplitting A) (W : Set A) : Prop :=
  (∀ S ∈ quotientCone D W,
    (fiber D W S).Nonempty ∧ IsClosed (fiber D W S) ∧ Convex ℝ (fiber D W S)) ∧
  fiber D W 0 = radicalSlice D W ∧
  (∀ S ∈ quotientCone D W, ∀ T ∈ quotientCone D W,
    ∀ R ∈ fiber D W S, ∀ Q ∈ fiber D W T, R + Q ∈ fiber D W (S + T)) ∧
  (∀ a : ℝ, 0 ≤ a → ∀ S ∈ quotientCone D W,
    (fun R => a • R) '' fiber D W S ⊆ fiber D W (a • S)) ∧
  (∀ a : ℝ, 0 < a → ∀ S ∈ quotientCone D W,
    (fun R => a • R) '' fiber D W S = fiber D W (a • S)) ∧
  IsClosed (fiberGraph D (quotientCone D W) (fiber D W))

/-- Lemma 4.3, PDF p.21: projected edge is a closed Lie subalgebra and acts on C. -/
def QuotientProperties (D : LeviSplitting A) (W : Set A) : Prop :=
  IsCone (quotientCone D W) ∧
  (∃ e : LieSubalgebra ℝ D.s, (e : Set D.s) = projectedEdge D W) ∧
  IsClosed (projectedEdge D W) ∧
  ∀ S ∈ projectedEdge D W, expAd S '' quotientCone D W ⊆ quotientCone D W

/-- Proposition 4.7, PDF p.24: FCC, together with membership of its target base. -/
def FCC (D : LeviSplitting A) (W : Set A) : Prop :=
  ∀ X ∈ edge W, ∀ S ∈ quotientCone D W,
    expAd (piS D X) S ∈ quotientCone D W ∧
    expAd X '' slice D (fiber D W) S ⊆ slice D (fiber D W) (expAd (piS D X) S)

/-- Proposition 4.8, PDF p.25: every reconstruction conclusion and uniqueness. -/
def ReconstructionResult (D : LeviSplitting A) (C : Set D.s)
    (F : D.s → Set D.r) : Prop :=
  IsLieWedge (reconstructLeviFibers D C F) ∧
  radicalSlice D (reconstructLeviFibers D C F) = F 0 ∧
  quotientCone D (reconstructLeviFibers D C F) = C ∧
  edge (reconstructLeviFibers D C F) = candidateEdge D C F ∧
  (∀ S ∈ C, fiber D (reconstructLeviFibers D C F) S = F S) ∧
  ∀ V : Set A, quotientCone D V = C →
    (∀ S ∈ C, fiber D V S = F S) → V = reconstructLeviFibers D C F

/-- Definition 2.9, PDF p.9: Bouligand tangent cone with positive scalars.
This avoids Mathlib's bilateral scalar tangent cone. -/
def contingent {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    (C : Set E) (x : E) : Set E :=
  {v | ∃ (y : ℕ → E) (a : ℕ → ℝ),
    (∀ n, y n ∈ C) ∧ (∀ n, 0 < a n) ∧
    Filter.Tendsto y Filter.atTop (nhds x) ∧
    Filter.Tendsto (fun n => a n • (y n - x)) Filter.atTop (nhds v)}

/-- Equation (48), PDF p.29: derivative through the tangent of the entire graph. -/
def fiberDerivative (D : LeviSplitting A) (W : Set A) (S : D.s) (R : D.r)
    (V : D.s) : Set D.r :=
  {Q | (V, Q) ∈ contingent (fiberGraph D (quotientCone D W) (fiber D W)) (S, R)}

/-- Equation (3), PDF p.6: the actual action of s on its radical ideal. -/
def action (D : LeviSplitting A) (S : D.s) (R : D.r) : D.r :=
  ⟨⁅(S : A), (R : A)⁆, _root_.lie_mem_right ℝ A D.r (S : A) (R : A) R.property⟩

/-- Sanity: no off-base assignment is introduced by actual fibers at zero. -/
example (D : LeviSplitting A) (W : Set A) : fiber D W 0 = radicalSlice D W := by
  ext R
  simp [fiber, radicalSlice]

/-- Sanity: the coordinate map really adds the two embedded components. -/
example (D : LeviSplitting A) (S : D.s) (R : D.r) :
    coords D (S, R) = (S : A) + (R : A) := rfl

/-- Sanity: the candidate edge is computed directly from two opposite fibers. -/
example (D : LeviSplitting A) (C : Set D.s) (F : D.s → Set D.r) (x : A) :
    x ∈ candidateEdge D C F ↔
      ∃ S ∈ edge C, ∃ R, R ∈ F S ∧ -R ∈ F (-S) ∧ x = (S : A) + (R : A) := Iff.rfl

end Coordinates

open Coordinates

section AbstractResults

variable {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    [T2Space A] [FiniteDimensional ℝ A]

end AbstractResults

open QAlgorithms.Papers.Independent.Information100

/-- Sections 2.2 and 2.4, PDF pp.7,10: full superoperator matrix in matrix units.
The accepted P26 convention makes multiplication composition and Choi output-first. -/
abbrev Super (d : ℕ) := P26.Map d

/-- Sections 2.1 and 2.2, PDF pp.5,7: a Lie subalgebra carries the topology
inherited from its ambient real Lie algebra, including superoperator and Gaussian
moment spaces. Reuse the topological additive group instance on its underlying
submodule; no new assumption is introduced. -/
local instance inheritedSubalgebraTopologicalAddGroup {A : Type*}
    [LieRing A] [LieAlgebra ℝ A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    (g : LieSubalgebra ℝ A) : IsTopologicalAddGroup g :=
  inferInstanceAs (IsTopologicalAddGroup g.toSubmodule)

/-- Coordinate wrapper for a specified action on operators; no matrix is assumed. -/
def superOfAction {d : ℕ} (L : P59.Operator d → P59.Operator d) : Super d :=
  fun p q => L (Matrix.single q.1 q.2 1) p.1 p.2

/-- Section 2.4, PDF p.10: actual rank-one dissipator in matrix-unit coordinates. -/
def dissipatorMap {d : ℕ} (L : P59.Operator d) : Super d :=
  superOfAction (P59.dissipator L)

/-- Section 2.4, PDF p.10: actual Hamiltonian action with its minus-i sign. -/
def coherentMap {d : ℕ} (H : P59.Operator d) : Super d :=
  superOfAction (P59.coherent H)

/-- Lemma 2.13, PDF p.11: Hamiltonian generators with the scalar gauge fixed. -/
def Hamiltonian {d : ℕ} (L : Super d) : Prop :=
  P59.IsHamiltonianAction (P26.applyMap L)

/-- Section 2.2, PDF p.7: ambient Hermiticity-preserving trace-annihilating action. -/
def LK {d : ℕ} (L : Super d) : Prop := P59.IsLKAction (P26.applyMap L)

/-- Remark 2.18, PDF p.13: a physical unital dissipator has zero Hamiltonian part. -/
def UnitalDissipator {d : ℕ} (F : Fin (d^2-1) → P59.Operator d)
    (L : Super d) : Prop :=
  (∃ K : Matrix (Fin (d^2-1)) (Fin (d^2-1)) ℂ,
    K.PosSemidef ∧ P26.applyMap L = P59.kossakowskiAction F 0 K) ∧
  P26.applyMap L 1 = 0

/-- Sanity: wrapping a zero jump produces the zero superoperator. -/
example (d : ℕ) : dissipatorMap (0 : P59.Operator d) = 0 := by
  ext p q
  simp [dissipatorMap, superOfAction, P59.dissipator]

/-- Section 2.4 and Example 4.15, PDF pp.10,28: standard Pauli operators,
with false and true corresponding to the computational indices 0 and 1. -/
def sigma (i : Fin 3) : P59.Operator 2 :=
  fun a b => QAlgorithms.QubitChannels.sigma i (a.val == 1) (b.val == 1)

/-- Example 4.15, PDF p.28: Hilbert--Schmidt orthonormal Pauli basis. -/
def pauliBasis : Fin (2^2-1) → P59.Operator 2 :=
  fun j => ((Real.sqrt 2 : ℂ)⁻¹) • sigma j

/-- Remark 2.18, PDF p.13, and Section 5, PDF p.33: sigma-minus=|1><0|. -/
def sigmaMinus : P59.Operator 2 := Matrix.single 1 0 1

/-- Sections 2.2 and 4.4, PDF pp.8,27--28: Bloch linear coefficient of a generator. -/
def blochQ (L : Super 2) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (sigma i * P26.applyMap L (sigma j)).trace.re / 2

/-- Sections 2.2 and 4.4, PDF pp.8,27--28: inhomogeneous Bloch coefficient. -/
def blochB (L : Super 2) : Fin 3 → ℝ :=
  fun i => (sigma i * P26.applyMap L 1).trace.re / 2

/-- Example 4.15, PDF p.28: the actual affine-generator action, including translation. -/
def blochLift (Q : Matrix (Fin 3) (Fin 3) ℝ) (b : Fin 3 → ℝ) : Super 2 :=
  superOfAction (fun X => (X.trace / 2) • (∑ i, (b i : ℂ) • sigma i) +
    ∑ j, ((sigma j * X).trace / 2) • (∑ i, (Q i j : ℂ) • sigma i))

/-- Canonical normalized Pauli Kossakowski matrix, PDF pp.13,28.
The imaginary antisymmetric part uses the actual Bloch translation. -/
def pauliKossakowskiMatrix (L : Super 2) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((2⁻¹ : ℝ) • (blochQ L + (blochQ L).transpose) -
    ((blochQ L).trace / 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).map Complex.ofReal +
    (Complex.I / 2) • (P59.rotationGenerator (blochB L)).map Complex.ofReal

/-- Example 4.15, PDF pp.27--28: full-cone base in the affine Levi splitting. -/
def fullQubitBase : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {S | S.trace = 0 ∧ ∃ (a : ℝ) (b : Fin 3 → ℝ),
    P59.IsPhysicalAction pauliBasis (P26.applyMap (blochLift (S + a • 1) b))}

/-- Example 4.15, PDF pp.27--28: full fiber with radical coordinates (lambda,b). -/
def fullQubitFiber (S : Matrix (Fin 3) (Fin 3) ℝ) : Set (ℝ × (Fin 3 → ℝ)) :=
  {p | P59.IsPhysicalAction pauliBasis (P26.applyMap (blochLift (S + p.1 • 1) p.2))}

/-- Example 4.15, PDF p.28: anisotropic traceless base point S_t. -/
def radialBase (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  t • Matrix.diagonal ![1, 1, -2]

/-- Sanity: Pauli reindexing fixes the declared computational lowering operator. -/
example : sigmaMinus 1 0 = 1 := by simp [sigmaMinus, Matrix.single]

/-- Sanity: the full affine zero data produce the zero superoperator. -/
example : blochLift 0 0 = 0 := by
  ext p q
  simp [blochLift, superOfAction]

/-- Section 6.3, PDF pp.38--39: finite first-moment drift matrix only. -/
def gaussianA (r gamma : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![-gamma/2-r, -gamma/2+r]

/-- Section 6.3, PDF p.38: diffusion matrix in the [Q,P]=i convention. -/
def gaussianD (gamma : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := (gamma/2) • 1

/-- Section 6.3, PDF p.38: CCR symplectic matrix for the Q,P ordering. -/
def ccrOmega : Matrix (Fin 2) (Fin 2) ℝ := !![0,1; -1,0]

/-- Section 6.3, PDF pp.38--39: infinitesimal moment-level CP matrix. -/
def gaussianCP (r gamma : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (gaussianD gamma).map Complex.ofReal - (Complex.I/2) •
    (gaussianA r gamma * ccrOmega + ccrOmega * (gaussianA r gamma).transpose).map Complex.ofReal

/-- Section 2.5, PDF p.13: Hurwitz means strictly negative real parts of all eigenvalues. -/
def Hurwitz {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ z : ℂ, (A.map Complex.ofReal - z • 1).det = 0 → z.re < 0

/-- Sanity: zero rates give zero CP data, rather than a spurious positive gap. -/
example : gaussianCP 0 0 = 0 := by
  have hA : gaussianA 0 0 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [gaussianA, Matrix.diagonal_apply]
  ext i j
  simp [gaussianCP, gaussianD, hA]

section ProjectionClosedness

/-- Remark 4.5, PDF p.22: the concrete three-dimensional closed cone. -/
def projectionExample : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2.2 ∧ p.2.1 ^ 2 ≤ p.1 * p.2.2}

/-- Remark 4.5, PDF p.22: projection retaining y and z. -/
def yzProjection (p : ℝ × ℝ × ℝ) : ℝ × ℝ := (p.2.1, p.2.2)

/-- Remark 4.5, PDF p.22: polyhedral cone, expressed by finitely many closed
homogeneous half-spaces; coefficients are actual real linear functionals. -/
def PolyhedralCone {A : Type*} [AddCommGroup A] [Module ℝ A] (W : Set A) : Prop :=
  ∃ (m : ℕ) (f : Fin m → A →ₗ[ℝ] ℝ), W = {x | ∀ i, 0 ≤ f i x}

/-- Sanity: z=0 forces y=0 in the example; no condition on x beyond x>=0. -/
example (x y : ℝ) : (x, y, (0 : ℝ)) ∈ projectionExample ↔ 0 ≤ x ∧ y = 0 := by
  change (0 ≤ x ∧ 0 ≤ (0 : ℝ) ∧ y ^ 2 ≤ x * 0) ↔ 0 ≤ x ∧ y = 0
  constructor
  · rintro ⟨hx, _, hy⟩
    exact ⟨hx, by nlinarith [sq_nonneg y]⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨hx, le_refl 0, by norm_num⟩

end ProjectionClosedness

section LocalConstruction

variable {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    [T2Space A] [FiniteDimensional ℝ A]

/-- Section 3.1, PDF pp.15--17: closed conical hull formed by intersection.
The ambient full space belongs to the defining family, including for empty input. -/
def closedConicalHull (G : Set A) : Set A :=
  {x | ∀ C : Set A, IsClosed C → IsCone C → G ⊆ C → x ∈ C}

/-- Definition 3.2, PDF p.15: minimal LOCAL wedge, not the global tangent wedge. -/
def minimalWedge (G : Set A) : Set A :=
  {x | x ∈ LieSubalgebra.lieSpan ℝ A G ∧
    ∀ W : Set A, IsLieWedge W → G ⊆ W → x ∈ W}

/-- Proposition 3.5, PDF pp.16--17: the finite-product group orbit of the edge.
Since the edge is symmetric, inverses are included through exp(ad(-X)). -/
def edgeOrbit (W : Set A) : Set A :=
  {y | ∃ (xs : List A) (x : A),
    (∀ z ∈ xs, z ∈ edge W) ∧ x ∈ W ∧
    y = xs.foldr (fun z v => expAd z v) x}

/-- Proposition 3.5, PDF pp.16--17: one whole orbit-and-closed-hull step. -/
def orbitStep (W : Set A) : Set A := closedConicalHull (edgeOrbit W)

/-- Proposition 3.5, PDF pp.16--17: actual recursive iteration from the input cone. -/
def wedgeStage (G : Set A) : ℕ → Set A
  | 0 => closedConicalHull G
  | n + 1 => orbitStep (wedgeStage G n)

/-- Sanity: stage zero is determined solely by the supplied generator set. -/
example (G : Set A) : wedgeStage G 0 = closedConicalHull G := rfl

end LocalConstruction

/-- Definition 3.4, PDF p.16: closure of finite positive-time products in the
ambient superoperator space, not closure inside an immersed subgroup. -/
def reachability {d : ℕ} (G : Set (Super d)) : Set (Super d) :=
  closure {P | ∃ xs : List (ℝ × Super d),
    (∀ p ∈ xs, 0 ≤ p.1 ∧ p.2 ∈ G) ∧
    P = (xs.map (fun p => NormedSpace.exp (p.1 • p.2))).prod}

/-- Definition 3.4, PDF p.16: tangent wedge of the closed semigroup, equivalently
those X whose positive-time exponential belongs to it for every nonnegative time. -/
def globalTangentWedge {d : ℕ} (G : Set (Super d)) : Set (Super d) :=
  {X | ∀ t : ℝ, 0 ≤ t → NormedSpace.exp (t • X) ∈ reachability G}

/-- Section 6.1, PDF p.37: homogeneous-coordinate model of aff(R^n).
Only the last row is constrained; translations occupy the last column. -/
def affineAlgebra (n : ℕ) : LieSubalgebra ℝ (Matrix (Fin (n+1)) (Fin (n+1)) ℝ) where
  carrier := {M | ∀ j, M (Fin.last n) j = 0}
  zero_mem' := by intro j; rfl
  add_mem' := by intro A B hA hB j; simp [hA j, hB j]
  smul_mem' := by intro c A hA j; simp [hA j]
  lie_mem' := by
    intro A B hA hB j
    change (A * B - B * A) (Fin.last n) j = 0
    change ∀ k, A (Fin.last n) k = 0 at hA
    change ∀ k, B (Fin.last n) k = 0 at hB
    simp [Matrix.mul_apply, hA, hB]

/-- Sanity: in zero spatial dimension the affine algebra is the zero algebra. -/
example : affineAlgebra 0 = ⊥ := by
  ext M
  change (∀ j, M (Fin.last 0) j = 0) ↔ M = 0
  constructor
  · intro h
    ext i j
    have hi : i = Fin.last 0 := by
      apply Fin.ext
      have hbound : i.val < 1 := i.isLt
      omega
    simpa [hi] using h j
  · rintro rfl j
    rfl

/-- Example 1.1 and Appendix A.4, PDF pp.3,44: standard raw Gell--Mann basis. -/
def gellMann : Fin (3^2-1) → P59.Operator 3 :=
  ![!![0,1,0; 1,0,0; 0,0,0],
    !![0,-Complex.I,0; Complex.I,0,0; 0,0,0],
    !![1,0,0; 0,-1,0; 0,0,0],
    !![0,0,1; 0,0,0; 1,0,0],
    !![0,0,-Complex.I; 0,0,0; Complex.I,0,0],
    !![0,0,0; 0,0,1; 0,1,0],
    !![0,0,0; 0,0,-Complex.I; 0,Complex.I,0],
    (Real.sqrt 3 : ℂ)⁻¹ • !![1,0,0; 0,1,0; 0,0,-2]]

/-- Appendix A.4, PDF p.44: default orthonormal Gell--Mann coordinates. -/
def gellMannBasis : Fin (3^2-1) → P59.Operator 3 :=
  fun j => (Real.sqrt 2 : ℂ)⁻¹ • gellMann j

/-- Example 1.1, PDF p.3: first actual rank-one jump. -/
def qutritJump1 : P59.Operator 3 :=
  gellMann ⟨0, by decide⟩ + Complex.I • gellMann ⟨3, by decide⟩

/-- Example 1.1, PDF p.3: second actual rank-one jump. -/
def qutritJump2 : P59.Operator 3 :=
  gellMann ⟨1, by decide⟩ + Complex.I • gellMann ⟨4, by decide⟩

/-- Appendix A.4, PDF p.44: orthogonal compression away from the UNNORMALIZED
maximally entangled vector sum_i |ii>. The factor 1/d is indispensable. -/
def conditionalProjection (d : ℕ) : Super d :=
  1 - (d : ℂ)⁻¹ • (fun p q => if p.1 = p.2 ∧ q.1 = q.2 then 1 else 0)

/-- Example 1.1, PDF p.3: conditional Choi matrix in the accepted output-first
unnormalized convention, retained as a full d^2 by d^2 matrix including its kernel. -/
def compressedGeneratorChoi {d : ℕ} (L : Super d) : Super d :=
  conditionalProjection d * P26.choi L * conditionalProjection d

/-- Sanity: the first qutrit jump has the printed (0,2) entry i. -/
example : qutritJump1 0 2 = Complex.I := by
  simp [qutritJump1, gellMann]

/-- Section 4.6.1, PDF p.31: independently actuable cascaded qutrit rays. -/
def cascadeG : Set (Super 3) :=
  {dissipatorMap (Matrix.single 0 1 1), dissipatorMap (Matrix.single 1 2 1)}

/-- Section 4.6.1, PDF p.31: selected simultaneous generator, distinct from the
multi-ray control specification. -/
def cascadeDrift (a b : ℝ) : Super 3 :=
  a • dissipatorMap (Matrix.single 0 1 1) + b • dissipatorMap (Matrix.single 1 2 1)

/-- Section 4.6.2, PDF p.32: unit-rate pauliDepolarizingGenerator noise, independently switchable. -/
def pauliDepolarizingGenerator : Super 2 := ∑ i : Fin 3, dissipatorMap (sigma i)

/-- Section 4.6.2, PDF p.32: the three Hamiltonian control directions. -/
def qubitControl : LieSubalgebra ℝ (Super 2) :=
  LieSubalgebra.lieSpan ℝ (Super 2) (Set.range (fun i : Fin 3 => coherentMap (sigma i)))

/-- Section 4.6.2, PDF p.32: signed Hamiltonian rays and one positive noise ray. -/
def depolarizingG (gamma : ℝ) : Set (Super 2) :=
  {X | (∃ i : Fin 3, X = coherentMap (sigma i) ∨ X = -coherentMap (sigma i)) ∨
    X = gamma • pauliDepolarizingGenerator}

/-- Section 4.6.2, PDF p.32: fiber using the central pauliDepolarizingGenerator coordinate. -/
def depolarizingFiber (S : Super 2) : Set ℝ :=
  {a | S + a • pauliDepolarizingGenerator ∈ minimalWedge (depolarizingG 1)}

/-- Sanity: the unit-rate input really includes the independently switchable noise ray. -/
example : pauliDepolarizingGenerator ∈ depolarizingG 1 := by
  right
  simp

/-- Section 5, PDF p.33: ordered tensor product A on the first qubit, B on the second. -/
def tensor2 (A B : P59.Operator 2) : P59.Operator 4 :=
  fun i j => A ⟨i.val / 2, by omega⟩ ⟨j.val / 2, by omega⟩ *
    B ⟨i.val % 2, by omega⟩ ⟨j.val % 2, by omega⟩

/-- Section 5, PDF p.33: Hamiltonians sigma_A,i tensor I_B divided by two. -/
def twoQubitH (i : Fin 3) : P59.Operator 4 := (2⁻¹ : ℂ) • tensor2 (sigma i) 1

/-- Section 5, PDF p.33: actual projector-modulated jump J0. -/
def modulatedJ0 : P59.Operator 4 := tensor2 (Matrix.single 0 0 1) sigmaMinus

/-- Section 5, PDF p.33: actual projector-modulated jump J1. -/
def modulatedJ1 : P59.Operator 4 := tensor2 (Matrix.single 1 1 1) sigmaMinus

/-- Equation (53), PDF p.33: bilinear cross-superoperator, with half anticommutator. -/
def crossSuper {d : ℕ} (L M : P59.Operator d) : Super d :=
  superOfAction (fun X => M * X * Lᴴ + L * X * Mᴴ -
    (2⁻¹ : ℂ) • ((Mᴴ * L + Lᴴ * M) * X + X * (Mᴴ * L + Lᴴ * M)))

/-- Sanity: tensor order places |0><0| tensor |1><0| at row 1, column 0. -/
example : modulatedJ0 1 0 = 1 := by
  simp [modulatedJ0, tensor2, sigmaMinus, Matrix.single]

/-- Section 2.1, PDF p.6: maximal nilpotent ideal, formed in the complete lattice
of ideals; the supremum here is lattice-theoretic, not a real sSup. -/
def nilradical {A : Type*} [LieRing A] [LieAlgebra ℝ A] : LieIdeal ℝ A :=
  sSup {I : LieIdeal ℝ A | LieModule.IsNilpotent I I}

/-- Corollary 2.6, PDF p.8: scalar linear part plus arbitrary translations.
This is the semidirect radical, not a central direct sum. -/
def affineRadical (n : ℕ) : Set (affineAlgebra n) :=
  {X | ∃ a : ℝ, ∀ i j : Fin (n+1), i.val < n → j.val < n →
    (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) i j = if i = j then a else 0}

/-- Corollary 2.6 and Section 6.1, PDF pp.8,37: pure translations. -/
def affineTranslations (n : ℕ) : Set (affineAlgebra n) :=
  {X | ∀ i j : Fin (n+1), i.val < n → j.val < n →
    (X : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) i j = 0}

/-- Section 6.1, PDF p.37: identity on the linear coordinates, zero homogeneous row. -/
def affineIdentity (n : ℕ) : affineAlgebra n :=
  ⟨Matrix.diagonal (fun i => if i = Fin.last n then 0 else 1), by
    intro j
    simp [Matrix.diagonal_apply]⟩

/-- Sanity: the scalar linear identity vanishes at zero spatial dimension. -/
example : affineIdentity 0 = 0 := by
  apply Subtype.ext
  ext i j
  have hi : i = Fin.last 0 := by
    apply Fin.ext
    have hbound : i.val < 1 := i.isLt
    omega
  simp [affineIdentity, hi, Matrix.diagonal_apply]

/-- Section 6.3, PDF pp.38--39: faithful finite Gaussian moment representation on
(q,p,Vqq,Vqp,Vpp,1). Covariance evolves by A V+V A^T+D. -/
def momentMap (A D : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  !![A 0 0,A 0 1,0,0,0,0;
     A 1 0,A 1 1,0,0,0,0;
     0,0,2*A 0 0,2*A 0 1,0,D 0 0;
     0,0,A 1 0,A 0 0+A 1 1,A 0 1,D 0 1;
     0,0,0,2*A 1 0,2*A 1 1,D 1 1;
     0,0,0,0,0,0]

/-- Section 6.3, PDF p.39: one-sided squeezing ray. -/
def squeezeMoment (r : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  momentMap (Matrix.diagonal ![-r,r]) 0

/-- Section 6.3, PDF p.39: one-sided amplitude damping moment pair. -/
def dampingMoment (gamma : ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  momentMap ((-gamma/2) • 1) (gaussianD gamma)

/-- Section 6.3, PDF p.39: two independently actuable one-sided moment rays. -/
def gaussianG (r gamma : ℝ) : Set (Matrix (Fin 6) (Fin 6) ℝ) :=
  {squeezeMoment r, dampingMoment gamma}

/-- Section 6.3, PDF p.39: the specified two quadratic Hamiltonian drift matrices. -/
def squeezeMatrices : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![!![-1,0; 0,1], !![0,1; 1,0]]

/-- Section 6.3, PDF p.39: signed quadratic controls and nonzero one-sided damping. -/
def gaussianExtensionG (gamma : ℝ) : Set (Matrix (Fin 6) (Fin 6) ℝ) :=
  {X | (∃ i : Fin 2, X = momentMap (squeezeMatrices i) 0 ∨
    X = -momentMap (squeezeMatrices i) 0) ∨ X = dampingMoment gamma}

/-- Sanity: the finite moment representation has a zero homogeneous last row. -/
example (A D : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 6) : momentMap A D 5 j = 0 := by
  simp [momentMap, ← Matrix.zero_empty]

/-- Remark 4.14, PDF p.27: fixed pointed Lie-generating Hamiltonian cone in su(2). -/
def pointedHamiltonianCone : Set (Super 2) :=
  closedConicalHull (Set.range (fun i : Fin 3 => coherentMap (sigma i)))

/-- Remark 4.14(1), PDF p.27: actual first counterexample cone. -/
def constantCounterexample : Set (Super 2) :=
  {X | ∃ S ∈ pointedHamiltonianCone, ∃ a : ℝ, 0 ≤ a ∧ X = S + a • pauliDepolarizingGenerator}

/-- Remark 4.14(2), PDF p.27: conical hull of FOUR generators, not a union of cones. -/
def varyingCounterexample : Set (Super 2) :=
  closedConicalHull (Set.range (fun i : Fin 3 => coherentMap (sigma i)) ∪
    {coherentMap (sigma 0) + (2 : ℝ) • pauliDepolarizingGenerator})

/-- Remark 4.14, PDF p.27: central-coordinate fiber in su(2) direct-sum R L_D. -/
def centralFiber (W : Set (Super 2)) (S : Super 2) : Set ℝ :=
  {a | S + a • pauliDepolarizingGenerator ∈ W}

/-- Remark 4.14, PDF p.27: Levi projection in the concrete reductive model.
Tr(Q_D)=-12, so this subtracts precisely the central coordinate. -/
def depolarizingProjection (X : Super 2) : Super 2 :=
  X - ((blochQ X).trace / (-12 : ℝ)) • pauliDepolarizingGenerator

/-- Sanity: both counterexample fibers are defined by actual lifts, not assumptions. -/
example (W : Set (Super 2)) (a : ℝ) :
    a ∈ centralFiber W 0 ↔ a • pauliDepolarizingGenerator ∈ W := by
  simp [centralFiber]

/-- Section 6.4, PDF pp.39--40: rotation generator, in homogeneous Euclidean coordinates. -/
def euclideanJ : Matrix (Fin 3) (Fin 3) ℝ := !![0,-1,0; 1,0,0; 0,0,0]

/-- Section 6.4, PDF pp.39--40: x translation. -/
def euclideanPx : Matrix (Fin 3) (Fin 3) ℝ := Matrix.single 0 2 1

/-- Section 6.4, PDF pp.39--40: y translation. -/
def euclideanPy : Matrix (Fin 3) (Fin 3) ℝ := Matrix.single 1 2 1

/-- Section 6.4, PDF pp.39--40: actual e(2), whose TRUE Levi factor is zero. -/
def euclideanAlgebra : LieSubalgebra ℝ (Matrix (Fin 3) (Fin 3) ℝ) :=
  LieSubalgebra.lieSpan ℝ (Matrix (Fin 3) (Fin 3) ℝ) {euclideanJ, euclideanPx, euclideanPy}

/-- Equation (62), PDF p.40: the positive quadrant in the translation ideal. -/
def quadrant : Set (ℝ × ℝ) := {v | 0 ≤ v.1 ∧ 0 ≤ v.2}

/-- Section 6.4, PDF p.40: the assembled candidate with reversible rotations. -/
def euclideanCandidate : Set (Matrix (Fin 3) (Fin 3) ℝ) :=
  {X | ∃ a b c : ℝ, 0 ≤ b ∧ 0 ≤ c ∧
    X = a • euclideanJ + b • euclideanPx + c • euclideanPy}

/-- Section 6.4, PDF p.40: ordinary rotation action on the translation plane. -/
def rotatePlane (t : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos t * v.1 - Real.sin t * v.2, Real.sin t * v.1 + Real.cos t * v.2)

/-- Section 6.4, PDF p.40: translation slice of any candidate, without mislabelling
so(2) as a semisimple Levi factor. -/
def translationSlice (W : Set (Matrix (Fin 3) (Fin 3) ℝ)) : Set (ℝ × ℝ) :=
  {v | v.1 • euclideanPx + v.2 • euclideanPy ∈ W}

/-- Section 6.4, PDF pp.39--40: varying fibers over a subspace in the abelian example. -/
def absoluteEpigraph : Set (ℝ × ℝ) := {p | |p.1| ≤ p.2}

/-- Sanity: pi rotation takes the positive x direction out of the quadrant. -/
example : rotatePlane Real.pi (1,0) = (-1,0) := by
  simp [rotatePlane]

/-- Remark 6.4, PDF p.40: bidirectional x control and independently switchable z noise. -/
def dephasingG : Set (Super 2) :=
  {coherentMap (sigma 0), -coherentMap (sigma 0), dissipatorMap (sigma 2)}

/-- Remark 6.4, PDF p.40: the declared one-noise-ray candidate. -/
def dephasingCandidate : Set (Super 2) :=
  {X | ∃ a b : ℝ, 0 ≤ b ∧ X = a • coherentMap (sigma 0) + b • dissipatorMap (sigma 2)}

/-- Equation (64), PDF p.40: full conic orbit closure, allowing all yz jump directions. -/
def dephasingOrbitCone : Set (Super 2) :=
  closedConicalHull {L | ∃ a b : ℝ, L = dissipatorMap ((a : ℂ) • sigma 1 + (b : ℂ) • sigma 2)}

/-- Remark 6.4, PDF p.40: unit-total-rate orbit in the yz plane. -/
def fixedDephasingOrbit : Set (Super 2) :=
  {L | ∃ a b : ℝ, a^2+b^2 = 1 ∧
    L = dissipatorMap ((a : ℂ) • sigma 1 + (b : ℂ) • sigma 2)}

/-- Remark 6.4, PDF p.40: a REAL yz Kossakowski block in raw Pauli coordinates.
The factor two converts it to the accepted orthonormal Pauli basis. -/
def yzNoise (K : Matrix (Fin 2) (Fin 2) ℝ) : Super 2 :=
  superOfAction (P59.kossakowskiAction pauliBasis 0
    (fun i j => if hi : 0 < i.val then
      if hj : 0 < j.val then
        (2 : ℂ) * (K ⟨i.val-1, by omega⟩ ⟨j.val-1, by omega⟩ : ℂ)
      else 0 else 0))

/-- Remark 6.4, PDF p.40: radical slice of the actual generated local wedge,
expressed in ambient coordinates without choosing a Levi complement. -/
def dephasingRadicalSlice : Set (Super 2) :=
  {X | X ∈ minimalWedge dephasingG ∧
    ∃ Y : LieSubalgebra.lieSpan ℝ (Super 2) dephasingG,
      Y ∈ LieAlgebra.radical ℝ (LieSubalgebra.lieSpan ℝ (Super 2) dephasingG) ∧
      (Y : Super 2) = X}

/-- Sanity: the yz-block embedding kills the unused x row and column. -/
example : yzNoise 0 = 0 := by
  ext p q
  simp [yzNoise, superOfAction, P59.kossakowskiAction, P59.coherent]

/-- Section 5, PDF p.33: signed primary controls and two INDEPENDENT unit noise rays. -/
def twoQubitG : Set (Super 4) :=
  {X | (∃ i : Fin 3, X = coherentMap (twoQubitH i) ∨ X = -coherentMap (twoQubitH i)) ∨
    X = dissipatorMap modulatedJ0 ∨ X = dissipatorMap modulatedJ1}

/-- Section 5, PDF p.33: the actual primary control algebra. -/
def twoQubitControl : LieSubalgebra ℝ (Super 4) :=
  LieSubalgebra.lieSpan ℝ (Super 4) (Set.range (fun i : Fin 3 => coherentMap (twoQubitH i)))

/-- Equation (54), PDF p.34: the exact ordered recursive words; zero-based Lean indices.
The certificate representative E=2 D1 is used only here. -/
def twoQubitWords : Fin 22 → Super 4 :=
  let X := coherentMap (twoQubitH 0)
  let Y := coherentMap (twoQubitH 1)
  let Z := coherentMap (twoQubitH 2)
  let D := dissipatorMap modulatedJ0
  let E := (2 : ℝ) • dissipatorMap modulatedJ1
  let b6 := ⁅X,D⁆
  let b7 := ⁅X,E⁆
  let b8 := ⁅X,b6⁆
  let b9 := ⁅Y,D⁆
  let b10 := ⁅Y,E⁆
  let b11 := ⁅Y,b6⁆
  let b12 := ⁅Y,b9⁆
  let b13 := ⁅D,b6⁆
  let b14 := ⁅D,b7⁆
  let b15 := ⁅D,b8⁆
  let b16 := ⁅D,b9⁆
  let b17 := ⁅D,b10⁆
  let b18 := ⁅D,b13⁆
  let b19 := ⁅D,b15⁆
  let b20 := ⁅D,b16⁆
  let b21 := ⁅b6,b9⁆
  let b22 := ⁅b6,b16⁆
  ![X,Y,Z,D,E,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,b21,b22]

/-- Equation (56), PDF p.34: the three standard adjoint rotation matrices. -/
def adjointRotations : Fin 3 → Matrix (Fin 3) (Fin 3) ℝ :=
  ![!![0,0,0; 0,0,-1; 0,1,0], !![0,0,1; 0,0,0; -1,0,0], !![0,-1,0; 1,0,0; 0,0,0]]

/-- Sanity: the final word is the bracket that escapes the truncated 21-word span. -/
example : twoQubitWords 21 = ⁅twoQubitWords 5,twoQubitWords 15⁆ := rfl

/-- Section 5.2, PDF pp.35--36: one independently rotatable dissipative orbit.
The determinant-one restriction is SU(2), not a common linked rotation of both rays. -/
def modulatedOrbit (i : Fin 2) : Set (Super 4) :=
  {X | ∃ U : Matrix.unitaryGroup (Fin 2) ℂ,
    (U : P59.Operator 2).det = 1 ∧
    X = dissipatorMap (tensor2
      ((U : P59.Operator 2) * Matrix.single i i 1 * (U : P59.Operator 2)ᴴ) sigmaMinus)}

/-- Equation (61), PDF p.36: actual control conjugation of a superoperator. -/
def controlConjugation (U : Matrix.unitaryGroup (Fin 2) ℂ) (L : Super 4) : Super 4 :=
  let V := tensor2 (U : P59.Operator 2) 1
  superOfAction (fun X => V * P26.applyMap L (Vᴴ * X * V) * Vᴴ)

section ControlAverages

/-- Equation (61), PDF p.36: the control group uses its usual Borel sigma-algebra.
The averaging measure is supported on the determinant-one subgroup. -/
local instance controlGroupMeasurableSpace :
    MeasurableSpace (Matrix.unitaryGroup (Fin 2) ℂ) :=
  borel (Matrix.unitaryGroup (Fin 2) ℂ)

/-- The specified measurable structure is exactly the Borel structure. -/
local instance controlGroupBorelSpace :
    BorelSpace (Matrix.unitaryGroup (Fin 2) ℂ) := ⟨rfl⟩

/-- The Frobenius norm already selected for superoperator matrices is continuous
in their inherited finite-product topology. Supply its existing Mathlib instance
explicitly for the integrability predicates in Equation (61). -/
local instance superContinuousENorm : ContinuousENorm (Super 4) :=
  @SeminormedAddGroup.toContinuousENorm (Super 4)
    (Matrix.frobeniusSeminormedAddCommGroup :
      SeminormedAddCommGroup (Super 4)).toSeminormedAddGroup

/-- Equation (61), PDF p.36: Bochner average with a specified normalized Haar measure.
Integrability is asserted in the theorem, never replaced by the integral's junk value. -/
def controlAverage (mu : MeasureTheory.Measure (Matrix.unitaryGroup (Fin 2) ℂ))
    (L : Super 4) : Super 4 := ∫ U, controlConjugation U L ∂mu

/-- Sanity: the average of zero is zero for every measure. -/
example (mu : MeasureTheory.Measure (Matrix.unitaryGroup (Fin 2) ℂ)) :
    controlAverage mu 0 = 0 := by
  have hAction (X : P59.Operator 4) : P26.applyMap (0 : Super 4) X = 0 := by
    ext i j
    change (Matrix.mulVec (0 : Super 4) (fun p => X p.1 p.2)) (i, j) = 0
    simp only [Matrix.zero_mulVec, Pi.zero_apply]
  have hConjugation (U : Matrix.unitaryGroup (Fin 2) ℂ) :
      controlConjugation U 0 = 0 := by
    dsimp only [controlConjugation]
    simp only [hAction, Matrix.mul_zero, Matrix.zero_mul]
    rfl
  simp only [controlAverage, hConjugation, MeasureTheory.integral_zero]

end ControlAverages

/-- Section 3.2, PDF p.18: simultaneous upper triangularization of a complex
matrix representation. Real Lie representations into complex matrices are exactly
the restrictions of the complexified representations used by the source. -/
def SimultaneouslyTriangularizable {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    {m : ℕ} (rho : A →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∃ P Q : Matrix (Fin m) (Fin m) ℂ, P*Q = 1 ∧ Q*P = 1 ∧
    ∀ (X : A) (i j : Fin m), j.val < i.val → (Q * rho X * P) i j = 0

/-- Section 3.2, PDF p.18: complete reducibility of the actual adjoint module. -/
def AdjointCompletelyReducible (A : Type*) [LieRing A] [LieAlgebra ℝ A] : Prop :=
  ∀ I : LieSubmodule ℝ A A, ∃ J : LieSubmodule ℝ A A,
    IsCompl I.toSubmodule J.toSubmodule

/-- Section 3.2, PDF p.18: action coupling requires the actual nonzero action
and nontrivial components in BOTH factors. -/
def ActionCoupled {A : Type*} [LieRing A] [LieAlgebra ℝ A]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul ℝ A]
    [T2Space A] [FiniteDimensional ℝ A]
    (D : LeviSplitting A) (W : Set A) : Prop :=
  (∃ S : D.s, ∃ R : D.r, action D S R ≠ 0) ∧
    radicalSlice D W ≠ {0} ∧ quotientCone D W ≠ {0}

/-- Sanity: zero matrices in every dimension have the standard triangular basis. -/
example (m : ℕ) (rho : ℝ →ₗ⁅ℝ⁆ Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ x, rho x = 0) : SimultaneouslyTriangularizable rho := by
  refine ⟨1,1,by simp,by simp,?_⟩
  intro x i j hij
  simp [h]

end QAlgorithms.Papers.Independent.Dependency50.P12


