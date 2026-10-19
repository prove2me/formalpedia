-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16
-- name    : QAlgorithms_Papers_Independent_Dependency50_P16
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T08:14:21.491207+00:00
-- url     : https://prove2.me/theorems/9dfacf6b-f06b-4267-addc-f92a0af4c33f
-- title:
--   Definitions for Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control
-- statement:
--   The objects the formalized statements of *Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control* (arXiv:2308.00561) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `RMat`: PDF pp.6,10: real matrices for reduced population dynamics and entry bounds.
--   - `simplex`: PDF p.5: the full simplex, without an ordering requirement.
--   - `chamber`: PDF p.5: the nonincreasing Weyl chamber.
--   - `vertex`: PDF p.5: the i-th simplex vertex (indices in Lean start at zero).
--   - `barycenter`: PDF p.5: the barycenter. The theorems always assume n >= 2.
--   - `spectralDiagonal`: PDF p.5: real diagonal embedding.
--   - `orderedSpectrum`: PDF pp.5,29: the ordered real spectrum, also for non-normalized Hermitian matrices.
--   - `specialUnitary`: PDF p.5: special unitaries are unitaries of determinant one.
--   - `sandwich`: PDF p.30: a two-sided multiplication map.
--   - `cpGenerator`: PDF p.30, (C.1): general CP-generator representation; no trace condition.
--   - `LindbladData`: PDF p.4: arbitrary finite GKSL data, with Hermitian drift.
--   - `driftK`: PDF pp.4,30: K = i H0 + (1/2) sum V*V.
--   - `gkslGenerator`: PDF p.4: the actual generator G = -L.
--   - `controlledData`: PDF p.4: a constant control adds -i[H,X].
--   - `semigroupEvolution`: PDF p.30: exp(tG), as an exponential of a continuous linear endomorphism.
--   - `cpSemigroup`: PDF p.30: continuous CP semigroup on nonnegative time.
--   - `quantumSemigroup`: PDF p.30: quantum dynamical means additionally trace preserving.
--   - `rates`: PDF pp.5-6, (2.3): rates of the finite jump family.
--   - `populationGenerator`: PDF p.6, (2.4): column convention for G_U = -L_U.
--   - `inducedCP`: PDF p.32: induced diagonal action for general CP data; need not be stochastic.
--   - `fields`: PDF p.6: compact family of induced fields.
--   - `derivatives`: PDF p.6: achievable derivatives at a vector.
--   - `stabilizable`: PDF p.8: relaxed stabilization, distinct from a single stationary field.
--   - `stronglyStabilizable`: PDF p.8: strong stabilization by one U.
--   - `stabilizableSystem`: PDF p.10: every simplex point is stabilizable.
--   - `integralPath`: PDF pp.3,6-7: integral trajectories; integrability is explicit on every compact interval. This gives local absolute continuity, also on an infinite time interval.
--   - `reducedSolution`: PDF p.6, Definition 2.1: measurable SU(n) controls, with the actual integral equation.
--   - `relaxedSolution`: PDF p.6, Definition 2.2: the differential inclusion holds almost everywhere.
--   - `FullControls`: PDF pp.3-4: a fixed family generating at least su(n) over the reals.
--   - `fullSolution`: PDF p.3: the unbounded, locally integrable real controls of system (B).
--   - `hamiltonianSolution`: PDF p.7: integrable traceless Hermitian Hamiltonian, with no chosen finite controls.
--   - `reachRAt`: PDF p.13: fixed-time reduced reachability.
--   - `reachCAt`: PDF p.13: fixed-time convexified reachability.
--   - `reachBAt`: PDF p.13: fixed-time full reachability.
--   - `reachR`: PDF p.13: all-time reachability includes T=0.
--   - `reachC`: PDF p.13: all-time convexified reachability.
--   - `reachB`: PDF p.13: all-time full reachability.
--   - `orbitSaturation`: PDF p.5: saturation of a spectral set by full unitary orbits.
--   - `Face`: PDF p.9: faces are specified by their nonempty coordinate support.
--   - `faceSet`: PDF p.9: the coordinate face itself.
--   - `faceInterior`: PDF p.9, footnote 6: positivity at precisely the coordinates of F.
--   - `faceTangent`: PDF p.9: the linear tangent space to the affine hull of F.
--   - `viable`: PDF p.9: all-time viability in the convexified system.
--   - `directlyReachable`: PDF p.19: direct reachability requires an initial point outside the face.
--   - `densitySupport`: PDF pp.32-33: support is the actual range of the density operator.
--   - `orthogonalProjector`: PDF p.32: matrix of the canonical orthogonal projection.
--   - `invariant`: PDF p.32: invariance of a linear subspace, including the zero subspace.
--   - `relaxationAlgebra`: PDF p.31: unital associative relaxation algebra.
--   - `extendedAlgebra`: PDF p.31: extended relaxation algebra includes K, not just the drift.
--   - `extendedStarAlgebra`: PDF p.34: the extended star algebra includes the drift and all adjoint jumps.
--   - `lazy`: PDF p.32: lazy subspaces are nonzero common invariant subspaces of the jumps.
--   - `collecting0`: PDF pp.32-33, footnote 23: collecting lattice with the zero subspace included.
--   - `collecting`: PDF pp.32-33: named collecting subspaces additionally are nonzero.
--   - `enclosure`: PDF p.34: enclosure means reducing all jumps and the original drift.
--   - `scalarOn`: PDF pp.10,33: scalar jump compressions mean purely Hamiltonian dissipation on S.
--   - `minimalCollecting`: PDF p.33: nonzero minimal element of the collecting-subspace lattice.
--   - `stationary`: PDF p.33: a stationary normalized density.
--   - `extremalStationary`: PDF p.33, footnote 25: extremality among all stationary densities.
--   - `uniqueStationaryOn`: PDF p.33: unique fixed density with full support S, among densities supported in S.
--   - `attractive`: PDF p.17, footnote 13: every initial density converges to this fixed density.
--   - `decaying`: PDF p.33: decay is tested on every normalized initial density.
--   - `asymptotic`: PDF p.33: orthogonal complement of a decaying subspace.
--   - `maximalDecay`: PDF p.33: the maximal decaying subspace is constructed by taking the supremum.
--   - `minimalAsymptotic`: PDF p.33: minimal asymptotic space, constructed from the decaying family.
--   - `commonEigenvector`: PDF pp.10,17: common normalized right eigenvector.
--   - `eigenvectorObstruction`: PDF p.14: every common right eigenvector is also a common left eigenvector. Normalization loses no nonzero eigenvector in finite dimension.
--   - `triangularizable`: PDF pp.10,12: one invertible basis triangularizes the entire set.
--   - `unitarilyTriangularizable`: PDF p.12, footnote 8: one unitary basis for the entire set.
--   - `solvableGenerated`: PDF pp.10,12: the generated complex commutator Lie algebra is solvable.
--   - `someRepresentation`: PDF p.4: quantify all actual representations of the same generator.
--   - `everyRepresentation`: PDF p.4: representation independence is expressed without any Kraus-rank restriction.
--   - `unital`: PDF p.4: unitality concerns the generator, rather than one jump.
--   - `purelyHamiltonian`: PDF p.25: purely Hamiltonian generators, allowing an arbitrary Hermitian Hamiltonian.
--   - `partialPopulation`: PDF pp.18,20: population in the first d coordinates.
--   - `inflow`: PDF p.17: total inflow across the d-dimensional cut.
--   - `outflow`: PDF p.17: total outflow across the same cut.
--   - `flowValues`: PDF p.17: exactly 0/0 is omitted; positive/0 is retained as infinity.
--   - `flowSup`: PDF pp.17,20: complete-lattice supremum; empty domain gives 0.
--   - `flowInf`: PDF p.20: complete-lattice infimum; empty domain gives infinity.
--   - `reverseCoolable`: PDF p.21: reverse cooling uses closure of forward reachability from e1.
--   - `coolable`: PDF p.17: the trajectory can depend on the initial simplex point.
--   - `controllableR`: PDF p.21: approximate controllability of the reduced system.
--   - `controllableB`: PDF p.21: approximate controllability of the full density system.
--   - `purelyHamiltonianFace`: PDF p.20, footnote 16: every induced field tangent along the face vanishes on it. The definition is only used together with viability.
--   - `majorizedBy`: PDF pp.22,29: ordinary majorization, via the exact permutation polytope.
--   - `spectrallyMajorizedBy`: PDF p.29: majorization by the spectrum of an actual Hermitian matrix. The existential is only the proof of Hermiticity; its spectrum is computed.
--   - `starClosed`: PDF p.23: star closure of a unital complex matrix algebra.
--   - `hasType`: PDF pp.23-24: type is pinned by an actual unitary Wedderburn decomposition. Each q occurs k times, rather than the product q*k occurring once.
--   - `hasBlocks`: PDF p.24: arbitrary simultaneous reducing blocks, without fullness of each block algebra.
--   - `refines`: PDF p.23, Definition 5.3: the finer vector is aggregated into the coarser one.
--   - `multiplicities`: PDF p.24: multiplicities include the eigenvalue zero.
--   - `smallType`: PDF pp.25-26: the two minimal nontrivial control types.
--   - `zeroSum`: PDF p.12: the full zero-sum tangent space.
--   - `directlyAccessible`: PDF p.12: direct accessibility is the span condition, not convex controllability.
--   - `simplexChart`: PDF p.13, footnote 9: coordinates on the trace-one affine hyperplane.
--   - `genericallyDirectlyAccessible`: PDF p.13, footnote 9: open, dense, and full measure relative to the simplex. Lebesgue measure is transported by an explicit affine coordinate chart.
--   - `nowhereDirectlyAccessible`: PDF p.26: nowhere means at every simplex point, including the boundary.
--   - `densitySpectrum`: PDF p.5: total extension of the Hermitian spectrum; used only with a density hypothesis.
--   - `basisVector`: PDF p.32: the standard unit vector.
--   - `adapted`: PDF p.32: adaptation uses columns of U, not columns of U*.
--   - `shiftedDriftHamiltonian`: PDF p.31, Remark C.4, corrected: printed +i/2 is replaced by 1/(2i)=-i/2. For Vnew=V+cI, (C.4) and K=iH0+sum(V*V)/2 force this sign to preserve G=-L.
--   - `gaugeJumps`: PDF p.31: scalar-shifted jumps.
--   - `pureHamiltonianRHS`: PDF p.10: the complete pure-state Hamiltonian prescription, with arbitrary real a.
--   - `stabilizingBlock`: PDF p.33: sufficient lower-left block condition for a collecting subspace.
--   - `invariantDissipator`: PDF p.27: covariance of the actual non-Hamiltonian superoperator.
--   - `trivialCommutant`: PDF p.19: the commutant of the named drift and jumps is exactly scalar.
--   - `diagonalizableJumps`: PDF p.25: simultaneous special-unitary diagonalization.
--   - `normalCommutingJumps`: PDF p.25: normality and pairwise commutation, both required.
--   - `approximatelyViableOrbits`: PDF p.10: every orbit is viable up to a prescribed finite-horizon error.
--   - `maxEntryNorm`: PDF p.10: maximum absolute matrix entry, not operator norm.
--   - `accessibleB`: PDF pp.12-13: accessibility means nonempty relative interior of the all-time reachable set.
--   - `genericallyAccessibleB`: PDF p.13, footnote 9: full-system genericity in the real trace-one Hermitian affine space. L is an actual linear coordinate isomorphism onto the traceless Hermitian tangent space; its choice does not change open, dense, or measure-zero sets.
-- source:
--   Reachability, Coolability, and Stabilizability of Open Markovian Quantum Systems with Fast Unitary Control, arXiv:2308.00561v1, https://arxiv.org/abs/2308.00561v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity

/-!
Statements from Malvetti et al., arXiv:2308.00561v1.
The sign convention is G = -L. All new definitions are local to this paper.
Only theorem statements contain sorry. Compilation is pending the batch handoff.
-/

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ENNReal NNReal Matrix.Norms.L2Operator
open MeasureTheory Filter

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance 100] LieRing.ofAssociativeRing

namespace QAlgorithms.Papers.Independent.Dependency50.P16

local notation "Mat" => fun n : ℕ => Matrix (Fin n) (Fin n) ℂ

/-- PDF pp.6,10: real matrices for reduced population dynamics and entry bounds. -/
abbrev RMat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

local notation "Vec" => fun n : ℕ => Fin n → ℝ

local notation "Hilbert" => fun n : ℕ => EuclideanSpace ℂ (Fin n)

local notation "Operator" => fun n : ℕ => Module.End ℂ (Mat n)

/-- PDF p.5: the full simplex, without an ordering requirement. -/
def simplex (n : ℕ) : Set (Vec n) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- PDF p.5: the nonincreasing Weyl chamber. -/
def chamber (n : ℕ) : Set (Vec n) := {x | x ∈ simplex n ∧ Antitone x}

/-- PDF p.5: the i-th simplex vertex (indices in Lean start at zero). -/
def vertex {n : ℕ} (i : Fin n) : Vec n := fun j => if j = i then 1 else 0

/-- PDF p.5: the barycenter. The theorems always assume n >= 2. -/
def barycenter (n : ℕ) : Vec n := fun _ => (n : ℝ)⁻¹

/-- PDF p.5: real diagonal embedding. -/
def spectralDiagonal {n : ℕ} (x : Vec n) : Mat n := Matrix.diagonal (fun i => (x i : ℂ))

/-- PDF pp.5,29: the ordered real spectrum, also for non-normalized Hermitian matrices. -/
def orderedSpectrum {n : ℕ} (A : Mat n) (hA : A.IsHermitian) : Vec n :=
  fun i => hA.eigenvalues₀ ⟨i.val, by simpa using i.isLt⟩

/-- PDF p.5: special unitaries are unitaries of determinant one. -/
def specialUnitary {n : ℕ} (U : Mat n) : Prop :=
  U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ U.det = 1

/-- PDF p.30: a two-sided multiplication map. -/
def sandwich {n : ℕ} (A B : Mat n) : Operator n :=
  (LinearMap.mulLeft ℂ A).comp (LinearMap.mulRight ℂ B)

/-- PDF p.30, (C.1): general CP-generator representation; no trace condition. -/
def cpGenerator {n r : ℕ} (K : Mat n) (V : Fin r → Mat n) : Operator n :=
  (∑ k, sandwich (V k) (V k)ᴴ) - LinearMap.mulLeft ℂ K - LinearMap.mulRight ℂ Kᴴ

/-- PDF p.4: arbitrary finite GKSL data, with Hermitian drift. -/
structure LindbladData (n : ℕ) where
  count : ℕ
  jump : Fin count → Mat n
  drift : Mat n
  drift_hermitian : drift.IsHermitian

/-- PDF pp.4,30: K = i H0 + (1/2) sum V*V. -/
def driftK {n : ℕ} (D : LindbladData n) : Mat n :=
  Complex.I • D.drift + (1 / 2 : ℂ) • ∑ k, (D.jump k)ᴴ * D.jump k

/-- PDF p.4: the actual generator G = -L. -/
def gkslGenerator {n : ℕ} (D : LindbladData n) : Operator n := cpGenerator (driftK D) D.jump

/-- PDF p.4: a constant control adds -i[H,X]. -/
def controlledData {n : ℕ} (D : LindbladData n) (H : Mat n) (hH : H.IsHermitian) :
    LindbladData n :=
  { D with drift := D.drift + H, drift_hermitian := D.drift_hermitian.add hH }

/-- PDF p.30: exp(tG), as an exponential of a continuous linear endomorphism. -/
def semigroupEvolution {n : ℕ} (G : Operator n) (t : ℝ) : Mat n →L[ℂ] Mat n :=
  NormedSpace.exp ((t : ℂ) • (LinearMap.toContinuousLinearMap G))

/-- PDF p.30: continuous CP semigroup on nonnegative time. -/
def cpSemigroup {n : ℕ} (Phi : ℝ → Mat n →L[ℂ] Mat n) : Prop :=
  ContinuousOn Phi (Set.Ici 0) ∧ Phi 0 = ContinuousLinearMap.id ℂ (Mat n) ∧
    (∀ s ≥ 0, ∀ t ≥ 0, Phi (s + t) = (Phi s).comp (Phi t)) ∧
    ∀ t ≥ 0, QAlgorithms.Entanglement.IsCompletelyPositive (Phi t).toLinearMap

/-- PDF p.30: quantum dynamical means additionally trace preserving. -/
def quantumSemigroup {n : ℕ} (Phi : ℝ → Mat n →L[ℂ] Mat n) : Prop :=
  cpSemigroup Phi ∧ ∀ t ≥ 0, ∀ X, (Phi t X).trace = X.trace

/-- PDF pp.5-6, (2.3): rates of the finite jump family. -/
def rates {n r : ℕ} (V : Fin r → Mat n) (U : Mat n) : RMat n :=
  fun i j => ∑ k, Complex.normSq ((Uᴴ * V k * U) i j)

/-- PDF p.6, (2.4): column convention for G_U = -L_U. -/
def populationGenerator {n r : ℕ} (V : Fin r → Mat n) (U : Mat n) : RMat n :=
  rates V U - Matrix.diagonal (fun j => ∑ i, rates V U i j)

/-- PDF p.32: induced diagonal action for general CP data; need not be stochastic. -/
def inducedCP {n r : ℕ} (K : Mat n) (V : Fin r → Mat n) (U : Mat n) : RMat n :=
  fun i j => ((Uᴴ * cpGenerator K V (QAlgorithms.conjSuperop U (Matrix.single j j 1)) * U) i i).re

/-- PDF p.6: compact family of induced fields. -/
def fields {n : ℕ} (D : LindbladData n) : Set (RMat n) :=
  {A | ∃ U, specialUnitary U ∧ A = populationGenerator D.jump U}

/-- PDF p.6: achievable derivatives at a vector. -/
def derivatives {n : ℕ} (D : LindbladData n) (x : Vec n) : Set (Vec n) :=
  {v | ∃ A ∈ fields D, v = A *ᵥ x}

/-- PDF p.8: relaxed stabilization, distinct from a single stationary field. -/
def stabilizable {n : ℕ} (D : LindbladData n) (x : Vec n) : Prop :=
  x ∈ simplex n ∧ (0 : Vec n) ∈ convexHull ℝ (derivatives D x)

/-- PDF p.8: strong stabilization by one U. -/
def stronglyStabilizable {n : ℕ} (D : LindbladData n) (x : Vec n) : Prop :=
  x ∈ simplex n ∧ (0 : Vec n) ∈ derivatives D x

/-- PDF p.10: every simplex point is stabilizable. -/
def stabilizableSystem {n : ℕ} (D : LindbladData n) : Prop :=
  ∀ x ∈ simplex n, stabilizable D x

/-- PDF pp.3,6-7: integral trajectories; integrability is explicit on every compact interval.
This gives local absolute continuity, also on an infinite time interval. -/
def integralPath {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Set ℝ) (x v : ℝ → E) : Prop :=
  ∀ t ∈ I, IntervalIntegrable v volume 0 t ∧ x t = x 0 + ∫ s in (0 : ℝ)..t, v s

/-- PDF p.6, Definition 2.1: measurable SU(n) controls, with the actual integral equation. -/
def reducedSolution {n : ℕ} (D : LindbladData n) (I : Set ℝ) (x : ℝ → Vec n) : Prop :=
  (∀ t ∈ I, x t ∈ simplex n) ∧ ∃ U : ℝ → Mat n,
    @Measurable I (Mat n) inferInstance (borel (Mat n)) (fun t : I => U t) ∧ (∀ t ∈ I, specialUnitary (U t)) ∧
    integralPath I x (fun t => populationGenerator D.jump (U t) *ᵥ x t)

/-- PDF p.6, Definition 2.2: the differential inclusion holds almost everywhere. -/
def relaxedSolution {n : ℕ} (D : LindbladData n) (I : Set ℝ) (x : ℝ → Vec n) : Prop :=
  (∀ t ∈ I, x t ∈ simplex n) ∧ ∃ v : ℝ → Vec n,
    integralPath I x v ∧ ∀ᵐ t ∂volume.restrict I, v t ∈ convexHull ℝ (derivatives D (x t))

/-- PDF pp.3-4: a fixed family generating at least su(n) over the reals. -/
structure FullControls (n : ℕ) where
  count : ℕ
  hamiltonian : Fin count → Mat n
  hermitian : ∀ j, (hamiltonian j).IsHermitian
  generating : {X : Mat n | Xᴴ = -X ∧ X.trace = 0} ⊆
    (LieSubalgebra.lieSpan ℝ (Mat n) (Set.range (fun j => Complex.I • hamiltonian j)) : Set (Mat n))

/-- PDF p.3: the unbounded, locally integrable real controls of system (B). -/
def fullSolution {n : ℕ} (D : LindbladData n) (C : FullControls n)
    (I : Set ℝ) (rho : ℝ → Mat n) : Prop :=
  (∀ t ∈ I, QAlgorithms.IsDensityMatrix (rho t)) ∧ ∃ u : Fin C.count → ℝ → ℝ,
    (∀ j, ∀ t ∈ I, IntervalIntegrable (u j) volume 0 t) ∧
    integralPath I rho (fun t => gkslGenerator D (rho t) - Complex.I •
      ((∑ j, (u j t : ℂ) • C.hamiltonian j) * rho t -
        rho t * (∑ j, (u j t : ℂ) • C.hamiltonian j)))

/-- PDF p.7: integrable traceless Hermitian Hamiltonian, with no chosen finite controls. -/
def hamiltonianSolution {n : ℕ} (D : LindbladData n) (T : ℝ)
    (H rho : ℝ → Mat n) : Prop :=
  IntervalIntegrable H volume 0 T ∧
    (∀ t ∈ Set.Icc 0 T, (H t).IsHermitian ∧ (H t).trace = 0) ∧
    (∀ t ∈ Set.Icc 0 T, QAlgorithms.IsDensityMatrix (rho t)) ∧
    integralPath (Set.Icc 0 T) rho (fun t => gkslGenerator D (rho t) -
      Complex.I • (H t * rho t - rho t * H t))

/-- PDF p.13: fixed-time reduced reachability. -/
def reachRAt {n : ℕ} (D : LindbladData n) (x : Vec n) (T : ℝ) : Set (Vec n) :=
  {y | 0 ≤ T ∧ ∃ path, reducedSolution D (Set.Icc 0 T) path ∧ path 0 = x ∧ path T = y}

/-- PDF p.13: fixed-time convexified reachability. -/
def reachCAt {n : ℕ} (D : LindbladData n) (x : Vec n) (T : ℝ) : Set (Vec n) :=
  {y | 0 ≤ T ∧ ∃ path, relaxedSolution D (Set.Icc 0 T) path ∧ path 0 = x ∧ path T = y}

/-- PDF p.13: fixed-time full reachability. -/
def reachBAt {n : ℕ} (D : LindbladData n) (C : FullControls n) (rho : Mat n) (T : ℝ) :
    Set (Mat n) :=
  {sigma | 0 ≤ T ∧ ∃ path, fullSolution D C (Set.Icc 0 T) path ∧ path 0 = rho ∧ path T = sigma}

/-- PDF p.13: all-time reachability includes T=0. -/
def reachR {n : ℕ} (D : LindbladData n) (x : Vec n) : Set (Vec n) :=
  {y | ∃ T, y ∈ reachRAt D x T}

/-- PDF p.13: all-time convexified reachability. -/
def reachC {n : ℕ} (D : LindbladData n) (x : Vec n) : Set (Vec n) :=
  {y | ∃ T, y ∈ reachCAt D x T}

/-- PDF p.13: all-time full reachability. -/
def reachB {n : ℕ} (D : LindbladData n) (C : FullControls n) (rho : Mat n) : Set (Mat n) :=
  {sigma | ∃ T, sigma ∈ reachBAt D C rho T}

/-- PDF p.5: saturation of a spectral set by full unitary orbits. -/
def orbitSaturation {n : ℕ} (S : Set (Vec n)) : Set (Mat n) :=
  {rho | ∃ x ∈ S, ∃ U, specialUnitary U ∧ rho = QAlgorithms.conjSuperop U (spectralDiagonal x)}

/-- PDF p.9: faces are specified by their nonempty coordinate support. -/
structure Face (n : ℕ) where
  support : Finset (Fin n)
  nonempty : support.Nonempty

/-- PDF p.9: the coordinate face itself. -/
def faceSet {n : ℕ} (F : Face n) : Set (Vec n) :=
  {x | x ∈ simplex n ∧ ∀ i ∉ F.support, x i = 0}

/-- PDF p.9, footnote 6: positivity at precisely the coordinates of F. -/
def faceInterior {n : ℕ} (F : Face n) : Set (Vec n) :=
  {x | x ∈ faceSet F ∧ ∀ i ∈ F.support, 0 < x i}

/-- PDF p.9: the linear tangent space to the affine hull of F. -/
def faceTangent {n : ℕ} (F : Face n) : Set (Vec n) :=
  {v | ∑ i, v i = 0 ∧ ∀ i ∉ F.support, v i = 0}

/-- PDF p.9: all-time viability in the convexified system. -/
def viable {n : ℕ} (D : LindbladData n) (S : Set (Vec n)) : Prop :=
  ∀ x ∈ S, ∃ path, relaxedSolution D (Set.Ici 0) path ∧ path 0 = x ∧
    ∀ t ≥ 0, path t ∈ S

/-- PDF p.19: direct reachability requires an initial point outside the face. -/
def directlyReachable {n : ℕ} (D : LindbladData n) (F : Face n) : Prop :=
  ∃ path mu, relaxedSolution D (Set.Ici 0) path ∧ path 0 ∉ faceSet F ∧
    mu ∈ faceInterior F ∧ Tendsto path atTop (nhds mu)

/-- PDF pp.32-33: support is the actual range of the density operator. -/
def densitySupport {n : ℕ} (rho : Mat n) : Submodule ℂ (Hilbert n) := LinearMap.range (Matrix.toEuclideanLin rho)

/-- PDF p.32: matrix of the canonical orthogonal projection. -/
def orthogonalProjector {n : ℕ} (S : Submodule ℂ (Hilbert n)) : Mat n :=
  fun i j => (S.starProjection (WithLp.toLp 2 (fun k => if k = j then (1 : ℂ) else 0))) i

/-- PDF p.32: invariance of a linear subspace, including the zero subspace. -/
def invariant {n : ℕ} (A : Set (Mat n)) (S : Submodule ℂ (Hilbert n)) : Prop :=
  ∀ X ∈ A, ∀ v ∈ S, QAlgorithms.act X v ∈ S

/-- PDF p.31: unital associative relaxation algebra. -/
def relaxationAlgebra {n r : ℕ} (V : Fin r → Mat n) : Subalgebra ℂ (Mat n) :=
  Algebra.adjoin ℂ (Set.range V)

/-- PDF p.31: extended relaxation algebra includes K, not just the drift. -/
def extendedAlgebra {n r : ℕ} (K : Mat n) (V : Fin r → Mat n) : Subalgebra ℂ (Mat n) :=
  Algebra.adjoin ℂ (insert K (Set.range V))

/-- PDF p.34: the extended star algebra includes the drift and all adjoint jumps. -/
def extendedStarAlgebra {n : ℕ} (D : LindbladData n) : Subalgebra ℂ (Mat n) :=
  Algebra.adjoin ℂ (insert D.drift (Set.range D.jump ∪ Set.range (fun k => (D.jump k)ᴴ)))

/-- PDF p.32: lazy subspaces are nonzero common invariant subspaces of the jumps. -/
def lazy {n r : ℕ} (V : Fin r → Mat n) (S : Submodule ℂ (Hilbert n)) : Prop :=
  S ≠ ⊥ ∧ invariant (Set.range V) S

/-- PDF pp.32-33, footnote 23: collecting lattice with the zero subspace included. -/
def collecting0 {n r : ℕ} (K : Mat n) (V : Fin r → Mat n)
    (S : Submodule ℂ (Hilbert n)) : Prop := invariant (extendedAlgebra K V : Set (Mat n)) S

/-- PDF pp.32-33: named collecting subspaces additionally are nonzero. -/
def collecting {n r : ℕ} (K : Mat n) (V : Fin r → Mat n)
    (S : Submodule ℂ (Hilbert n)) : Prop := S ≠ ⊥ ∧ collecting0 K V S

/-- PDF p.34: enclosure means reducing all jumps and the original drift. -/
def enclosure {n : ℕ} (D : LindbladData n) (S : Submodule ℂ (Hilbert n)) : Prop :=
  (∀ k, orthogonalProjector S * D.jump k = D.jump k * orthogonalProjector S) ∧
    orthogonalProjector S * D.drift = D.drift * orthogonalProjector S

/-- PDF pp.10,33: scalar jump compressions mean purely Hamiltonian dissipation on S. -/
def scalarOn {n : ℕ} (A : Mat n) (S : Submodule ℂ (Hilbert n)) : Prop :=
  ∃ c : ℂ, ∀ v ∈ S, QAlgorithms.act A v = c • v

/-- PDF p.33: nonzero minimal element of the collecting-subspace lattice. -/
def minimalCollecting {n : ℕ} (D : LindbladData n) (S : Submodule ℂ (Hilbert n)) : Prop :=
  collecting (driftK D) D.jump S ∧
    ∀ T, collecting (driftK D) D.jump T → T ≤ S → T = S

/-- PDF p.33: a stationary normalized density. -/
def stationary {n : ℕ} (D : LindbladData n) (rho : Mat n) : Prop :=
  QAlgorithms.IsDensityMatrix rho ∧ gkslGenerator D rho = 0

/-- PDF p.33, footnote 25: extremality among all stationary densities. -/
def extremalStationary {n : ℕ} (D : LindbladData n) (rho : Mat n) : Prop :=
  stationary D rho ∧ ∀ sigma tau, stationary D sigma → stationary D tau →
    ∀ a : ℝ, 0 < a → a < 1 → rho = a • sigma + (1 - a) • tau → sigma = rho ∧ tau = rho

/-- PDF p.33: unique fixed density with full support S, among densities supported in S. -/
def uniqueStationaryOn {n : ℕ} (D : LindbladData n) (S : Submodule ℂ (Hilbert n)) : Prop :=
  ∃ rho, stationary D rho ∧ densitySupport rho = S ∧
    ∀ sigma, stationary D sigma → densitySupport sigma ≤ S → sigma = rho

/-- PDF p.17, footnote 13: every initial density converges to this fixed density. -/
def attractive {n : ℕ} (D : LindbladData n) (rho : Mat n) : Prop :=
  stationary D rho ∧ ∀ sigma, QAlgorithms.IsDensityMatrix sigma →
    Tendsto (fun t => semigroupEvolution (gkslGenerator D) t sigma) atTop (nhds rho)

/-- PDF p.33: decay is tested on every normalized initial density. -/
def decaying {n : ℕ} (D : LindbladData n) (S : Submodule ℂ (Hilbert n)) : Prop :=
  ∀ rho, QAlgorithms.IsDensityMatrix rho →
    Tendsto (fun t => (orthogonalProjector S * semigroupEvolution (gkslGenerator D) t rho).trace) atTop (nhds 0)

/-- PDF p.33: orthogonal complement of a decaying subspace. -/
def asymptotic {n : ℕ} (D : LindbladData n) (S : Submodule ℂ (Hilbert n)) : Prop :=
  decaying D Sᗮ

/-- PDF p.33: the maximal decaying subspace is constructed by taking the supremum. -/
def maximalDecay {n : ℕ} (D : LindbladData n) : Submodule ℂ (Hilbert n) :=
  sSup {S | decaying D S}

/-- PDF p.33: minimal asymptotic space, constructed from the decaying family. -/
def minimalAsymptotic {n : ℕ} (D : LindbladData n) : Submodule ℂ (Hilbert n) :=
  (maximalDecay D)ᗮ

/-- PDF pp.10,17: common normalized right eigenvector. -/
def commonEigenvector {n r : ℕ} (V : Fin r → Mat n) (psi : Hilbert n) : Prop :=
  ‖psi‖ = 1 ∧ ∀ k, ∃ c : ℂ, QAlgorithms.act (V k) psi = c • psi

/-- PDF p.14: every common right eigenvector is also a common left eigenvector.
Normalization loses no nonzero eigenvector in finite dimension. -/
def eigenvectorObstruction {n r : ℕ} (V : Fin r → Mat n) : Prop :=
  ∀ psi, commonEigenvector V psi → commonEigenvector (fun k => (V k)ᴴ) psi

/-- PDF pp.10,12: one invertible basis triangularizes the entire set. -/
def triangularizable {n : ℕ} (A : Set (Mat n)) : Prop :=
  ∃ B C : Mat n, B * C = 1 ∧ C * B = 1 ∧ ∀ X ∈ A, (C * X * B).IsUpperTriangular

/-- PDF p.12, footnote 8: one unitary basis for the entire set. -/
def unitarilyTriangularizable {n : ℕ} (A : Set (Mat n)) : Prop :=
  ∃ U : Mat n, U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
    ∀ X ∈ A, (Uᴴ * X * U).IsUpperTriangular

/-- PDF pp.10,12: the generated complex commutator Lie algebra is solvable. -/
def solvableGenerated {n : ℕ} (A : Set (Mat n)) : Prop :=
  LieAlgebra.IsSolvable (LieSubalgebra.lieSpan ℂ (Mat n) A)

/-- PDF p.4: quantify all actual representations of the same generator. -/
def someRepresentation {n : ℕ} (D : LindbladData n) (P : LindbladData n → Prop) : Prop :=
  ∃ E, gkslGenerator E = gkslGenerator D ∧ P E

/-- PDF p.4: representation independence is expressed without any Kraus-rank restriction. -/
def everyRepresentation {n : ℕ} (D : LindbladData n) (P : LindbladData n → Prop) : Prop :=
  ∀ E, gkslGenerator E = gkslGenerator D → P E

/-- PDF p.4: unitality concerns the generator, rather than one jump. -/
def unital {n : ℕ} (D : LindbladData n) : Prop := gkslGenerator D 1 = 0

/-- PDF p.25: purely Hamiltonian generators, allowing an arbitrary Hermitian Hamiltonian. -/
def purelyHamiltonian {n : ℕ} (D : LindbladData n) : Prop :=
  ∃ H : Mat n, H.IsHermitian ∧ ∀ X, gkslGenerator D X = -Complex.I • (H * X - X * H)

/-- PDF pp.18,20: population in the first d coordinates. -/
def partialPopulation {n : ℕ} (d : ℕ) (x : Vec n) : ℝ := ∑ i : Fin n, if i.val < d then x i else 0

/-- PDF p.17: total inflow across the d-dimensional cut. -/
def inflow {n r : ℕ} (V : Fin r → Mat n) (d : ℕ) (U : Mat n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i.val < d ∧ d ≤ j.val then rates V U i j else 0

/-- PDF p.17: total outflow across the same cut. -/
def outflow {n r : ℕ} (V : Fin r → Mat n) (d : ℕ) (U : Mat n) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if d ≤ i.val ∧ j.val < d then rates V U i j else 0

/-- PDF p.17: exactly 0/0 is omitted; positive/0 is retained as infinity. -/
def flowValues {n r : ℕ} (V : Fin r → Mat n) (d : ℕ) : Set ℝ≥0∞ :=
  {z | ∃ U, specialUnitary U ∧ 0 < inflow V d U + outflow V d U ∧
    z = ENNReal.ofReal (inflow V d U) / ENNReal.ofReal (outflow V d U)}

/-- PDF pp.17,20: complete-lattice supremum; empty domain gives 0. -/
def flowSup {n r : ℕ} (V : Fin r → Mat n) (d : ℕ) : ℝ≥0∞ := sSup (flowValues V d)

/-- PDF p.20: complete-lattice infimum; empty domain gives infinity. -/
def flowInf {n r : ℕ} (V : Fin r → Mat n) (d : ℕ) : ℝ≥0∞ := sInf (flowValues V d)

/-- PDF p.21: reverse cooling uses closure of forward reachability from e1. -/
def reverseCoolable {n : ℕ} (D : LindbladData n) (i : Fin n) : Prop :=
  chamber n ⊆ closure (reachR D (vertex i))

/-- PDF p.17: the trajectory can depend on the initial simplex point. -/
def coolable {n : ℕ} (D : LindbladData n) (i : Fin n) : Prop :=
  ∀ x ∈ simplex n, ∃ path, reducedSolution D (Set.Ici 0) path ∧ path 0 = x ∧
    Tendsto path atTop (nhds (vertex i))

/-- PDF p.21: approximate controllability of the reduced system. -/
def controllableR {n : ℕ} (D : LindbladData n) : Prop :=
  ∀ x ∈ simplex n, simplex n ⊆ closure (reachR D x)

/-- PDF p.21: approximate controllability of the full density system. -/
def controllableB {n : ℕ} (D : LindbladData n) (C : FullControls n) : Prop :=
  ∀ rho, QAlgorithms.IsDensityMatrix rho →
    {sigma | QAlgorithms.IsDensityMatrix sigma} ⊆ closure (reachB D C rho)

/-- PDF p.20, footnote 16: every induced field tangent along the face vanishes on it.
The definition is only used together with viability. -/
def purelyHamiltonianFace {n : ℕ} (D : LindbladData n) (F : Face n) : Prop :=
  ∀ A ∈ fields D, (∀ x ∈ faceSet F, A *ᵥ x ∈ faceTangent F) →
    ∀ x ∈ faceSet F, A *ᵥ x = 0

/-- PDF pp.22,29: ordinary majorization, via the exact permutation polytope. -/
def majorizedBy {n : ℕ} (x y : Vec n) : Prop :=
  x ∈ convexHull ℝ {z | ∃ p : Equiv.Perm (Fin n), z = fun i => y (p i)}

/-- PDF p.29: majorization by the spectrum of an actual Hermitian matrix.
The existential is only the proof of Hermiticity; its spectrum is computed. -/
def spectrallyMajorizedBy {n : ℕ} (x : Vec n) (A : Mat n) : Prop :=
  ∃ hA : A.IsHermitian, majorizedBy x (orderedSpectrum A hA)

/-- PDF p.23: star closure of a unital complex matrix algebra. -/
def starClosed {n : ℕ} (A : Subalgebra ℂ (Mat n)) : Prop := ∀ X ∈ A, Xᴴ ∈ A

/-- PDF pp.23-24: type is pinned by an actual unitary Wedderburn decomposition.
Each q occurs k times, rather than the product q*k occurring once. -/
def hasType {n : ℕ} (A : Subalgebra ℂ (Mat n)) (tau : Multiset ℕ) : Prop :=
  ∃ (m : ℕ) (q k : Fin m → ℕ)
    (e : Fin n ≃ (Σ a : Fin m, Fin (q a) × Fin (k a))) (U : Mat n),
    (∀ a, 0 < q a ∧ 0 < k a) ∧ U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
    tau = ∑ a, Multiset.replicate (k a) (q a) ∧
    ∀ X : Mat n, X ∈ A ↔ ∃ B : ∀ a, Matrix (Fin (q a)) (Fin (q a)) ℂ,
      U * X * Uᴴ = Matrix.reindex e.symm e.symm
        (Matrix.blockDiagonal' (fun a => Matrix.kronecker (B a) (1 : Matrix (Fin (k a)) (Fin (k a)) ℂ)))

/-- PDF p.24: arbitrary simultaneous reducing blocks, without fullness of each block algebra. -/
def hasBlocks {n : ℕ} (A : Subalgebra ℂ (Mat n)) (w : Multiset ℕ) : Prop :=
  ∃ (m : ℕ) (q : Fin m → ℕ) (e : Fin n ≃ (Σ a : Fin m, Fin (q a))) (U : Mat n),
    (∀ a, 0 < q a) ∧ U ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
    w = Multiset.ofList (List.ofFn q) ∧ ∀ X ∈ A,
      ∃ B : ∀ a, Matrix (Fin (q a)) (Fin (q a)) ℂ,
        U * X * Uᴴ = Matrix.reindex e.symm e.symm (Matrix.blockDiagonal' B)

/-- PDF p.23, Definition 5.3: the finer vector is aggregated into the coarser one. -/
def refines (v w : Multiset ℕ) : Prop :=
  ∃ (k l : ℕ) (a : Fin k → ℕ) (b : Fin l → ℕ) (f : Fin k → Fin l),
    Multiset.ofList (List.ofFn a) = v ∧ Multiset.ofList (List.ofFn b) = w ∧
    ∀ j, ∑ i : Fin k, (if f i = j then a i else 0) = b j

/-- PDF p.24: multiplicities include the eigenvalue zero. -/
def multiplicities {n : ℕ} (x : Vec n) : Multiset ℕ :=
  Multiset.ofList ((Finset.univ.image x).toList.map (fun a => (Finset.univ.filter (fun i => x i = a)).card))

/-- PDF pp.25-26: the two minimal nontrivial control types. -/
def smallType {n : ℕ} (D : LindbladData n) : Prop :=
  hasType (relaxationAlgebra D.jump) (Multiset.replicate n 1) ∨
    hasType (relaxationAlgebra D.jump) (2 ::ₘ Multiset.replicate (n - 2) 1)

/-- PDF p.12: the full zero-sum tangent space. -/
def zeroSum (n : ℕ) : Submodule ℝ (Vec n) :=
  LinearMap.ker
    ({ toFun := fun x => ∑ i, x i
       map_add' := by intros; simp [Finset.sum_add_distrib]
       map_smul' := by intros; simp [Finset.mul_sum] } : Vec n →ₗ[ℝ] ℝ)

/-- PDF p.12: direct accessibility is the span condition, not convex controllability. -/
def directlyAccessible {n : ℕ} (D : LindbladData n) (x : Vec n) : Prop :=
  Submodule.span ℝ (derivatives D x) = zeroSum n

/-- PDF p.13, footnote 9: coordinates on the trace-one affine hyperplane. -/
def simplexChart (n : ℕ) (x : Fin (n - 1) → ℝ) : Vec n :=
  fun i => if h : i.val < n - 1 then x ⟨i.val, h⟩ else 1 - ∑ j, x j

/-- PDF p.13, footnote 9: open, dense, and full measure relative to the simplex.
Lebesgue measure is transported by an explicit affine coordinate chart. -/
def genericallyDirectlyAccessible {n : ℕ} (D : LindbladData n) : Prop :=
  ∃ S : Set {x : Vec n // x ∈ simplex n}, IsOpen S ∧ Dense S ∧
    (∀ x ∈ S, directlyAccessible D x.val) ∧
    volume {y : Fin (n - 1) → ℝ | simplexChart n y ∈ simplex n ∧
      ¬∃ h : simplexChart n y ∈ simplex n, (⟨simplexChart n y, h⟩ : {x // x ∈ simplex n}) ∈ S} = 0

/-- PDF p.26: nowhere means at every simplex point, including the boundary. -/
def nowhereDirectlyAccessible {n : ℕ} (D : LindbladData n) : Prop :=
  ∀ x ∈ simplex n, ¬directlyAccessible D x

/-- Sanity: with no jumps and K=0, the represented generator is zero. -/
example {n : ℕ} : cpGenerator (0 : Mat n) (fun k : Fin 0 => Fin.elim0 k) = 0 := by
  simp [cpGenerator]

/-- Sanity: a scalar pure zero field gives no rates for an empty jump family. -/
example {n : ℕ} (U : Mat n) : rates (fun k : Fin 0 => (Fin.elim0 k : Mat n)) U = 0 := by
  ext i j
  simp [rates]

/-- Sanity: scalar-noise ratio domain is empty in the zero-jump case. -/
example {n d : ℕ} : flowSup (fun k : Fin 0 => (Fin.elim0 k : Mat n)) d = 0 := by
  simp [flowSup, flowValues, inflow, outflow, rates]

/-- Sanity: zero eigenvalues contribute their full multiplicity. -/
example : multiplicities (fun _ : Fin 2 => (0 : ℝ)) = {2} := by
  norm_num [multiplicities, Finset.univ_fin2]

/-- PDF p.5: total extension of the Hermitian spectrum; used only with a density hypothesis. -/
def densitySpectrum {n : ℕ} (rho : Mat n) : Vec n :=
  if h : rho.IsHermitian then orderedSpectrum rho h else 0

/-- PDF p.32: the standard unit vector. -/
def basisVector {n : ℕ} (j : Fin n) : Hilbert n :=
  WithLp.toLp 2 (fun i => if i = j then (1 : ℂ) else 0)

/-- PDF p.32: adaptation uses columns of U, not columns of U*. -/
def adapted {n : ℕ} (U : Mat n) (S : Submodule ℂ (Hilbert n)) : Prop :=
  Submodule.span ℂ {v | ∃ j : Fin n, j.val < Module.finrank ℂ S ∧
    v = QAlgorithms.act U (basisVector j)} = S

/-- PDF p.31, Remark C.4, corrected: printed +i/2 is replaced by 1/(2i)=-i/2.
For Vnew=V+cI, (C.4) and K=iH0+sum(V*V)/2 force this sign to preserve G=-L. -/
def shiftedDriftHamiltonian {n : ℕ} (D : LindbladData n) (c : Fin D.count → ℂ) (a : ℝ) : Mat n :=
  D.drift + (1 / (2 * Complex.I)) • ∑ k, (conj (c k) • D.jump k - c k • (D.jump k)ᴴ) +
    (a : ℂ) • (1 : Mat n)

/-- PDF p.31: scalar-shifted jumps. -/
def gaugeJumps {n : ℕ} (D : LindbladData n) (c : Fin D.count → ℂ) : Fin D.count → Mat n :=
  fun k => D.jump k + c k • (1 : Mat n)

/-- PDF p.10: the complete pure-state Hamiltonian prescription, with arbitrary real a. -/
def pureHamiltonianRHS {n : ℕ} (D : LindbladData n) (z : Fin D.count → ℂ) (a : ℝ) : Mat n :=
  -(D.drift + ((a : ℂ) - (1 / (2 * Complex.I)) * ∑ k, (Complex.normSq (z k) : ℂ)) •
    (1 : Mat n) + (1 / (2 * Complex.I)) • ∑ k, (D.jump k)ᴴ * D.jump k)

/-- PDF p.33: sufficient lower-left block condition for a collecting subspace. -/
def stabilizingBlock {n : ℕ} (D : LindbladData n) (S : Submodule ℂ (Hilbert n)) (H : Mat n) : Prop :=
  (1 - orthogonalProjector S) * H * orthogonalProjector S =
    -(1 - orthogonalProjector S) * (D.drift + (1 / (2 * Complex.I)) •
      ∑ k, (D.jump k)ᴴ * D.jump k) * orthogonalProjector S

/-- PDF p.27: covariance of the actual non-Hamiltonian superoperator. -/
def invariantDissipator {n : ℕ} (D : LindbladData n) : Prop :=
  ∀ U : Mat n, U ∈ Matrix.unitaryGroup (Fin n) ℂ → ∀ X : Mat n,
    cpGenerator ((1 / 2 : ℂ) • ∑ k, (D.jump k)ᴴ * D.jump k) D.jump (QAlgorithms.conjSuperop U X) =
      QAlgorithms.conjSuperop U (cpGenerator ((1 / 2 : ℂ) • ∑ k, (D.jump k)ᴴ * D.jump k) D.jump X)

/-- PDF p.19: the commutant of the named drift and jumps is exactly scalar. -/
def trivialCommutant {n : ℕ} (D : LindbladData n) : Prop :=
  ∀ X : Mat n, (X * D.drift = D.drift * X) →
    (∀ k, X * D.jump k = D.jump k * X) → ∃ c : ℂ, X = c • (1 : Mat n)

/-- PDF p.25: simultaneous special-unitary diagonalization. -/
def diagonalizableJumps {n : ℕ} (D : LindbladData n) : Prop :=
  ∃ U : Mat n, specialUnitary U ∧ ∀ k, ∀ i j, i ≠ j → (Uᴴ * D.jump k * U) i j = 0

/-- PDF p.25: normality and pairwise commutation, both required. -/
def normalCommutingJumps {n : ℕ} (D : LindbladData n) : Prop :=
  (∀ k, D.jump k * (D.jump k)ᴴ = (D.jump k)ᴴ * D.jump k) ∧
    ∀ j k, D.jump j * D.jump k = D.jump k * D.jump j

/-- PDF p.10: every orbit is viable up to a prescribed finite-horizon error. -/
def approximatelyViableOrbits {n : ℕ} (D : LindbladData n) (C : FullControls n) : Prop :=
  ∀ rho, QAlgorithms.IsDensityMatrix rho → ∀ T : ℝ, 0 ≤ T → ∀ eps : ℝ, 0 < eps →
    ∃ path, fullSolution D C (Set.Icc 0 T) path ∧ path 0 = rho ∧
      ∀ t ∈ Set.Icc 0 T, ∃ U : Mat n, specialUnitary U ∧
        ‖path t - QAlgorithms.conjSuperop U rho‖ ≤ eps

/-- PDF p.10: maximum absolute matrix entry, not operator norm. -/
def maxEntryNorm {n : ℕ} (A : RMat n) : ℝ :=
  ((Finset.univ.sup (fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊) : ℝ≥0) : ℝ)

/-- PDF pp.12-13: accessibility means nonempty relative interior of the all-time reachable set. -/
def accessibleB {n : ℕ} (D : LindbladData n) (C : FullControls n) (rho : Mat n) : Prop :=
  (interior {sigma : {X : Mat n // QAlgorithms.IsDensityMatrix X} |
    sigma.val ∈ reachB D C rho}).Nonempty

/-- PDF p.13, footnote 9: full-system genericity in the real trace-one Hermitian affine space.
L is an actual linear coordinate isomorphism onto the traceless Hermitian tangent space;
its choice does not change open, dense, or measure-zero sets. -/
def genericallyAccessibleB {n : ℕ} (D : LindbladData n) (C : FullControls n) : Prop :=
  ∃ L : (Fin (n * n - 1) → ℝ) →ₗ[ℝ] Mat n,
    Function.Injective L ∧ Set.range L = {X | X.IsHermitian ∧ X.trace = 0} ∧
    ∃ S : Set {X : Mat n // QAlgorithms.IsDensityMatrix X},
      IsOpen S ∧ Dense S ∧ (∀ rho ∈ S, accessibleB D C rho.val) ∧
      volume {y : Fin (n * n - 1) → ℝ |
        QAlgorithms.IsDensityMatrix (L y + (1 / (n : ℂ)) • (1 : Mat n)) ∧
        ¬∃ h : QAlgorithms.IsDensityMatrix (L y + (1 / (n : ℂ)) • (1 : Mat n)),
          (⟨L y + (1 / (n : ℂ)) • (1 : Mat n), h⟩ : {X // QAlgorithms.IsDensityMatrix X}) ∈ S} = 0

/-- Sanity: the reused action is the standard Euclidean matrix action. -/
example {n : ℕ} (A : Mat n) (v : Hilbert n) :
    QAlgorithms.act A v = Matrix.toEuclideanLin A v := by
  rfl

/-- Sanity: the reused conjugation has the source's U X U* convention. -/
example {n : ℕ} (U X : Mat n) : QAlgorithms.conjSuperop U X = U * X * Uᴴ := by
  rfl

/-! ## Source theorem statements -/

end QAlgorithms.Papers.Independent.Dependency50.P16


