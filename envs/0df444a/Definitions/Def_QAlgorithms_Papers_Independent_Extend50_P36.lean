-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36
-- name    : QAlgorithms_Papers_Independent_Extend50_P36
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T13:50:21.597855+00:00
-- url     : https://prove2.me/theorems/06e5dea5-a2aa-470d-9874-52cf3d12e80f
-- title:
--   Definitions for Compatible quantum correlations: on extension problems for Werner and isotropic states
-- statement:
--   The objects the formalized statements of *Compatible quantum correlations: on extension problems for Werner and isotropic states* (arXiv:1305.1342) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `JoinsTwo`: Definition II.1, PDF p.3, two overlapping bipartite marginals.
--   - `JoinableTwo`: Definition II.1, PDF p.3. Positivity and normalization belong to the joining state.
--   - `JoinableThree`: PDF p.8: three specified pair marginals, ordered AB,AC,BC.
--   - `SharingIndex`: Definition II.4, PDF pp.4–5: the actual sharing register.
--   - `sharingMarginal`: Eq.(3), PDF p.5: trace out all sites except the selected left/right pair. The row constraint counts each configuration of the traced sites exactly once.
--   - `Shares`: Eq.(3), PDF p.5: all mn marginals equal the same bipartite operator.
--   - `Sharable`: Definition II.4, PDF pp.4–5; statements impose positive sharing counts.
--   - `ArbitrarilySharable`: PDF pp.5–6: a separate finite extension for every positive pair of counts.
--   - `fullyMixed`: PDF p.5: the completely mixed operator on a finite register.
--   - `convexStateMixture`: PDF pp.3,5: a convex combination with weight t on the first operator.
--   - `localConjugate`: Eq.(4), PDF p.5: conjugation by a product of local matrices. The sharing theorems supply unitary factors; matrix arguments avoid coupling the operation to a particular decidable-equality instance of a bundled unitary group.
--   - `quditSwapOperator`: PDF p.6: the swap operator on two d-dimensional factors.
--   - `entangledEffect`: PDF p.6: d times the maximally entangled projector, the partially transposed swap.
--   - `wernerSwapState`: Sec.III A, PDF p.6, swap-expectation parametrization. Physical range [-1,1].
--   - `isotropicOverlapState`: Sec.III A, PDF p.6: phi = d times singlet fraction. Physical range [0,d].
--   - `wernerConcurrence`: Eq.(5), PDF p.6, including the separable branch.
--   - `isotropicConcurrence`: Eq.(6), PDF p.6, including the separable branch.
--   - `wernerCubeRoot`: Eq.(17), PDF p.8: primitive cube root with positive imaginary part.
--   - `wernerRegion`: Eqs.(15)–(17), PDF p.8. Coordinates are AB,AC,BC.
--   - `mixedConePhase`: Eq.(21), PDF p.8: exp(i theta) as the source's explicit radicals.
--   - `mixedCone`: Eqs.(20)–(21), PDF p.8: the cone inside its physical parameter box.
--   - `mixedRegion`: Theorem III.2, PDF p.8: higher dimensions add precisely the vertex (0,0,-1).
--   - `isotropicEllipse`: Eq.(23), PDF p.9: ellipse circumference; its hull with the origin is used below.
--   - `IsotropicStarJoinable`: Theorem III.6, PDF p.11: a central site and n distinct outer marginals.
--   - `classicalAgreementLaw`: Eq.(8), PDF p.7: classical analogue with agreement probability alpha.
--   - `ClassicalTripleJoinable`: PDF pp.7–8: actual classical joining law, ordered AB,AC,BC.
--   - `classicalVertices`: PDF p.7: four always available vertices and the all-disagree vertex when d >= 3.
--   - `fullAntisymmetricVector`: Eq.(7), PDF p.6: fully antisymmetric normalized d-partite amplitude. Zero-based coordinates replace the source's labels 1,...,d.
--   - `pairMarginal`: PDF pp.6–7: arbitrary pair reduction on a homogeneous tensor register.
--   - `cqWitness`: PDF pp.3–4: explicit CQ witnesses in the X and Z bases, as (I+P⊗P)/4.
--   - `IsClassicalQuantum`: PDF p.4: classical on the first subsystem in some orthonormal basis.
--   - `qubitSharingWitness`: Proposition IV.1, PDF p.12: the specified qubit counterexample.
--   - `qubitJoiningWitness`: Proposition IV.1, PDF p.13: the normalized three-qubit pure joining state.
--   - `pseudoPure`: PDF p.13: pseudo-pure mixture, weight t on a normalized maximally entangled vector.
--   - `NeighborhoodConfiguration`: General neighborhoods of Sec.II A, PDF pp.2–3.
--   - `assembleNeighborhood`: PDF p.3: combine a neighborhood configuration and its tensor complement.
--   - `neighborhoodMarginal`: Eq.(1), PDF p.3: explicit partial trace for an arbitrary neighborhood.
--   - `JoiningList`: Definition II.1, PDF p.3: the full joining fiber of any finite neighborhood list.
--   - `collectiveTensorOperator`: PDF pp.8,12: the tensor power of a matrix, with an optional conjugate on site zero.
--   - `collectiveTriple`: Eqs.(13),(18), PDF p.8: U⊗U⊗U or conjugate(U)⊗U⊗U in A,B,C order.
--   - `tripleTwirl`: Eqs.(13),(18), PDF p.8: the normalized Haar twirl, as a matrix-valued integral.
--   - `pairTwirl`: Corollary IV.2, PDF p.13: the two-factor Haar twirl, with conjugation on A only.
--   - `diagonalAxisRotation`: PDF p.9: the explicit rotation about the diagonal line, with fixed origin.
--   - `tableFour`: Table I(c), PDF p.12: uncomputed entries return none, never a zero threshold.
--   - `triplePerm`: Appendix A, PDF p.14: the three actual transpositions and the oriented 3-cycle.
--   - `transposeA`: Appendix A, PDF p.14: transpose on factor A, without changing B,C.
--   - `wernerBasis`: Eqs.(A1)–(A2), PDF p.14; coordinates ordered +,-,0,1,2,3.
--   - `mixedBasis`: Eqs.(A5)–(A6), PDF p.14; no unit Hilbert–Schmidt normalization is asserted.
--   - `coordinateOperator`: Eqs.(A3),(A7), PDF p.14: actual density reconstruction, with the absent antisymmetric sector explicitly omitted at d=2.
--   - `PhysicalCoordinates`: Eqs.(A4),(A7), PDF pp.14–15: trace one, positivity ball, and absent sector.
--   - `tripleSymmetryCoordinates`: Appendix A, PDF p.14: coordinates computed from the physical operator.
--   - `TripleInvariant`: Eqs.(14),(19), PDF p.8: the concrete collective-invariant subspace.
--   - `CoordinateCharacterization`: Appendix A's two full physical coordinate characterizations, PDF pp.14–15.
--   - `crossSwap`: Appendix B, PDF p.17: the actual cross-group swap matrix.
--   - `sharingHamiltonian`: Appendix B, PDF p.17: minus the average of the mn cross-group swaps.
--   - `realEigenvalues`: Appendix B, PDF p.17: real eigenvalues, defined by actual nonzero eigenvectors.
--   - `maximalRealEigenvalue`: Appendix B, PDF p.17: maximum of the nonempty finite real spectrum of a Hermitian operator on the nonempty physical register. Only that domain is used.
--   - `fullEigenkernelProjector`: Appendix B, PDF p.17: the orthogonal projector onto the entire eigenspace.
--   - `extremalSharingState`: Appendix B, PDF p.17: the whole top-eigenspace projector divided by its trace.
--   - `embeddedQuditGenerator`: Eq.(B1), PDF p.17: insert a local generator on one site of a tensor register.
--   - `collectiveCasimir`: Eq.(B1), PDF p.17: group Casimir embedded in the same full register. left/right flags select L, R, or their union.
--   - `NormalizedGenerators`: Eq.(B1)'s normalization, PDF p.17: Hermitian traceless generators with Tr(lambda_alpha lambda_beta)=delta_alpha,beta, spanning by their full dimension.
--   - `youngColumnSquareSum`: Eq.(B3), PDF p.18: sum of squared column heights, over all possibly nonempty columns.
--   - `rowSquares`: Eq.(B3), PDF p.18: sum of squared row lengths, with zero padding up to d.
--   - `youngEigenvalue`: Eq.(B3), PDF p.18: scalar prescribed by three Young diagrams.
--   - `youngSector`: PDF pp.17–18: actual simultaneous physical isotypic sector. The accepted character idempotents are constructed independently of H and of Eq.(B3).
-- source:
--   Compatible quantum correlations: on extension problems for Werner and isotropic states, arXiv:1305.1342v3, https://arxiv.org/abs/1305.1342v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21

/-! Statements and paper-local physical definitions for Johnson and Viola,
*Compatible quantum correlations: on extension problems for Werner and isotropic states*,
arXiv:1305.1342v3. PDF page numbers are used throughout.
-/

noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise
open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.
open QAlgorithms.Papers.Independent.Information100.P21 (Op)

/-- Definition II.1, PDF p.3, two overlapping bipartite marginals. -/
def JoinsTwo {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (X : Op (I × J × K)) (A : Op (I × J)) (B : Op (I × K)) : Prop :=
  IsDensityMatrix X ∧ (idTensorSuperop traceRight) X = A ∧ (idTensorSuperop traceLeft) X = B

/-- Definition II.1, PDF p.3. Positivity and normalization belong to the joining state. -/
def JoinableTwo {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (A : Op (I × J)) (B : Op (I × K)) : Prop := ∃ X, JoinsTwo X A B

/-- PDF p.8: three specified pair marginals, ordered AB,AC,BC. -/
def JoinableThree {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (A : Op (I × J)) (B : Op (I × K)) (C : Op (J × K)) : Prop :=
  ∃ X, JoinsTwo X A B ∧ traceLeft X = C

/-- Definition II.4, PDF pp.4–5: the actual sharing register. -/
abbrev SharingIndex (I J : Type*) (m n : ℕ) := (Fin m → I) × (Fin n → J)

/-- Eq.(3), PDF p.5: trace out all sites except the selected left/right pair.
The row constraint counts each configuration of the traced sites exactly once. -/
def sharingMarginal {I J : Type*} [Fintype I] [Fintype J] {m n : ℕ}
    (X : Op (SharingIndex I J m n)) (i : Fin m) (j : Fin n) : Op (I × J) :=
  fun a b => ∑ x : Fin m → I, ∑ y : Fin n → J,
    if x i = a.1 ∧ y j = a.2 then
      X (x,y) (Function.update x i b.1,Function.update y j b.2) else 0

/-- Eq.(3), PDF p.5: all mn marginals equal the same bipartite operator. -/
def Shares {I J : Type*} [Fintype I] [Fintype J] {m n : ℕ}
    (X : Op (SharingIndex I J m n)) (rho : Op (I × J)) : Prop :=
  IsDensityMatrix X ∧ ∀ i : Fin m, ∀ j : Fin n, sharingMarginal X i j = rho

/-- Definition II.4, PDF pp.4–5; statements impose positive sharing counts. -/
def Sharable {I J : Type*} [Fintype I] [Fintype J]
    (m n : ℕ) (rho : Op (I × J)) : Prop :=
  ∃ X : Op (SharingIndex I J m n), Shares (m := m) (n := n) X rho

/-- PDF pp.5–6: a separate finite extension for every positive pair of counts. -/
def ArbitrarilySharable {I J : Type*} [Fintype I] [Fintype J]
    (rho : Op (I × J)) : Prop := ∀ m n : ℕ, 0 < m → 0 < n → Sharable m n rho

/-- PDF p.5: the completely mixed operator on a finite register. -/
def fullyMixed (I : Type*) [Fintype I] [DecidableEq I] : Op I :=
  ((Fintype.card I : ℂ)⁻¹) • 1

/-- PDF pp.3,5: a convex combination with weight t on the first operator. -/
def convexStateMixture {I : Type*} (t : ℝ) (A B : Op I) : Op I :=
  (t : ℂ) • A + ((1-t : ℝ) : ℂ) • B

/-- Eq.(4), PDF p.5: conjugation by a product of local matrices.
The sharing theorems supply unitary factors; matrix arguments avoid coupling
the operation to a particular decidable-equality instance of a bundled unitary group. -/
def localConjugate {I J : Type*} [Fintype I] [Fintype J]
    (U : Op I) (V : Op J) (rho : Op (I × J)) :
    Op (I × J) :=
  let W := Matrix.kronecker U V
  W * rho * Wᴴ

/-- PDF p.6: the swap operator on two d-dimensional factors. -/
def quditSwapOperator (d : ℕ) : Op (Fin d × Fin d) :=
  fun a b => if a = (b.2,b.1) then 1 else 0

/-- PDF p.6: d times the maximally entangled projector, the partially transposed swap. -/
def entangledEffect (d : ℕ) : Op (Fin d × Fin d) :=
  fun a b => if a.1 = a.2 ∧ b.1 = b.2 then 1 else 0

/-- Sec.III A, PDF p.6, swap-expectation parametrization. Physical range [-1,1]. -/
def wernerSwapState (d : ℕ) (psi : ℝ) : Op (Fin d × Fin d) :=
  (((d : ℂ)-(psi : ℂ))/((d : ℂ)*((d : ℂ)^2-1))) • 1 +
    (((d : ℂ)*(psi : ℂ)-1)/((d : ℂ)*((d : ℂ)^2-1))) • quditSwapOperator d

/-- Sec.III A, PDF p.6: phi = d times singlet fraction. Physical range [0,d]. -/
def isotropicOverlapState (d : ℕ) (phi : ℝ) : Op (Fin d × Fin d) :=
  (((d : ℂ)-(phi : ℂ))/((d : ℂ)*((d : ℂ)^2-1))) • 1 +
    (((d : ℂ)*(phi : ℂ)-1)/((d : ℂ)*((d : ℂ)^2-1))) • entangledEffect d

/-- Eq.(5), PDF p.6, including the separable branch. -/
def wernerConcurrence (psi : ℝ) : ℝ := max 0 (-psi)

/-- Eq.(6), PDF p.6, including the separable branch. -/
def isotropicConcurrence (d : ℕ) (phi : ℝ) : ℝ :=
  Real.sqrt (2/((d : ℝ)*((d : ℝ)-1))) * max 0 (phi-1)

/-- Eq.(17), PDF p.8: primitive cube root with positive imaginary part. -/
def wernerCubeRoot : ℂ := Complex.exp (Complex.I * (2*Real.pi/3 : ℝ))

/-- Eqs.(15)–(17), PDF p.8. Coordinates are AB,AC,BC. -/
def wernerRegion (d : ℕ) (a b c : ℝ) : Prop :=
  let mean := (a+b+c)/3
  let radius := (2/3 : ℝ)*‖(c : ℂ)+wernerCubeRoot*(b : ℂ)+wernerCubeRoot^2*(a : ℂ)‖
  radius ≤ 1-mean ∧ (if d = 2 then 0 ≤ mean else radius ≤ 1+mean)

/-- Eq.(21), PDF p.8: exp(i theta) as the source's explicit radicals. -/
def mixedConePhase (d : ℕ) : ℂ :=
  (Real.sqrt (((d : ℝ)-1)/(2*d)) : ℂ) +
    Complex.I * (Real.sqrt (((d : ℝ)+1)/(2*d)) : ℂ)

/-- Eqs.(20)–(21), PDF p.8: the cone inside its physical parameter box. -/
def mixedCone (d : ℕ) : Set (Fin 3 → ℝ) :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ d ∧ 0 ≤ x 1 ∧ x 1 ≤ d ∧ -1 ≤ x 2 ∧ x 2 ≤ 1 ∧
    x 0+x 1-x 2 ≤ d ∧
    ‖((d : ℝ)*(x 2-1) : ℂ) + (Real.sqrt (2*d/((d : ℝ)-1)) : ℂ) *
      (mixedConePhase d*(x 0 : ℂ)+conj (mixedConePhase d)*(x 1 : ℂ))‖ ≤ 1+x 0+x 1-x 2}

/-- Theorem III.2, PDF p.8: higher dimensions add precisely the vertex (0,0,-1). -/
def mixedRegion (d : ℕ) : Set (Fin 3 → ℝ) :=
  if d = 2 then mixedCone d else convexHull ℝ (mixedCone d ∪ {![0,0,-1]})

/-- Eq.(23), PDF p.9: ellipse circumference; its hull with the origin is used below. -/
def isotropicEllipse (d : ℕ) : Set (Fin 2 → ℝ) :=
  {x | (x 0+x 1-(d : ℝ))^2+(x 0-x 1)^2/((d : ℝ)^2-1) = 1}

/-- Theorem III.6, PDF p.11: a central site and n distinct outer marginals. -/
def IsotropicStarJoinable (d n : ℕ) (phi : Fin n → ℝ) : Prop :=
  ∃ X : Op (SharingIndex (Fin d) (Fin d) 1 n),
    IsDensityMatrix X ∧ ∀ j, sharingMarginal X 0 j = isotropicOverlapState d (phi j)

/-- Eq.(8), PDF p.7: classical analogue with agreement probability alpha. -/
def classicalAgreementLaw (d : ℕ) (alpha : ℝ) : Fin d × Fin d → ℝ :=
  fun a => if a.1 = a.2 then alpha/d else (1-alpha)/((d : ℝ)*((d : ℝ)-1))

/-- PDF pp.7–8: actual classical joining law, ordered AB,AC,BC. -/
def ClassicalTripleJoinable (d : ℕ) (a b c : ℝ) : Prop :=
  ∃ p : Fin d × Fin d × Fin d → ℝ,
    (∀ x, 0 ≤ p x) ∧ (∑ x, p x) = 1 ∧
    (∀ i j, (∑ k, p (i,j,k)) = classicalAgreementLaw d a (i,j)) ∧
    (∀ i k, (∑ j, p (i,j,k)) = classicalAgreementLaw d b (i,k)) ∧
    (∀ j k, (∑ i, p (i,j,k)) = classicalAgreementLaw d c (j,k))

/-- PDF p.7: four always available vertices and the all-disagree vertex when d >= 3. -/
def classicalVertices (d : ℕ) : Set (Fin 3 → ℝ) :=
  {![1,1,1], ![1,0,0], ![0,1,0], ![0,0,1]} ∪
    (if 3 ≤ d then {![0,0,0]} else ∅)

/-- Eq.(7), PDF p.6: fully antisymmetric normalized d-partite amplitude.
Zero-based coordinates replace the source's labels 1,...,d. -/
def fullAntisymmetricVector (d : ℕ) : EuclideanSpace ℂ (Fin d → Fin d) :=
  (Real.sqrt (d.factorial : ℝ) : ℂ)⁻¹ •
    ∑ pi : Equiv.Perm (Fin d),
      ((((Equiv.Perm.sign pi : ℤˣ) : ℤ) : ℂ)) • ket (fun i => pi.symm i)

/-- PDF pp.6–7: arbitrary pair reduction on a homogeneous tensor register. -/
def pairMarginal {d N : ℕ} (X : Op (Fin N → Fin d))
    (i j : Fin N) : Op (Fin d × Fin d) :=
  fun a b => ∑ x : Fin N → Fin d,
    if x i = a.1 ∧ x j = a.2 then
      X x (Function.update (Function.update x i b.1) j b.2) else 0

/-- PDF pp.3–4: explicit CQ witnesses in the X and Z bases, as (I+P⊗P)/4. -/
def cqWitness (inXBasis : Bool) : Op (Fin 2 × Fin 2) :=
  let Z : Op (Fin 2) := Matrix.diagonal ![(1 : ℂ),-1]
  let X : Op (Fin 2) := !![0,1;1,0]
  (1/4 : ℂ) • (1 + Matrix.kronecker (if inXBasis then X else Z)
    (if inXBasis then X else Z))

/-- PDF p.4: classical on the first subsystem in some orthonormal basis. -/
def IsClassicalQuantum {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (rho : Op (I × J)) : Prop :=
  ∃ U : Matrix.unitaryGroup I ℂ, ∃ p : I → ℝ, ∃ sigma : I → Op J,
    (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ (∀ i, IsDensityMatrix (sigma i)) ∧
    rho = ∑ i, (p i : ℂ) • Matrix.kronecker
      ((U : Op I) * (Matrix.diagonal (fun j => if j = i then 1 else 0)) * (U : Op I)ᴴ)
      (sigma i)

/-- Proposition IV.1, PDF p.12: the specified qubit counterexample. -/
def qubitSharingWitness : Op (Fin 2 × Fin 2) :=
  let v : EuclideanSpace ℂ (Fin 2 × Fin 2) := ket (0,0)+ket (1,1)
  (1/3 : ℂ) • (pureDensity v+pureDensity (ket (1,0)))

/-- Proposition IV.1, PDF p.13: the normalized three-qubit pure joining state. -/
def qubitJoiningWitness : Op (Fin 2 × Fin 2 × Fin 2) :=
  pureDensity ((Real.sqrt 3 : ℂ)⁻¹ • (ket (0,0,0)+ket (1,0,1)+ket (1,1,0)))

/-- PDF p.13: pseudo-pure mixture, weight t on a normalized maximally entangled vector. -/
def pseudoPure (t : ℝ) (v : EuclideanSpace ℂ (Fin 2 × Fin 2)) : Op (Fin 2 × Fin 2) :=
  convexStateMixture t (pureDensity v) (fullyMixed (Fin 2 × Fin 2))

/-- General neighborhoods of Sec.II A, PDF pp.2–3. -/
abbrev NeighborhoodConfiguration {N : ℕ} (dim : Fin N → ℕ) (S : Finset (Fin N)) :=
  (i : {i // i ∈ S}) → Fin (dim i.val)

/-- PDF p.3: combine a neighborhood configuration and its tensor complement. -/
def assembleNeighborhood {N : ℕ} {dim : Fin N → ℕ} {S : Finset (Fin N)}
    (x : NeighborhoodConfiguration dim S) (z : NeighborhoodConfiguration dim Sᶜ) : (i : Fin N) → Fin (dim i) :=
  fun i => if h : i ∈ S then x ⟨i,h⟩ else z ⟨i,by simpa using h⟩

/-- Eq.(1), PDF p.3: explicit partial trace for an arbitrary neighborhood. -/
def neighborhoodMarginal {N : ℕ} (dim : Fin N → ℕ) (S : Finset (Fin N))
    (X : Op ((i : Fin N) → Fin (dim i))) : Op (NeighborhoodConfiguration dim S) :=
  fun a b => ∑ z : NeighborhoodConfiguration dim Sᶜ, X (assembleNeighborhood a z) (assembleNeighborhood b z)

/-- Definition II.1, PDF p.3: the full joining fiber of any finite neighborhood list. -/
def JoiningList {N q : ℕ} (dim : Fin N → ℕ) (S : Fin q → Finset (Fin N))
    (rho : (j : Fin q) → Op (NeighborhoodConfiguration dim (S j)))
    (X : Op ((i : Fin N) → Fin (dim i))) : Prop :=
  IsDensityMatrix X ∧ ∀ j, neighborhoodMarginal dim (S j) X = rho j

/-- PDF pp.8,12: the tensor power of a matrix, with an optional conjugate on site zero. -/
def collectiveTensorOperator {d N : ℕ} (mixed : Bool) (U : Op (Fin d)) : Op (Fin N → Fin d) :=
  fun a b => ∏ i, if mixed ∧ i.val = 0 then conj (U (a i) (b i)) else U (a i) (b i)

/-- Eqs.(13),(18), PDF p.8: U⊗U⊗U or conjugate(U)⊗U⊗U in A,B,C order. -/
def collectiveTriple {d : ℕ} (mixed : Bool) (U : Op (Fin d)) : Op (Fin d × Fin d × Fin d) :=
  Matrix.kronecker (if mixed then U.map conj else U) (Matrix.kronecker U U)

/-- Eqs.(13),(18), PDF p.8: the normalized Haar twirl, as a matrix-valued integral. -/
def tripleTwirl {d : ℕ} (mixed : Bool) (X : Op (Fin d × Fin d × Fin d)) :
    Op (Fin d × Fin d × Fin d) :=
  ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
    collectiveTriple mixed (U : Op (Fin d)) * X * (collectiveTriple mixed (U : Op (Fin d)))ᴴ
    ∂(Schur.unitaryHaar d)

/-- Corollary IV.2, PDF p.13: the two-factor Haar twirl, with conjugation on A only. -/
def pairTwirl {d : ℕ} (mixed : Bool) (rho : Op (Fin d × Fin d)) : Op (Fin d × Fin d) :=
  ∫ U : Matrix.unitaryGroup (Fin d) ℂ,
    let W := Matrix.kronecker (if mixed then (U : Op (Fin d)).map conj else (U : Op (Fin d)))
      (U : Op (Fin d))
    W * rho * Wᴴ ∂(Schur.unitaryHaar d)

/-- PDF p.9: the explicit rotation about the diagonal line, with fixed origin. -/
def diagonalAxisRotation (theta : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let mean := (x 0+x 1+x 2)/3
  let c := Real.cos theta
  let s := Real.sin theta / Real.sqrt 3
  ![mean+c*(x 0-mean)+s*(x 2-x 1),
    mean+c*(x 1-mean)+s*(x 0-x 2),
    mean+c*(x 2-mean)+s*(x 1-x 0)]

/-- Table I(c), PDF p.12: uncomputed entries return none, never a zero threshold. -/
def tableFour : ℕ → ℕ → Option ℝ
  | 1,1 | 1,2 | 1,3 | 2,1 | 3,1 | 2,2 => some 1
  | 1,4 | 4,1 => some (3/4)
  | 1,5 | 5,1 => some (3/5)
  | 2,3 | 3,2 => some (2/3)
  | 2,4 | 4,2 | 2,5 | 5,2 | 3,4 | 4,3 => some (1/2)
  | 3,3 => some (5/9)
  | _,_ => none

example {I : Type*} [Fintype I] [DecidableEq I] (A : Op I) : convexStateMixture 1 A 0 = A := by
  simp [convexStateMixture]

example : wernerConcurrence 0 = 0 := by simp [wernerConcurrence]

example : tableFour 3 3 = some (5/9) ∧ tableFour 3 5 = none := ⟨rfl,rfl⟩

example {d : ℕ} (a b : Fin d) : quditSwapOperator d (a,b) (b,a) = 1 := by simp [quditSwapOperator]

example {d : ℕ} (a b : Fin d) : entangledEffect d (a,a) (b,b) = 1 := by
  simp [entangledEffect]

example {I J K : Type*} [Fintype K] : (idTensorSuperop traceRight) (0 : Op (I × J × K)) = 0 := by
  ext a b
  simp [idTensorSuperop, traceRight]

example {I J : Type*} [Fintype I] [Fintype J] {m n : ℕ} (i : Fin m) (j : Fin n) :
    sharingMarginal (0 : Op (SharingIndex I J m n)) i j = 0 := by
  ext a b
  simp [sharingMarginal]

example (U : Op (Fin 2)) : collectiveTensorOperator (N := 0) false U = 1 := by
  ext a b
  simp [collectiveTensorOperator, Matrix.one_apply, Subsingleton.elim a b]

/-- Appendix A, PDF p.14: the three actual transpositions and the oriented 3-cycle. -/
def triplePerm (d : ℕ) (k : Fin 4) : Op (Fin d × Fin d × Fin d) :=
  fun a b => if a = (match k.val with
    | 0 => (b.2.1,b.1,b.2.2)
    | 1 => (b.1,b.2.2,b.2.1)
    | 2 => (b.2.2,b.2.1,b.1)
    | _ => (b.2.2,b.1,b.2.1)) then 1 else 0

/-- Appendix A, PDF p.14: transpose on factor A, without changing B,C. -/
def transposeA {d : ℕ} (X : Op (Fin d × Fin d × Fin d)) : Op (Fin d × Fin d × Fin d) :=
  fun a b => X (b.1,a.2) (a.1,b.2)

/-- Eqs.(A1)–(A2), PDF p.14; coordinates ordered +,-,0,1,2,3. -/
def wernerBasis (d : ℕ) : Fin 6 → Op (Fin d × Fin d × Fin d) :=
  let A := triplePerm d 0
  let B := triplePerm d 1
  let C := triplePerm d 2
  let T := triplePerm d 3
  ![(1/6 : ℂ) • (1+A+B+C+T+Tᴴ),
    (1/6 : ℂ) • (1-A-B-C+T+Tᴴ),
    (1/3 : ℂ) • ((2 : ℂ) • 1-T-Tᴴ),
    (1/3 : ℂ) • ((2 : ℂ) • B-C-A),
    (Real.sqrt 3 : ℂ)⁻¹ • (A-C),
    (Complex.I/(Real.sqrt 3 : ℂ)) • (T-Tᴴ)]

/-- Eqs.(A5)–(A6), PDF p.14; no unit Hilbert–Schmidt normalization is asserted. -/
def mixedBasis (d : ℕ) : Fin 6 → Op (Fin d × Fin d × Fin d) :=
  let A := transposeA (triplePerm d 0)
  let B := triplePerm d 1
  let C := transposeA (triplePerm d 2)
  let T := transposeA (triplePerm d 3)
  let Td := transposeA ((triplePerm d 3)ᴴ)
  ![(1/2 : ℂ) • (1+B-((d : ℂ)+1)⁻¹ • (A+C+T+Td)),
    (1/2 : ℂ) • (1-B+((d : ℂ)-1)⁻¹ • (T+Td-A-C)),
    ((d : ℂ)^2-1)⁻¹ • ((d : ℂ) • (A+C)-(T+Td)),
    ((d : ℂ)^2-1)⁻¹ • ((d : ℂ) • (T+Td)-(A+C)),
    (Real.sqrt ((d : ℝ)^2-1) : ℂ)⁻¹ • (A-C),
    (Complex.I/(Real.sqrt ((d : ℝ)^2-1) : ℂ)) • (T-Td)]

/-- Eqs.(A3),(A7), PDF p.14: actual density reconstruction, with the absent
antisymmetric sector explicitly omitted at d=2. -/
def coordinateOperator (mixed : Bool) (d : ℕ) (r : Fin 6 → ℝ) :
    Op (Fin d × Fin d × Fin d) :=
  let B := if mixed then mixedBasis d else wernerBasis d
  let cp : ℂ := if mixed then 2/((d : ℂ)*(d+2)*(d-1)) else 6/((d : ℂ)*(d+1)*(d+2))
  let cm : ℂ := if mixed then 2/((d : ℂ)*(d-2)*(d+1)) else 6/((d : ℂ)*(d-1)*(d-2))
  let c0 : ℂ := if mixed then 1/(2*(d : ℂ)) else 3/(2*(d : ℂ)*((d : ℂ)^2-1))
  (cp*(r 0 : ℂ)) • B 0 +
    (if d = 2 then 0 else (cm*(r 1 : ℂ)) • B 1) +
    c0 • ∑ i : Fin 4, (r ((⟨i.val+2, by omega⟩ : Fin 6)) : ℂ) • B ((⟨i.val+2, by omega⟩ : Fin 6))

/-- Eqs.(A4),(A7), PDF pp.14–15: trace one, positivity ball, and absent sector. -/
def PhysicalCoordinates (d : ℕ) (r : Fin 6 → ℝ) : Prop :=
  r 0+r 1+r 2 = 1 ∧ 0 ≤ r 0 ∧ 0 ≤ r 1 ∧ 0 ≤ r 2 ∧
    (r 3)^2+(r 4)^2+(r 5)^2 ≤ (r 2)^2 ∧ (d = 2 → r 1 = 0)

/-- Appendix A, PDF p.14: coordinates computed from the physical operator. -/
def tripleSymmetryCoordinates (mixed : Bool) (d : ℕ) (X : Op (Fin d × Fin d × Fin d)) : Fin 6 → ℝ :=
  fun k => (X * (if mixed then mixedBasis d k else wernerBasis d k)).trace.re

/-- Eqs.(14),(19), PDF p.8: the concrete collective-invariant subspace. -/
def TripleInvariant {d : ℕ} (mixed : Bool) (X : Op (Fin d × Fin d × Fin d)) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
    collectiveTriple mixed (U : Op (Fin d)) * X * (collectiveTriple mixed (U : Op (Fin d)))ᴴ = X

/-- Appendix A's two full physical coordinate characterizations, PDF pp.14–15. -/
def CoordinateCharacterization (mixed : Bool) (d : ℕ) : Prop :=
  (∀ X, IsDensityMatrix X → TripleInvariant mixed X →
    PhysicalCoordinates d (tripleSymmetryCoordinates mixed d X) ∧
    coordinateOperator mixed d (tripleSymmetryCoordinates mixed d X) = X) ∧
  (∀ r : Fin 6 → ℝ, (d = 2 → r 1 = 0) →
    (IsDensityMatrix (coordinateOperator mixed d r) ↔ PhysicalCoordinates d r)) ∧
  (∀ r, PhysicalCoordinates d r →
    TripleInvariant mixed (coordinateOperator mixed d r) ∧
    tripleSymmetryCoordinates mixed d (coordinateOperator mixed d r) = r)

/-- Appendix B, PDF p.17: the actual cross-group swap matrix. -/
def crossSwap {d m n : ℕ} (i : Fin m) (j : Fin n) : Op (SharingIndex (Fin d) (Fin d) m n) :=
  fun a b => if a = (Function.update b.1 i (b.2 j),Function.update b.2 j (b.1 i)) then 1 else 0

/-- Appendix B, PDF p.17: minus the average of the mn cross-group swaps. -/
def sharingHamiltonian (d m n : ℕ) : Op (SharingIndex (Fin d) (Fin d) m n) :=
  (-(1/((m : ℂ)*(n : ℂ)))) • ∑ i : Fin m, ∑ j : Fin n, crossSwap i j

/-- Appendix B, PDF p.17: real eigenvalues, defined by actual nonzero eigenvectors. -/
def realEigenvalues {I : Type*} [Fintype I] [DecidableEq I] (H : Op I) : Set ℝ :=
  {r | ∃ v : EuclideanSpace ℂ I, v ≠ 0 ∧ act H v = (r : ℂ) • v}

/-- Appendix B, PDF p.17: maximum of the nonempty finite real spectrum of a
Hermitian operator on the nonempty physical register. Only that domain is used. -/
def maximalRealEigenvalue {I : Type*} [Fintype I] [DecidableEq I] (H : Op I) : ℝ :=
  sSup (realEigenvalues H)

/-- Appendix B, PDF p.17: the orthogonal projector onto the entire eigenspace. -/
def fullEigenkernelProjector {I : Type*} [Fintype I] [DecidableEq I] (H : Op I) (r : ℝ) : Op I :=
  let E := LinearMap.ker (Matrix.toEuclideanLin (H-(r : ℂ) • 1))
  fun a b => inner ℂ (ket a) (E.starProjection (ket b))

/-- Appendix B, PDF p.17: the whole top-eigenspace projector divided by its trace. -/
def extremalSharingState (d m n : ℕ) : Op (SharingIndex (Fin d) (Fin d) m n) :=
  let H := sharingHamiltonian d m n
  let P := fullEigenkernelProjector H (maximalRealEigenvalue H)
  P.trace⁻¹ • P

/-- Eq.(B1), PDF p.17: insert a local generator on one site of a tensor register. -/
def embeddedQuditGenerator {d N : ℕ} (i : Fin N) (A : Op (Fin d)) : Op (Fin N → Fin d) :=
  fun a b => A (a i) (b i) * ∏ k ∈ Finset.univ.erase i, if a k = b k then 1 else 0

/-- Eq.(B1), PDF p.17: group Casimir embedded in the same full register.
left/right flags select L, R, or their union. -/
def collectiveCasimir {d m n : ℕ} (left right : Bool)
    (L : Fin (d*d-1) → Op (Fin d)) : Op (SharingIndex (Fin d) (Fin d) m n) :=
  ∑ alpha : Fin (d*d-1),
    ((if left then Matrix.kronecker (∑ i : Fin m, embeddedQuditGenerator i (L alpha))
      (1 : Op (Fin n → Fin d)) else 0) +
     (if right then Matrix.kronecker (1 : Op (Fin m → Fin d))
      (∑ j : Fin n, embeddedQuditGenerator j (L alpha)) else 0))^2

/-- Eq.(B1)'s normalization, PDF p.17: Hermitian traceless generators with
Tr(lambda_alpha lambda_beta)=delta_alpha,beta, spanning by their full dimension. -/
def NormalizedGenerators (d : ℕ) (L : Fin (d*d-1) → Op (Fin d)) : Prop :=
  (∀ alpha, (L alpha).IsHermitian ∧ (L alpha).trace = 0) ∧
    ∀ alpha beta, (L alpha * L beta).trace = if alpha = beta then 1 else 0

/-- Eq.(B3), PDF p.18: sum of squared column heights, over all possibly nonempty columns. -/
def youngColumnSquareSum {d n : ℕ} (Y : Schur.Partition d n) : ℝ :=
  ∑ j ∈ Finset.range n, (Y.val.colLen j : ℝ)^2

/-- Eq.(B3), PDF p.18: sum of squared row lengths, with zero padding up to d. -/
def rowSquares {d n : ℕ} (Y : Schur.Partition d n) : ℝ :=
  ∑ i ∈ Finset.range d, (Y.val.rowLen i : ℝ)^2

/-- Eq.(B3), PDF p.18: scalar prescribed by three Young diagrams. -/
def youngEigenvalue {d m n : ℕ} (YL : Schur.Partition d m) (YR : Schur.Partition d n)
    (Y : Schur.Partition d (m+n)) : ℝ :=
  (youngColumnSquareSum Y-youngColumnSquareSum YL-youngColumnSquareSum YR-rowSquares Y+rowSquares YL+rowSquares YR)/
    (2*(m : ℝ)*(n : ℝ))

/-- PDF pp.17–18: actual simultaneous physical isotypic sector.
The accepted character idempotents are constructed independently of H and of Eq.(B3). -/
def youngSector {d m n : ℕ} (YL : Schur.Partition d m) (YR : Schur.Partition d n)
    (Y : Schur.Partition d (m+n)) : Op (SharingIndex (Fin d) (Fin d) m n) :=
  let P : Op (SharingIndex (Fin d) (Fin d) m n) := fun a b =>
    Schur.isotypicProjector Y (Fin.append a.1 a.2) (Fin.append b.1 b.2)
  P * Matrix.kronecker (Schur.isotypicProjector YL) (Schur.isotypicProjector YR)

example {d : ℕ} (X : Op (Fin d × Fin d × Fin d)) : transposeA (transposeA X) = X := rfl

example {d m n : ℕ} : collectiveCasimir (m := m) (n := n) false false
    (fun _ : Fin (d*d-1) => (0 : Op (Fin d))) = 0 := by
  simp [collectiveCasimir]

example (d n : ℕ) : sharingHamiltonian d 0 n = 0 := by
  simp [sharingHamiltonian]

example (d : ℕ) : coordinateOperator false d (fun _ => 0) = 0 := by
  simp [coordinateOperator]

example (d : ℕ) : coordinateOperator true d (fun _ => 0) = 0 := by
  simp [coordinateOperator]

end QAlgorithms.Papers.Independent.Extend50.P36


