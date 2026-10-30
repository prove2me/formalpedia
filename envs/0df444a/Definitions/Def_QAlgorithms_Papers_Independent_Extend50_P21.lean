-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P21
-- name    : QAlgorithms_Papers_Independent_Extend50_P21
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T20:08:45.272989+00:00
-- url     : https://prove2.me/theorems/ceb7c45c-426d-44cd-9ada-807248c7cbeb
-- title:
--   Definitions for Programmability of covariant quantum channels
-- statement:
--   The objects the formalized statements of *Programmability of covariant quantum channels* (arXiv:2012.00717) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CompactLie`: PDF p.3: compact means a finite-dimensional real compact Lie group. The manifold structure is existential; no connectedness is imposed.
--   - `ContinuousUnitaryRep`: PDF p.3, Definitions 1--2: a continuous unitary representation on a positive-dimensional coordinate Hilbert space. The matrix homomorphism is the accepted Support21.P09.Rep; this wrapper adds continuity and unitarity.
--   - `OperatorCovariant`: PDF pp.4--5: covariance on every operator. CPTP is recorded separately.
--   - `covariantChannels`: PDF p.5: the entire class of covariant channels.
--   - `covariantTensorCommutant`: PDF p.7: the actual physical commutant of entrywise-conjugate U tensor V.
--   - `choiSet`: PDF p.5: normalized reference-first Choi image of a channel class.
--   - `TensorIsotypicDecomposition`: PDF pp.3,7: a physical isotypic decomposition, with distinct occurring irreducible types and positive multiplicities. W transports the block representation onto the actual input-copy tensor output space; sizes alone are not a decomposition.
--   - `compressedDim`: PDF pp.15,21: the compressed program dimension.
--   - `netDim`: PDF p.17: real dimension bound on the Hermitian commutant.
--   - `programmedChannel`: PDF pp.5--6: channel induced by a program, with input before program.
--   - `ProgramsChannelClass`: PDF p.5: one fixed CPTP processor works for all target channels with the source half-diamond error and possibly mixed density programs.
--   - `PureImplements`: PDF pp.6,21: pure programs are unit vectors.
--   - `PureSimulation`: PDF p.6: exact simulation of all channels induced by the original processor, with the new processor fixed before the original program is chosen.
--   - `FiniteMeasurePrepareProcessor`: PDF p.9, Definition 17: a finite positive POVM and fixed channels in C. POVM effects need not have trace one; the printed D(HP) is corrected accordingly.
--   - `CommutativeMatrixSet`: PDF p.8: commutativity of an actual matrix algebra.
--   - `Polytope`: PDF pp.8--9: a polytope is the convex hull of a finite nonempty set. Being affinely isomorphic to a polytope is equivalent to this intrinsic property.
--   - `Simplex`: PDF pp.8--9: a simplex is the convex hull of finitely many affinely independent vertices. A single vertex gives the zero-dimensional simplex.
--   - `fullUnitaryClass`: PDF p.10: covariance under every unitary of the defining representation.
--   - `caratheodorySize`: PDF p.6: affine dimension plus one used in the refined purification bound.
--   - `oneDimMultiplicity`: PDF p.11, Proposition 21: multiplicity of a one-dimensional type is the complex dimension of its actual intertwiner/eigenvector space, including zero when the type is absent. It is not an arbitrary supplied integer.
--   - `omegaDensity`: PDF pp.10--11: normalized maximally entangled density (reference first).
--   - `tetraBasis`: PDF p.13: real orthonormal coordinates for H={(a_i): sum a_i=0}. The columns are (1,1,-1,-1)/2, (1,-1,1,-1)/2, (1,-1,-1,1)/2.
--   - `tetraMatrices`: PDF pp.12--13: the physical A4 permutation action, restricted to H by Q.
--   - `tetraRoot`: PDF p.13: the fixed primitive third root of unity.
--   - `tetraCycle`: PDF p.12: the permutation (123), using zero-based coordinates.
--   - `tetraCoset`: PDF pp.12--13: label the cosets K4,cK4,c^2K4. Inside A4, K4 consists exactly of elements whose square is the identity.
--   - `tetraCharacter`: PDF p.13: phi_j(c^k K4)=tetraRoot^(jk).
--   - `tetraBlocks`: PDF p.13, Eq.(3.1): the direct-sum representation, scalar types first, then theta tensor I_2.
--   - `tetraClass`: PDF p.13: all channels for the physical real tetrahedral action.
--   - `tetraV`: PDF p.13: V on H is fixed by the four displayed images of the tetrahedron vertices. The 4x4 matrix maps each vi to exactly that redundant prescription.
--   - `tetraUnitary`: PDF p.13: the three unitary channels.
--   - `tetraFlip`: PDF p.14: swap in the same real orthonormal coordinates.
--   - `tetraCornerProjection`: PDF p.14: the actual rank-six corner projector.
--   - `tetraPauli`: PDF p.14: Pauli X,Y,Z in that corner; Z has coefficient 1/(i sqrt(3)).
--   - `tetraCorner`: PDF p.14: the actual covariantTensorCommutant corner, with its support conditions.
--   - `tetraBloch`: PDF p.14: Bloch states, normalized by rank(P)=6.
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, https://arxiv.org/abs/2012.00717v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

/-!
Programmability of covariant quantum channels, arXiv:2012.00717v2.
All source citations use PDF pages. Accepted P56 supplies the normalized,
reference-first Choi definition and the reused Lemma 11. Other imports are
pinned accepted modules for representation, norm and channel definitions.
Compilation is pending the mechanical handoff.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff
open QAlgorithms
open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)
open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible EquivalentModels)
open QAlgorithms.Papers.Independent.Information100.P69 (diamond)
open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)
open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

namespace QAlgorithms.Papers.Independent.Extend50.P21

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF p.3: compact means a finite-dimensional real compact Lie group.
The manifold structure is existential; no connectedness is imposed. -/
def CompactLie (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  CompactSpace G ∧ T2Space G ∧ ∃ m : ℕ,
    ∃ charts : ChartedSpace (EuclideanSpace ℝ (Fin m)) G,
      letI := charts
      IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G ∧
      LieGroup (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ G

/-- PDF p.3, Definitions 1--2: a continuous unitary representation on a
positive-dimensional coordinate Hilbert space. The matrix homomorphism is the
accepted Support21.P09.Rep; this wrapper adds continuity and unitarity. -/
structure ContinuousUnitaryRep (G I : Type*) [Group G] [TopologicalSpace G]
    [Fintype I] [DecidableEq I] where
  mat : QAlgorithms.Papers.Independent.Support21.P09.Rep G I
  positive : 0 < Fintype.card I
  unitary_left : ∀ g, (mat g)ᴴ * mat g = 1
  unitary_right : ∀ g, mat g * (mat g)ᴴ = 1
  continuous : Continuous (mat : G → Matrix I I ℂ)

/-- Sanity: the accepted homomorphism fixes the identity group element. -/
example {G I : Type*} [Group G] [TopologicalSpace G]
    [Fintype I] [DecidableEq I] (U : ContinuousUnitaryRep G I) : U.mat 1 = 1 := by
  exact U.mat.map_one

/-- PDF pp.4--5: covariance on every operator. CPTP is recorded separately. -/
def OperatorCovariant {G I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (U : G → Matrix I I ℂ)
    (V : G → Matrix O O ℂ) (T : Superop I O) : Prop :=
  ∀ g A, T (U g * A * (U g)ᴴ) = V g * T A * (V g)ᴴ

/-- PDF p.5: the entire class of covariant channels. -/
def covariantChannels {G I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (U : G → Matrix I I ℂ)
    (V : G → Matrix O O ℂ) : Set (Superop I O) :=
  {T | IsChannel T ∧ OperatorCovariant U V T}

/-- PDF p.7: the actual physical commutant of entrywise-conjugate U tensor V. -/
def covariantTensorCommutant {G I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (U : G → Matrix I I ℂ)
    (V : G → Matrix O O ℂ) : Set (Matrix (I × O) (I × O) ℂ) :=
  {X | ∀ g, Commute X (Matrix.kronecker (fun i j => conj (U g i j)) (V g))}

/-- PDF p.5: normalized reference-first Choi image of a channel class. -/
def choiSet {I O : Type*} [Fintype I] [DecidableEq I]
    (C : Set (Superop I O)) : Set (Matrix (I × O) (I × O) ℂ) :=
  normalizedChoi '' C

/-- PDF pp.3,7: a physical isotypic decomposition, with distinct occurring
irreducible types and positive multiplicities. W transports the block representation
onto the actual input-copy tensor output space; sizes alone are not a decomposition. -/
structure TensorIsotypicDecomposition {G I O : Type*} [Group G] [TopologicalSpace G]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (U : ContinuousUnitaryRep G I) (V : ContinuousUnitaryRep G O) where
  count : ℕ
  degree : Fin count → ℕ
  copies : Fin count → ℕ
  degree_pos : ∀ k, 0 < degree k
  copies_pos : ∀ k, 0 < copies k
  component : (k : Fin count) → ContinuousUnitaryRep G (Fin (degree k))
  irreducible : ∀ k, Irreducible (component k).mat
  distinct : ∀ k l, k ≠ l → ¬ EquivalentModels (component k).mat (component l).mat
  transport : Matrix (I × O) (Σ k : Fin count, Fin (degree k) × Fin (copies k)) ℂ
  transport_left : transportᴴ * transport = 1
  transport_right : transport * transportᴴ = 1
  intertwines : ∀ g,
    Matrix.kronecker (fun i j => conj (U.mat g i j)) (V.mat g) * transport =
      transport * Matrix.blockDiagonal' (fun k =>
        Matrix.kronecker ((component k).mat g) (1 : Matrix (Fin (copies k)) (Fin (copies k)) ℂ))

/-- PDF pp.15,21: the compressed program dimension. -/
def compressedDim {G I O : Type*} [Group G] [TopologicalSpace G]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    {U : ContinuousUnitaryRep G I} {V : ContinuousUnitaryRep G O} (D : TensorIsotypicDecomposition U V) : ℕ :=
  ∑ k, D.copies k

/-- PDF p.17: real dimension bound on the Hermitian commutant. -/
def netDim {G I O : Type*} [Group G] [TopologicalSpace G]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    {U : ContinuousUnitaryRep G I} {V : ContinuousUnitaryRep G O} (D : TensorIsotypicDecomposition U V) : ℕ :=
  ∑ k, D.copies k ^ 2

/-- PDF pp.5--6: channel induced by a program, with input before program. -/
def programmedChannel {I O P : Type*} (processor : Superop (I × P) O)
    (program : Matrix P P ℂ) : Superop I O :=
  fun A => processor (Matrix.kronecker A program)

/-- PDF p.5: one fixed CPTP processor works for all target channels with the
source half-diamond error and possibly mixed density programs. -/
def ProgramsChannelClass {I O P : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Fintype P] [DecidableEq P]
    (processor : Superop (I × P) O) (C : Set (Superop I O)) (epsilon : ℝ) : Prop :=
  IsChannel processor ∧ ∀ T ∈ C, ∃ program : Matrix P P ℂ,
    IsDensityMatrix program ∧ diamond (fun A => programmedChannel processor program A - T A) / 2 ≤ epsilon

/-- PDF pp.6,21: pure programs are unit vectors. -/
def PureImplements {I O P : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Fintype P] [DecidableEq P]
    (processor : Superop (I × P) O) (C : Set (Superop I O)) (epsilon : ℝ) : Prop :=
  IsChannel processor ∧ ∀ T ∈ C, ∃ psi : EuclideanSpace ℂ P,
    ‖psi‖ = 1 ∧ diamond (fun A => programmedChannel processor (pureDensity psi) A - T A) / 2 ≤ epsilon

/-- PDF p.6: exact simulation of all channels induced by the original processor,
with the new processor fixed before the original program is chosen. -/
def PureSimulation {I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (p q : ℕ)
    (original : Superop (I × Fin p) O) (newProcessor : Superop (I × Fin q) O) : Prop :=
  IsChannel newProcessor ∧ ∀ program : Matrix (Fin p) (Fin p) ℂ,
    IsDensityMatrix program → ∃ psi : EuclideanSpace ℂ (Fin q),
      ‖psi‖ = 1 ∧ programmedChannel newProcessor (pureDensity psi) = programmedChannel original program

/-- PDF p.9, Definition 17: a finite positive POVM and fixed channels in C.
POVM effects need not have trace one; the printed D(HP) is corrected accordingly. -/
def FiniteMeasurePrepareProcessor {I O P : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] [Fintype P] [DecidableEq P]
    (processor : Superop (I × P) O) (C : Set (Superop I O)) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ effects : Fin k → Matrix P P ℂ,
    (∀ j, (effects j).PosSemidef) ∧ (∑ j, effects j) = 1 ∧
    ∃ targets : Fin k → Superop I O, (∀ j, targets j ∈ C) ∧
      ∀ A B, processor (Matrix.kronecker A B) =
        ∑ j, (Matrix.trace (effects j * B)) • targets j A

/-- PDF p.8: commutativity of an actual matrix algebra. -/
def CommutativeMatrixSet {A : Type*} [Fintype A] [DecidableEq A]
    (K : Set (Matrix A A ℂ)) : Prop := ∀ X ∈ K, ∀ Y ∈ K, Commute X Y

/-- PDF pp.8--9: a polytope is the convex hull of a finite nonempty set.
Being affinely isomorphic to a polytope is equivalent to this intrinsic property. -/
def Polytope {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) : Prop :=
  ∃ vertices : Finset E, vertices.Nonempty ∧ convexHull ℝ (vertices : Set E) = S

/-- PDF pp.8--9: a simplex is the convex hull of finitely many affinely
independent vertices. A single vertex gives the zero-dimensional simplex. -/
def Simplex {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ vertices : Fin k → E,
    AffineIndependent ℝ vertices ∧ convexHull ℝ (Set.range vertices) = S

/-- PDF p.10: covariance under every unitary of the defining representation. -/
def fullUnitaryClass (d : ℕ) : Set (Superop (Fin d) (Fin d)) :=
  {T | IsChannel T ∧ ∀ W : Matrix.unitaryGroup (Fin d) ℂ,
    ∀ A, T ((W : Matrix (Fin d) (Fin d) ℂ) * A * (W : Matrix (Fin d) (Fin d) ℂ)ᴴ) =
      (W : Matrix (Fin d) (Fin d) ℂ) * T A * (W : Matrix (Fin d) (Fin d) ℂ)ᴴ}

/-- PDF p.6: affine dimension plus one used in the refined purification bound. -/
def caratheodorySize (d1 d2 : ℕ) : ℕ := d1 ^ 2 * (d2 ^ 2 - 1) + 1

/-- Sanity: a one-dimensional output needs only one pure channel in a mixture. -/
example (d1 : ℕ) : caratheodorySize d1 1 = 1 := by simp [caratheodorySize]

/-- Sanity: the identity parameter is alpha=0. -/
example (d : ℕ) : depolarizing d 0 = (fun A => A) := by
  funext A
  simp [depolarizing]

/-- Sanity: a one-dimensional state has unit trace and is positive. -/
example : IsDensityMatrix (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  constructor
  · exact Matrix.PosSemidef.one
  · simp

/-- Sanity: normalized Choi reference-first entry at input dimension one. -/
example (T : Superop (Fin 1) (Fin 2)) (a b : Fin 2) :
    normalizedChoi T (0, a) (0, b) = T (Matrix.single 0 0 1) a b := by
  simp [normalizedChoi]

/-- PDF p.11, Proposition 21: multiplicity of a one-dimensional type is the
complex dimension of its actual intertwiner/eigenvector space, including zero
when the type is absent. It is not an arbitrary supplied integer. -/
def oneDimMultiplicity {G I O : Type*} [Group G] [TopologicalSpace G]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (U : ContinuousUnitaryRep G I) (V : ContinuousUnitaryRep G O) (lambda : ContinuousUnitaryRep G (Fin 1)) : ℕ :=
  Module.finrank ℂ ((⨅ g : G, LinearMap.ker (Matrix.toLin'
    (Matrix.kronecker (fun i j => conj (U.mat g i j)) (V.mat g) -
      lambda.mat g 0 0 • (1 : Matrix (I × O) (I × O) ℂ)))) :
      Submodule ℂ ((I × O) → ℂ))

/-- PDF pp.10--11: normalized maximally entangled density (reference first). -/
def omegaDensity (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  normalizedChoi (fun A : Matrix (Fin d) (Fin d) ℂ => A)

section General

variable {G I O : Type*} [Group G] [TopologicalSpace G]
variable [Fintype I] [DecidableEq I] [inputNonempty : Nonempty I]
variable [Fintype O] [DecidableEq O] [outputNonempty : Nonempty O]

include inputNonempty outputNonempty

end General

/-- PDF p.2: finite groups carry the discrete topology. -/
local instance tetraTopology : TopologicalSpace (alternatingGroup (Fin 4)) := ⊥

/-- PDF p.13: real orthonormal coordinates for H={(a_i): sum a_i=0}.
The columns are (1,1,-1,-1)/2, (1,-1,1,-1)/2, (1,-1,-1,1)/2. -/
def tetraBasis : Matrix (Fin 4) (Fin 3) ℂ :=
  (1 / 2 : ℂ) • !![1, 1, 1; 1, -1, -1; -1, 1, -1; -1, -1, 1]

/-- PDF pp.12--13: the physical A4 permutation action, restricted to H by Q. -/
def tetraMatrices (g : alternatingGroup (Fin 4)) : Matrix (Fin 3) (Fin 3) ℂ :=
  tetraBasisᴴ * (Matrix.of fun a b : Fin 4 =>
    if a = (g : Equiv.Perm (Fin 4)) b then (1 : ℂ) else 0) * tetraBasis

/-- PDF p.13: the fixed primitive third root of unity. -/
def tetraRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

/-- PDF p.12: the permutation (123), using zero-based coordinates. -/
def tetraCycle : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2

/-- PDF pp.12--13: label the cosets K4,cK4,c^2K4. Inside A4, K4 consists
exactly of elements whose square is the identity. -/
def tetraCoset (g : alternatingGroup (Fin 4)) : ℕ :=
  if (g : Equiv.Perm (Fin 4)) ^ 2 = 1 then 0 else
    if (tetraCycle⁻¹ * (g : Equiv.Perm (Fin 4))) ^ 2 = 1 then 1 else 2

/-- PDF p.13: phi_j(c^k K4)=tetraRoot^(jk). -/
def tetraCharacter (j : Fin 3) (g : alternatingGroup (Fin 4)) : ℂ :=
  tetraRoot ^ (j.val * tetraCoset g)

/-- PDF p.13, Eq.(3.1): the direct-sum representation, scalar types first,
then theta tensor I_2. -/
def tetraBlocks (g : alternatingGroup (Fin 4)) :
    Matrix (Fin 3 ⊕ (Fin 3 × Fin 2)) (Fin 3 ⊕ (Fin 3 × Fin 2)) ℂ :=
  Matrix.fromBlocks (Matrix.diagonal (fun j => tetraCharacter j g)) 0 0
    (Matrix.kronecker (tetraMatrices g) (1 : Matrix (Fin 2) (Fin 2) ℂ))

/-- PDF p.13: all channels for the physical real tetrahedral action. -/
def tetraClass : Set (Superop (Fin 3) (Fin 3)) :=
  covariantChannels tetraMatrices tetraMatrices

/-- PDF p.13: V on H is fixed by the four displayed images of the tetrahedron
vertices. The 4x4 matrix maps each vi to exactly that redundant prescription. -/
def tetraV : Matrix (Fin 3) (Fin 3) ℂ :=
  tetraBasisᴴ * ((1 / 2 : ℂ) •
    !![0, 1, tetraRoot, tetraRoot ^ 2; 1, 0, tetraRoot ^ 2, tetraRoot;
       tetraRoot, tetraRoot ^ 2, 0, 1; tetraRoot ^ 2, tetraRoot, 1, 0]) * tetraBasis

/-- PDF p.13: the three unitary channels. -/
def tetraUnitary (j : Fin 3) : Superop (Fin 3) (Fin 3) :=
  conjSuperop (tetraV ^ j.val)

/-- PDF p.14: swap in the same real orthonormal coordinates. -/
def tetraFlip : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  Matrix.of fun a b => if a.1 = b.2 ∧ a.2 = b.1 then 1 else 0

/-- PDF p.14: the actual rank-six corner projector. -/
def tetraCornerProjection : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  1 - ∑ j : Fin 3, normalizedChoi (tetraUnitary j)

/-- PDF p.14: Pauli X,Y,Z in that corner; Z has coefficient 1/(i sqrt(3)). -/
def tetraPauli : Fin 3 → Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  let P := tetraCornerProjection
  let R := 2 • Matrix.kronecker tetraV tetraVᴴ + 1
  ![P * tetraFlip,
    (1 / (Real.sqrt 3 : ℂ)) • (P * tetraFlip * R),
    (1 / (Complex.I * (Real.sqrt 3 : ℂ))) • (P * R)]

/-- PDF p.14: the actual covariantTensorCommutant corner, with its support conditions. -/
def tetraCorner : Set (Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :=
  {X | X ∈ covariantTensorCommutant tetraMatrices tetraMatrices ∧
    tetraCornerProjection * X = X ∧ X * tetraCornerProjection = X}

/-- PDF p.14: Bloch states, normalized by rank(P)=6. -/
def tetraBloch (lambda : Fin 3 → ℝ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (1 / 6 : ℂ) • (tetraCornerProjection + ∑ j, (lambda j : ℂ) • tetraPauli j)

/-- Sanity: the first tetrahedral coordinate really lies in the sum-zero space. -/
example : (∑ i : Fin 4, tetraBasis i 0) = 0 := by
  norm_num [tetraBasis, Fin.sum_univ_succ]

/-- Sanity: the Bloch center uses the rank-six normalization. -/
example : tetraBloch (fun _ => 0) = (1 / 6 : ℂ) • tetraCornerProjection := by
  simp [tetraBloch]

end QAlgorithms.Papers.Independent.Extend50.P21


