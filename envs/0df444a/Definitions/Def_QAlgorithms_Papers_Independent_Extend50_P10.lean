-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P10
-- name    : QAlgorithms_Papers_Independent_Extend50_P10
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T19:34:55.694998+00:00
-- url     : https://prove2.me/theorems/0b3382d5-3f03-40c1-9ecc-8ac8b346bec6
-- title:
--   Definitions for Speeding up Learning Quantum States through Group Equivariant Convolutional Quantum Ansätze
-- statement:
--   The objects the formalized statements of *Speeding up Learning Quantum States through Group Equivariant Convolutional Quantum Ansätze* (arXiv:2112.07611) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `complexDiagonals`: PDF pp.6,19: the full complex diagonal Cartan, in the specified basis. Matrix units below reuse the accepted Information100.P44.matrixUnit.
--   - `imaginaryRealDiagonals`: PDF pp.6,21: i times every real diagonal matrix.
--   - `generatedLie`: PDF pp.19–21: the Lie subalgebra generated over K, with bracket AB−BA. The intersection is over all K-submodules containing S and closed under that bracket; it is not a linear span or a topological closure.
--   - `indexGraph`: PDF p.20, Definition II.2: adjacency of distinct indices, made symmetric so that the graph is defined even before Hermiticity is imposed. For Hermitian matrices either direction is equivalent to H_ij ≠ 0.
--   - `PathConnectedHamiltonian`: PDF p.20: a Hamiltonian is Hermitian, and its basis-index graph is connected. In particular, a singleton zero Hamiltonian is allowed.
--   - `augmentedZLabel`: PDF p.26: augmented Pauli Z eigenvalue labels; none is Z_0=I and some i is Z_(i+1). The frozen pauliLabel instead selects Pauli matrices and cannot represent this eigenvalue map. The extra identity coordinate does not change ordinary bit-string indexing.
--   - `quadraticPauliLabel`: PDF p.26: all second-order augmented labels, including identity and first-order labels as the entries with an index 0.
--   - `qaoaControls`: PDF pp.7,26: every independently variable real quadratic Z Hamiltonian. This is a control family, not a fixed cost Hamiltonian.
--   - `evolutionGroup`: PDF pp.6,21,26: finite products of the listed matrix exponentials. Submonoid.closure is algebraic: its elements have finite words. When the Hamiltonian set is real-linear, negative controls supply all inverses.
--   - `generalizedQaoaGroup`: PDF pp.7,26: the fixed mixer has arbitrary real evolution times.
--   - `quditSiteMatrix`: PDF pp.12,18: lift a one-site operator to a named qudit, fixing other sites. The alphabet is Fin d, matching the frozen physical tensor-permutation action. The accepted qubit-only siteOperator uses integer bit indices and is not this general-qudit named-wire matrix.
--   - `spinOperator`: PDF p.12: one-half of the specified Pauli operator on a named site. finTwoEquiv identifies Fin 2 symbols 0,1 with false,true.
--   - `spinDot`: PDF pp.12,18: the actual three-component spin-half exchange product.
--   - `pairAmplitude`: PDF pp.9–10: normalized antisymmetric pair, embedded in any alphabet.
--   - `singletInitialization`: PDF p.9, Eq.(5): k zeros followed by b disjoint singlets; n=k+2b.
--   - `twoRowDiagram`: PDF pp.9–10: the unique two-row shape, with no truncated division.
--   - `physicalShapeProjector`: A total adapter to the frozen full physical isotypic projector. On an invalid size/height diagram it is zero; every initialization statement below uses a size-correct, height-bounded diagram. It never selects an embedded Specht copy. The frozen cellular-JM shapeProjector is a different abstract algebra object.
--   - `occupationModule`: PDF pp.3,9: M^mu is the coordinate subspace spanned by all words with occupation vector mu. This is not one chosen irreducible summand of that space.
--   - `tripleAmplitude`: PDF p.10: the normalized SU(3) determinant singlet, in the exact printed order uds−usd+dsu−dus+sud−sdu.
--   - `su3Initialization`: PDF p.10: a singles, b normalized pairs, c normalized determinant triples, on a+2b+3c physical sites.
--   - `threeRowDiagram`: PDF p.10 with the forced site-count correction: (a+b+c,b+c,c). Printed (n+k+l,n−k+l,l) must read ((n+k)/2+l,(n−k)/2+l,l) when n=a+2b and k=a. The printed shape has too many boxes.
--   - `columnInitialization`: PDF pp.2,9–10: tensor normalized antisymmetric states on the columns of lambda. The frozen cell numbering determines placement. Column permutations act on the frozen row-word; distinct permutations give distinct basis words.
--   - `PreparationGate`: A named-wire qudit gate in the continuous one- and two-qudit model used for the constant-depth claim, PDF pp.2,9–10. Arbitrary wire pairs are allowed.
--   - `liftSupported`: Lift an operator on a fixed subset, acting identically elsewhere.
--   - `PreparationCircuit`: PDF pp.2,9–10: layers have pairwise disjoint supports; depth is their count. The gate matrices carry their own unitarity, not an unrelated cost witness.
--   - `preparationMatrix`: Layers are listed in chronological order and multiply on the left.
--   - `collectiveAction`: PDF p.3: the collective action g tensor n, computed in the physical basis.
--   - `CollectivelyInvariant`: PDF pp.23–24: SU(d) symmetry refers to the actual collective group action. The frozen rational-permutation-submodule IsInvariant is a different predicate.
--   - `localInvariantHamiltonians`: PDF p.24: each Hamiltonian is supported on one fixed subset of at most k sites. Different Hamiltonians may choose different subsets.
--   - `invariantLocalGroup`: PDF p.24: V_k, exact finite products of fixed-support invariant evolutions.
--   - `invariantLocalSumGroup`: PDF p.24: V'_k allows finite real sums with different supports before exponentiation. This is a real span of the concrete local Hermitian operators.
--   - `physicalAlgebraMatrix`: PDF p.3: the actual linear extension of the physical permutation action.
--   - `spechtAlgebraMatrix`: PDF pp.3,19,24: the matrix of the actual regular-ideal Specht action. Any fixed orthonormal coordinates suffice for a determinant: these coordinates are deliberately not claimed to be Young or sequential CG coordinates.
--   - `specialInvariantLocalGroup`: PDF p.24: SV_k imposes determinant one on each nonrepeated Specht block. The coefficient function represents U through the concrete physical action and also computes all Specht blocks; no arbitrary unrelated block matrices occur. Only physical height-bounded shapes are tested.
--   - `originalYjm`: PDF pp.4–5: the original physical X_(k+1), with X_1=0.
--   - `cqaYjm`: PDF pp.6,23: only in the CQA control family, replace X_1 by I.
--   - `quadraticPhysicalControls`: PDF pp.6,23: real independently variable augmented quadratic controls.
--   - `adjacentSwapHamiltonian`: PDF p.24: the open-chain adjacent-SWAP Hamiltonian, with no (1,n) term.
--   - `physicalCqaGroup`: PDF pp.7,24: the simultaneous-sector CQA group used in four-locality, with its fixed open-chain mixer H_S, not an arbitrary H_P.
-- source:
--   Speeding up Learning Quantum States through Group Equivariant Convolutional Quantum Ansätze, arXiv:2112.07611v3, https://arxiv.org/abs/2112.07611v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

/-!
Statements from arXiv:2112.07611v3. Deferred nodes and the missing canonical
physical Young/CG interfaces are recorded in the assigned chunk's HARD.md.
Only algebraic finite generation is used below; `closure` occurs only in the
supplement's explicitly weaker density statement. Compilation is pending the
batch handoff. All local definitions have complete bodies.
-/

noncomputable section

open scoped Matrix
open QAlgorithms
open QAlgorithms.Schur
open QAlgorithms.Papers.Independent.Information100.P44 (matrixUnit)

namespace QAlgorithms.Papers.Independent.Extend50.P10

attribute [local instance] Classical.propDecidable

/-- PDF pp.6,19: the full complex diagonal Cartan, in the specified basis.
Matrix units below reuse the accepted Information100.P44.matrixUnit. -/
def complexDiagonals (D : ℕ) : Set (Matrix (Fin D) (Fin D) ℂ) :=
  Set.range (fun v : Fin D → ℂ => Matrix.diagonal v)

/-- PDF pp.6,21: i times every real diagonal matrix. -/
def imaginaryRealDiagonals (D : ℕ) : Set (Matrix (Fin D) (Fin D) ℂ) :=
  Set.range (fun v : Fin D → ℝ =>
    Complex.I • Matrix.diagonal (fun j => (v j : ℂ)))

/-- PDF pp.19–21: the Lie subalgebra generated over K, with bracket AB−BA.
The intersection is over all K-submodules containing S and closed under that
bracket; it is not a linear span or a topological closure. -/
def generatedLie (K : Type*) [Field K] {A : Type*} [Ring A] [Module K A]
    (S : Set A) : Submodule K A :=
  sInf {V : Submodule K A | S ⊆ V ∧
    ∀ a ∈ V, ∀ b ∈ V, a * b - b * a ∈ V}

/-- PDF p.20, Definition II.2: adjacency of distinct indices, made symmetric
so that the graph is defined even before Hermiticity is imposed. For Hermitian
matrices either direction is equivalent to H_ij ≠ 0. -/
def indexGraph {ι : Type*} (H : Matrix ι ι ℂ) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (H i j ≠ 0 ∨ H j i ≠ 0)
  symm := ⟨fun i j h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

/-- PDF p.20: a Hamiltonian is Hermitian, and its basis-index graph is connected.
In particular, a singleton zero Hamiltonian is allowed. -/
def PathConnectedHamiltonian {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℂ) : Prop :=
  H.IsHermitian ∧ (indexGraph H).Connected

/-- PDF p.26: augmented Pauli Z eigenvalue labels; none is Z_0=I and
some i is Z_(i+1). The frozen pauliLabel instead selects Pauli matrices and
cannot represent this eigenvalue map.
The extra identity coordinate does not change ordinary bit-string indexing. -/
def augmentedZLabel {n : ℕ} (x : Qubits n) : Option (Fin n) → ℝ
  | none => 1
  | some i => if x i then -1 else 1

/-- PDF p.26: all second-order augmented labels, including identity and
first-order labels as the entries with an index 0. -/
def quadraticPauliLabel {n : ℕ} (x : Qubits n) :
    Option (Fin n) × Option (Fin n) → ℝ :=
  fun p => augmentedZLabel x p.1 * augmentedZLabel x p.2

/-- PDF pp.7,26: every independently variable real quadratic Z Hamiltonian.
This is a control family, not a fixed cost Hamiltonian. -/
def qaoaControls (n : ℕ) : Set (Matrix (Qubits n) (Qubits n) ℂ) :=
  Set.range (fun beta : Option (Fin n) × Option (Fin n) → ℝ =>
    Matrix.diagonal (fun x =>
      ((∑ p, beta p * quadraticPauliLabel x p : ℝ) : ℂ)))

/-- PDF pp.6,21,26: finite products of the listed matrix exponentials.
Submonoid.closure is algebraic: its elements have finite words. When the
Hamiltonian set is real-linear, negative controls supply all inverses. -/
def evolutionGroup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Set (Matrix ι ι ℂ)) : Submonoid (Matrix ι ι ℂ) :=
  Submonoid.closure {U | ∃ H ∈ S, U = NormedSpace.exp (-Complex.I • H)}

/-- PDF pp.7,26: the fixed mixer has arbitrary real evolution times. -/
def generalizedQaoaGroup {n : ℕ} (H : Matrix (Qubits n) (Qubits n) ℂ) :
    Submonoid (Matrix (Qubits n) (Qubits n) ℂ) :=
  evolutionGroup (qaoaControls n ∪ Set.range (fun t : ℝ => t • H))

example {n : ℕ} (x : Qubits n) : augmentedZLabel x none = 1 := rfl

example {n : ℕ} (x : Qubits n) (j : Option (Fin n)) :
    quadraticPauliLabel x (none, j) = augmentedZLabel x j := by
  simp [quadraticPauliLabel, augmentedZLabel]

example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Set (Matrix ι ι ℂ)) : 1 ∈ evolutionGroup S :=
  (evolutionGroup S).one_mem

/-- PDF pp.12,18: lift a one-site operator to a named qudit, fixing other sites.
The alphabet is Fin d, matching the frozen physical tensor-permutation action.
The accepted qubit-only siteOperator uses integer bit indices and is not this
general-qudit named-wire matrix. -/
def quditSiteMatrix {d n : ℕ} (i : Fin n) (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  Matrix.of (fun x y => if ∀ j, j ≠ i → x j = y j then A (x i) (y i) else 0)

/-- PDF p.12: one-half of the specified Pauli operator on a named site.
finTwoEquiv identifies Fin 2 symbols 0,1 with false,true. -/
def spinOperator {n : ℕ} (i : Fin n) (A : Matrix Bool Bool ℂ) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  (1 / 2 : ℂ) • quditSiteMatrix i (Matrix.of (fun a b => A (finTwoEquiv a) (finTwoEquiv b)))

/-- PDF pp.12,18: the actual three-component spin-half exchange product. -/
def spinDot {n : ℕ} (i j : Fin n) : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  spinOperator i pauliX * spinOperator j pauliX +
  spinOperator i pauliY * spinOperator j pauliY +
  spinOperator i pauliZ * spinOperator j pauliZ

/-- PDF pp.9–10: normalized antisymmetric pair, embedded in any alphabet. -/
def pairAmplitude {d : ℕ} (x y : Fin d) : ℂ :=
  if x.val = 0 ∧ y.val = 1 then ((Real.sqrt 2)⁻¹ : ℂ)
  else if x.val = 1 ∧ y.val = 0 then -((Real.sqrt 2)⁻¹ : ℂ) else 0

/-- PDF p.9, Eq.(5): k zeros followed by b disjoint singlets; n=k+2b. -/
def singletInitialization (k b : ℕ) : EuclideanSpace ℂ (Fin (k + 2*b) → Fin 2) :=
  WithLp.toLp 2 (fun x =>
    (if ∀ i : Fin k, x ⟨i.val, by omega⟩ = 0 then 1 else 0) *
      ∏ j : Fin b,
        pairAmplitude (x ⟨k + 2*j.val, by omega⟩) (x ⟨k + 2*j.val + 1, by omega⟩))

/-- PDF pp.9–10: the unique two-row shape, with no truncated division. -/
def twoRowDiagram (k b : ℕ) : YoungDiagram :=
  YoungDiagram.ofRowLens [k+b, b] (by simp [List.sortedGE_iff_pairwise] <;> omega)

/-- A total adapter to the frozen full physical isotypic projector. On an invalid
size/height diagram it is zero; every initialization statement below uses a
size-correct, height-bounded diagram. It never selects an embedded Specht copy.
The frozen cellular-JM shapeProjector is a different abstract algebra object. -/
def physicalShapeProjector (d n : ℕ) (lambda : YoungDiagram) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  if h : lambda.card = n ∧ lambda.colLen 0 ≤ d then isotypicProjector ⟨lambda, h⟩
  else 0

/-- PDF pp.3,9: M^mu is the coordinate subspace spanned by all words with
occupation vector mu. This is not one chosen irreducible summand of that space. -/
def occupationModule {d n : ℕ} (mu : Fin d → ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n → Fin d)) :=
  Submodule.span ℂ {v | ∃ x : Fin n → Fin d,
    (∀ a, (Finset.univ.filter (fun i => x i = a)).card = mu a) ∧ v = ket x}

/-- PDF p.10: the normalized SU(3) determinant singlet, in the exact printed
order uds−usd+dsu−dus+sud−sdu. -/
def tripleAmplitude (x y z : Fin 3) : ℂ :=
  ((Real.sqrt 6)⁻¹ : ℂ) *
    ((if (x,y,z) = (0,1,2) then 1 else 0) -
     (if (x,y,z) = (0,2,1) then 1 else 0) +
     (if (x,y,z) = (1,2,0) then 1 else 0) -
     (if (x,y,z) = (1,0,2) then 1 else 0) +
     (if (x,y,z) = (2,0,1) then 1 else 0) -
     (if (x,y,z) = (2,1,0) then 1 else 0))

/-- PDF p.10: a singles, b normalized pairs, c normalized determinant triples,
on a+2b+3c physical sites. -/
def su3Initialization (a b c : ℕ) :
    EuclideanSpace ℂ (Fin (a+2*b+3*c) → Fin 3) :=
  WithLp.toLp 2 (fun x =>
    (if ∀ i : Fin a, x ⟨i.val, by omega⟩ = 0 then 1 else 0) *
    (∏ j : Fin b,
      pairAmplitude (x ⟨a+2*j.val, by omega⟩) (x ⟨a+2*j.val+1, by omega⟩)) *
    ∏ j : Fin c,
      tripleAmplitude (x ⟨a+2*b+3*j.val, by omega⟩)
        (x ⟨a+2*b+3*j.val+1, by omega⟩) (x ⟨a+2*b+3*j.val+2, by omega⟩))

/-- PDF p.10 with the forced site-count correction: (a+b+c,b+c,c).
Printed (n+k+l,n−k+l,l) must read ((n+k)/2+l,(n−k)/2+l,l)
when n=a+2b and k=a. The printed shape has too many boxes. -/
def threeRowDiagram (a b c : ℕ) : YoungDiagram :=
  YoungDiagram.ofRowLens [a+b+c, b+c, c] (by simp [List.sortedGE_iff_pairwise] <;> omega)

/-- PDF pp.2,9–10: tensor normalized antisymmetric states on the columns of
lambda. The frozen cell numbering determines placement. Column permutations
act on the frozen row-word; distinct permutations give distinct basis words. -/
def columnInitialization {d n : ℕ} (lambda : Partition d n) :
    EuclideanSpace ℂ (Fin n → Fin d) :=
  ((Real.sqrt ((columnPermutations lambda).card : ℝ))⁻¹ : ℂ) •
    ∑ pi ∈ columnPermutations lambda,
      ((((Equiv.Perm.sign pi : ℤˣ) : ℤ) : ℂ)) •
        act (tensorPermutation d n pi) (ket (highestWeightWord lambda))

/-- A named-wire qudit gate in the continuous one- and two-qudit model used for the
constant-depth claim, PDF pp.2,9–10. Arbitrary wire pairs are allowed. -/
structure PreparationGate (d n : ℕ) where
  support : Finset (Fin n)
  arity : support.card ≤ 2
  unitary : Matrix.unitaryGroup (support → Fin d) ℂ

/-- Lift an operator on a fixed subset, acting identically elsewhere. -/
def liftSupported {d n : ℕ} (S : Finset (Fin n))
    (A : Matrix (S → Fin d) (S → Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  Matrix.of (fun x y => if ∀ i, i ∉ S → x i = y i
    then A (fun i => x i.val) (fun i => y i.val) else 0)

/-- PDF pp.2,9–10: layers have pairwise disjoint supports; depth is their count.
The gate matrices carry their own unitarity, not an unrelated cost witness. -/
structure PreparationCircuit (d n : ℕ) where
  layers : List (List (PreparationGate d n))
  disjoint : ∀ layer ∈ layers,
    layer.Pairwise (fun g h => Disjoint g.support h.support)

/-- Layers are listed in chronological order and multiply on the left. -/
def preparationMatrix {d n : ℕ} (C : PreparationCircuit d n) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  C.layers.foldl (fun U layer =>
    (layer.map (fun g => liftSupported g.support (g.unitary : Matrix _ _ ℂ))).prod * U) 1

example : pairAmplitude (0 : Fin 2) 0 = 0 := by simp [pairAmplitude]

example : pairAmplitude (0 : Fin 2) 1 = ((Real.sqrt 2)⁻¹ : ℂ) := by
  simp [pairAmplitude]

example : tripleAmplitude 0 0 0 = 0 := by simp [tripleAmplitude]

example (n : ℕ) : preparationMatrix
    ({ layers := [], disjoint := by simp } : PreparationCircuit 2 n) = 1 := rfl

/-- PDF p.3: the collective action g tensor n, computed in the physical basis. -/
def collectiveAction (d n : ℕ) (g : Matrix.specialUnitaryGroup (Fin d) ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  Matrix.of (fun x y => ∏ i, (g : Matrix (Fin d) (Fin d) ℂ) (x i) (y i))

/-- PDF pp.23–24: SU(d) symmetry refers to the actual collective group action.
The frozen rational-permutation-submodule IsInvariant is a different predicate. -/
def CollectivelyInvariant {d n : ℕ} (H : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) : Prop :=
  ∀ g : Matrix.specialUnitaryGroup (Fin d) ℂ,
    H * collectiveAction d n g = collectiveAction d n g * H

/-- PDF p.24: each Hamiltonian is supported on one fixed subset of at most k
sites. Different Hamiltonians may choose different subsets. -/
def localInvariantHamiltonians (d n k : ℕ) :
    Set (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :=
  {H | H.IsHermitian ∧ CollectivelyInvariant H ∧
    ∃ S : Finset (Fin n), S.card ≤ k ∧
      ∃ A : Matrix (S → Fin d) (S → Fin d) ℂ, H = liftSupported S A}

/-- PDF p.24: V_k, exact finite products of fixed-support invariant evolutions. -/
def invariantLocalGroup (d n k : ℕ) :
    Submonoid (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :=
  evolutionGroup (localInvariantHamiltonians d n k)

/-- PDF p.24: V'_k allows finite real sums with different supports before
exponentiation. This is a real span of the concrete local Hermitian operators. -/
def invariantLocalSumGroup (d n k : ℕ) :
    Submonoid (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :=
  evolutionGroup (Submodule.span ℝ (localInvariantHamiltonians d n k) :
    Set (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ))

example (d : ℕ) (g : Matrix.specialUnitaryGroup (Fin d) ℂ) :
    collectiveAction d 0 g = 1 := by
  ext x y
  simp [collectiveAction, Matrix.one_apply, Subsingleton.elim x y]

/-- PDF p.3: the actual linear extension of the physical permutation action. -/
def physicalAlgebraMatrix (d n : ℕ) (f : Equiv.Perm (Fin n) → ℂ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ∑ g, f g • tensorPermutation d n g

/-- PDF pp.3,19,24: the matrix of the actual regular-ideal Specht action.
Any fixed orthonormal coordinates suffice for a determinant: these coordinates
are deliberately not claimed to be Young or sequential CG coordinates. -/
def spechtAlgebraMatrix {d n : ℕ} (lambda : Partition d n)
    (f : Equiv.Perm (Fin n) → ℂ) :
    Matrix (Fin (Module.finrank ℂ (spechtSpace lambda)))
      (Fin (Module.finrank ℂ (spechtSpace lambda))) ℂ :=
  let b := stdOrthonormalBasis ℂ (spechtSpace lambda)
  ∑ g, f g • LinearMap.toMatrix b.toBasis b.toBasis (spechtRepresentation lambda g)

/-- PDF p.24: SV_k imposes determinant one on each nonrepeated Specht block.
The coefficient function represents U through the concrete physical action and
also computes all Specht blocks; no arbitrary unrelated block matrices occur.
Only physical height-bounded shapes are tested. -/
def specialInvariantLocalGroup (d n k : ℕ) :
    Set (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :=
  {U | U ∈ invariantLocalGroup d n k ∧
    ∃ f : Equiv.Perm (Fin n) → ℂ, physicalAlgebraMatrix d n f = U ∧
      ∀ lambda : Partition d n, (spechtAlgebraMatrix lambda f).det = 1}

/-- PDF pp.4–5: the original physical X_(k+1), with X_1=0. -/
def originalYjm (d n : ℕ) (k : Fin n) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => j < k),
    tensorPermutation d n (Equiv.swap j k)

/-- PDF pp.6,23: only in the CQA control family, replace X_1 by I. -/
def cqaYjm (d n : ℕ) (k : Fin n) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  if k.val = 0 then 1 else originalYjm d n k

/-- PDF pp.6,23: real independently variable augmented quadratic controls. -/
def quadraticPhysicalControls (d n : ℕ) :
    Set (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :=
  Set.range (fun beta : Fin n × Fin n → ℝ =>
    ∑ p, (beta p : ℂ) • (cqaYjm d n p.1 * cqaYjm d n p.2))

/-- PDF p.24: the open-chain adjacent-SWAP Hamiltonian, with no (1,n) term. -/
def adjacentSwapHamiltonian (d n : ℕ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ∑ i : Fin n, if h : i.val + 1 < n then
    tensorPermutation d n (Equiv.swap i ⟨i.val+1, h⟩) else 0

/-- PDF pp.7,24: the simultaneous-sector CQA group used in four-locality,
with its fixed open-chain mixer H_S, not an arbitrary H_P. -/
def physicalCqaGroup (d n : ℕ) :
    Submonoid (Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) :=
  evolutionGroup (quadraticPhysicalControls d n ∪
    Set.range (fun t : ℝ => t • adjacentSwapHamiltonian d n))

example (d : ℕ) : cqaYjm d 1 0 = 1 := by simp [cqaYjm]

example (d : ℕ) : originalYjm d 1 0 = 0 := by simp [originalYjm]

example (d : ℕ) : adjacentSwapHamiltonian d 1 = 0 := by
  simp [adjacentSwapHamiltonian]

end QAlgorithms.Papers.Independent.Extend50.P10


