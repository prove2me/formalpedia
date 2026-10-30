-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P50
-- name    : QAlgorithms_Papers_Independent_Advance50_P50
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T11:03:33.334203+00:00
-- url     : https://prove2.me/theorems/575d791d-1957-4534-b945-5af9afa22844
-- title:
--   Definitions for Group-Invariant Quantum Machine Learning
-- statement:
--   The objects the formalized statements of *Group-Invariant Quantum Machine Learning* (arXiv:2205.02261) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `tensorFactors`: PDF p.5: independent tensor factors, in the displayed order.
--   - `ExpectationModel`: PDF p.3, Hypothesis Class 1: fixed input-independent unitary and Hermitian observable. A parameter value theta is fixed by choosing this model.
--   - `ExpectationModel.effective`: PDF p.5, Eq.(6): effective observable, computed from the model.
--   - `ExpectationModel.response`: PDF p.3, Eq.(2): the real exact expectation of the fixed model.
--   - `groupMatrices`: PDF pp.2–3: matrices of a specified subgroup of the unitary group.
--   - `DomainInvariant`: PDF p.3, Definition 1: invariance is relative to a declared data domain.
--   - `DatasetSymmetry`: PDF pp.2–3: all data are density matrices; the group preserves the data and their labels. The label map is only constrained on the data domain.
--   - `tensorCommutant`: PDF p.5, Definition 5: complex matrices commuting with every tensor power. The accepted ordinary matrix commutant is applied to the tensor-power image; no Hermiticity restriction is imposed.
--   - `tangentAtIdentity`: PDF p.5: the actual tangent space at identity, described by derivatives of curves in the represented group, rather than the false rule exp(g)=G.
--   - `MatrixLieData`: PDF p.5 and Appendix B: a matrix Lie group with its actual real tangent Lie algebra. The tangent identification prevents an unrelated algebra from being supplied. Skew-Hermiticity is the unitary Lie algebra convention.
--   - `lieComplement`: PDF p.5, Definition 6: Hilbert–Schmidt orthogonal complement inside u(d), which is a real vector space and need not be a Lie algebra.
--   - `timesI`: PDF p.5: multiplication by i identifies skew-Hermitian and Hermitian spaces.
--   - `slotFactor`: PDF pp.5,23–24: place A on copy j, B on the remaining copies in their original order. The subtype of all indices except j is the explicit reindexing.
--   - `separatedSpan`: PDF p.5, Proposition 2: the span of the specified k separated terms, with one prescribed A_j and complementary-copy operator B_j for each j.
--   - `inputLieSpace`: PDF pp.5–6: select the algebra or its complement for an input domain. This implements the explicitly stated interchangeable cases in Propositions 2,4.
--   - `purityDomain`: PDF p.6, Eq.(8): the full pure versus fixed-b mixed data domain.
--   - `SeparatesPurity`: PDF p.4, Definition 4: exact expectations separate every opposite-label pair.
--   - `copySwap`: PDF p.8: swap the two complete registers.
--   - `printedBell`: PDF p.10, literal Eq.(22): this is an unnormalized vector, with amplitude 1/d, not 1/sqrt(d). It is never used as a unit quantum state.
--   - `orthogonalMatrices`: PDF pp.9–10: orthogonal matrices in the fixed basis, represented as real unitaries.
--   - `localUnitaryMatrices`: PDF pp.12–14: the local unitary action, with the same local gate applied across copies only when its tensor power is subsequently taken.
--   - `localPermutation`: PDF p.14, Eq.(39): physical copy permutations independently at each site. This formula performs the copy/site shuffle explicitly and retains all kernels.
--   - `pairedSiteProduct`: PDF pp.13–14: tensor product of two-copy site operators, returned to copy-major order by the explicit coordinate map (c,j) ↦ (j,c).
--   - `subsystemSwap`: PDF pp.13–14: swap just the sites in Q, and identity on its complement.
--   - `FullyProduct`: PDF pp.12–14: full separability for a pure state, rather than separability across just one bipartition.
--   - `EntanglementMeasure`: PDF p.12, Eq.(29): the stated local-unitary-invariant entanglement measure.
--   - `entanglementDomain`: PDF p.12, Eq.(29): pure states in the zero or fixed-positive-E class.
--   - `globalImpurityObservable`: PDF p.13, Eq.(35): the averaged single-site impurity observable.
--   - `concentratableObservable`: PDF p.14, Eq.(37): literal tensor product of I+SWAP on Q, identity elsewhere.
--   - `sitePermutation`: PDF p.15: the physical permutation of site registers.
--   - `sitePermutationMatrices`: PDF p.15: all site permutations as a represented group action.
--   - `collectiveSpan`: PDF p.15, Eq.(43): span of the full set of collective one-qubit unitaries.
--   - `siteEmbedding`: PDF p.15, Eq.(41), and Appendix G p.29: embed a one-qubit operator on a specified site and identity on every other site. Reuse the accepted Fin-indexed site operator through the frozen bitstring/index equivalence.
--   - `graphHamiltonian`: PDF pp.14–15, Eq.(41): unordered edges occur once, via i<j.
--   - `graphEvolution`: PDF pp.14–15, Eqs.(40)–(41): the actual Ising graph evolution, sign -itH.
--   - `graphEncoding`: PDF p.14, Eq.(40): encode a graph by conjugating the fixed fiduciary density.
--   - `composeLayers`: PDF p.16, Eq.(44): the constructed composition of consecutive maps.
--   - `AncillaModel`: PDF p.25, Hypothesis Class 3: only an ancilla observable is measured.
--   - `AncillaModel.effective`: PDF p.25, Eq.(D1): the effective ancilla-only measurement.
--   - `AncillaModel.response`: PDF p.25, Eq.(D1): ancilla |0>, followed by two identical data copies.
--   - `swapTestMatrix`: PDF p.25: the constructed controlled-SWAP test H-CSWAP-H.
--   - `cnot3`: PDF p.26, Fig.1: a CNOT on named wires; wire 0 is the ancilla.
--   - `runGates`: PDF p.26, Fig.1: evaluate the printed gate list in chronological order.
--   - `circuit1`: PDF p.26, Fig.1(a): the complete printed native-gate SWAP-test circuit. Simultaneous gates on different wires are ordered ancilla first.
--   - `circuitW`: PDF p.26, Fig.1(b): W=T†H as specified in the caption.
--   - `circuit2`: PDF p.26, Fig.1(b): the complete printed circuit from Ref.[61].
--   - `targetObservable3`: PDF p.26, Eq.(D4): Z on the ancilla times SWAP on the two data qubits.
--   - `ancillaRealignment`: PDF p.26: realignment across the ancilla/data operator bipartition. Rows index ancilla output/input; columns index data output/input. The accepted realignment is transported through Fin.cons with each paired index reversed.
--   - `operatorSchmidtRank`: PDF p.26: operator Schmidt rank is the rank of the realigned matrix, not the rank of U or the Schmidt rank of an output state.
--   - `LocallyEquivalent`: PDF p.26: left and right local unitary equivalence across ancilla/data.
--   - `posteriorAt`: PDF pp.26–27, Lemma 2: posterior class-0 probability at the atom X=c, with equal class priors. Each measure is the conditional sampling law in its class. The factors 1/2 cancel; no density at a point is used.
--   - `haarOutput`: PDF p.28, Eq.(F2): finite-index Haar unitary transported to the frozen bitstring basis using the accepted most-significant-bit convention.
--   - `qgcnnGenerator`: PDF p.29, Eq.(G3), adapted from Ref.[32]: tied real parameters and the same Hermitian one-site operators at every site. Each unordered edge is counted once.
-- source:
--   Group-Invariant Quantum Machine Learning, arXiv:2205.02261v2, https://arxiv.org/abs/2205.02261v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P38
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P03
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

/-!
Statements from Larocca et al., arXiv:2205.02261v2 (2022).
All page numbers are PDF pages. New definitions are confined to this paper.
Copy-major basis: `Fin k → Qubits n`; a site's k bits are obtained by transposing
these two finite indices, without changing their order. Predictions are exact
expectations, not individual measurement outcomes. See HARD.md for deferred claims.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Advance50.P50

open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate ENNReal

-- Exact accepted primitives; no paper-local redeclarations.
open QAlgorithms.Papers.Independent.Information100.P63 (Mat tensorPower)
open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)
open QAlgorithms.Papers.Independent.Gap48.P38 (subsystemReduction)
open QAlgorithms.Papers.Independent.Information100.P32 (purity)
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

-- Matrices carry the associative commutator bracket X*Y-Y*X.
attribute [local instance 100] LieRing.ofAssociativeRing

/-- PDF p.5: independent tensor factors, in the displayed order. -/
def tensorFactors {I : Type*} {k : ℕ} (A : Fin k → Mat I) : Mat (Copies I k) :=
  fun x y => ∏ c, A c (x c) (y c)

/-- PDF p.3, Hypothesis Class 1: fixed input-independent unitary and Hermitian
observable. A parameter value theta is fixed by choosing this model. -/
structure ExpectationModel (I : Type*) [Fintype I] [DecidableEq I] (k : ℕ) where
  unitary : Matrix.unitaryGroup (Copies I k) ℂ
  observable : Mat (Copies I k)
  hermitian : observable.IsHermitian

/-- PDF p.5, Eq.(6): effective observable, computed from the model. -/
def ExpectationModel.effective {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ}
    (M : ExpectationModel I k) : Mat (Copies I k) :=
  (M.unitary : Mat (Copies I k)).conjTranspose * M.observable * M.unitary

/-- PDF p.3, Eq.(2): the real exact expectation of the fixed model. -/
def ExpectationModel.response {I : Type*} [Fintype I] [DecidableEq I] {k : ℕ}
    (M : ExpectationModel I k) (rho : Mat I) : ℝ :=
  ((M.unitary : Mat (Copies I k)) * tensorPower k rho *
    (M.unitary : Mat (Copies I k)).conjTranspose * M.observable).trace.re

/-- PDF pp.2–3: matrices of a specified subgroup of the unitary group. -/
def groupMatrices {I : Type*} [Fintype I] [DecidableEq I]
    (G : Subgroup (Matrix.unitaryGroup I ℂ)) : Set (Mat I) :=
  {V | ∃ u : Matrix.unitaryGroup I ℂ, u ∈ G ∧ (u : Mat I) = V}

/-- PDF p.3, Definition 1: invariance is relative to a declared data domain. -/
def DomainInvariant {I : Type*} [Fintype I] (G R : Set (Mat I)) (h : Mat I → ℝ) : Prop :=
  ∀ V ∈ G, ∀ rho ∈ R, h (conjSuperop V rho) = h rho

/-- PDF pp.2–3: all data are density matrices; the group preserves the data
and their labels. The label map is only constrained on the data domain. -/
def DatasetSymmetry {I : Type*} [Fintype I] (G R : Set (Mat I))
    (label : Mat I → Bool) : Prop :=
  (∀ rho ∈ R, IsDensityMatrix rho) ∧
  ∀ V ∈ G, ∀ rho ∈ R, conjSuperop V rho ∈ R ∧ label (conjSuperop V rho) = label rho

/-- PDF p.5, Definition 5: complex matrices commuting with every tensor power.
The accepted ordinary matrix commutant is applied to the tensor-power image;
no Hermiticity restriction is imposed. -/
def tensorCommutant {I : Type} [Fintype I] (k : ℕ) (G : Set (Mat I)) :
    Set (Mat (Copies I k)) :=
  by
    classical
    exact QAlgorithms.Papers.Independent.Next46.P23.matrixCommutant ((tensorPower k) '' G)

/-- PDF p.5: the actual tangent space at identity, described by derivatives
of curves in the represented group, rather than the false rule exp(g)=G. -/
def tangentAtIdentity {I : Type*} [Fintype I] [DecidableEq I]
    (G : Subgroup (Matrix.unitaryGroup I ℂ)) : Set (Mat I) :=
  {X | ∃ c : ℝ → Mat I, c 0 = 1 ∧
    (∀ t, c t ∈ groupMatrices G) ∧ HasDerivAt c X 0}

/-- PDF p.5 and Appendix B: a matrix Lie group with its actual real tangent
Lie algebra. The tangent identification prevents an unrelated algebra from
being supplied. Skew-Hermiticity is the unitary Lie algebra convention. -/
structure MatrixLieData (I : Type*) [Fintype I] [DecidableEq I] where
  group : Subgroup (Matrix.unitaryGroup I ℂ)
  algebra : LieSubalgebra ℝ (Mat I)
  actualTangent : (algebra : Set (Mat I)) = tangentAtIdentity group
  skew : ∀ X : Mat I, X ∈ algebra → X.conjTranspose = -X

/-- PDF p.5, Definition 6: Hilbert–Schmidt orthogonal complement inside u(d),
which is a real vector space and need not be a Lie algebra. -/
def lieComplement {I : Type*} [Fintype I] [DecidableEq I]
    (L : MatrixLieData I) : Set (Mat I) :=
  {X | X.conjTranspose = -X ∧ ∀ Y ∈ L.algebra, (X.conjTranspose * Y).trace = 0}

/-- PDF p.5: multiplication by i identifies skew-Hermitian and Hermitian spaces. -/
def timesI {I : Type*} (S : Set (Mat I)) : Set (Mat I) :=
  (fun X => Complex.I • X) '' S

/-- PDF pp.5,23–24: place A on copy j, B on the remaining copies in their
original order. The subtype of all indices except j is the explicit reindexing. -/
def slotFactor {I : Type*} {k : ℕ} (j : Fin k) (A : Mat I)
    (B : Mat ({c : Fin k // c ≠ j} → I)) : Mat (Copies I k) :=
  fun x y => A (x j) (y j) * B (fun c => x c.1) (fun c => y c.1)

/-- PDF p.5, Proposition 2: the span of the specified k separated terms,
with one prescribed A_j and complementary-copy operator B_j for each j. -/
def separatedSpan {I : Type*} {k : ℕ} (A : Fin k → Mat I)
    (B : (j : Fin k) → Mat ({c : Fin k // c ≠ j} → I)) :
    Submodule ℂ (Mat (Copies I k)) :=
  Submodule.span ℂ (Set.range (fun j => slotFactor j (A j) (B j)))

/-- PDF pp.5–6: select the algebra or its complement for an input domain.
This implements the explicitly stated interchangeable cases in Propositions 2,4. -/
def inputLieSpace {I : Type*} [Fintype I] [DecidableEq I]
    (L : MatrixLieData I) (complementary : Bool) : Set (Mat I) :=
  if complementary then lieComplement L else (L.algebra : Set (Mat I))

/-- PDF p.6, Eq.(8): the full pure versus fixed-b mixed data domain. -/
def purityDomain {I : Type*} [Fintype I] (b : ℝ) : Set (Mat I) :=
  {rho | IsDensityMatrix rho ∧ (purity rho = 1 ∨ purity rho = b)}

/-- PDF p.4, Definition 4: exact expectations separate every opposite-label pair. -/
def SeparatesPurity {I : Type*} [Fintype I] (b : ℝ) (h : Mat I → ℝ) : Prop :=
  ∀ rho sigma : Mat I, IsDensityMatrix rho → IsDensityMatrix sigma →
    purity rho = 1 → purity sigma = b → h rho ≠ h sigma

/-- PDF p.8: swap the two complete registers. -/
def copySwap (I : Type*) [DecidableEq I] : Mat (Copies I 2) :=
  fun y x => if y 0 = x 1 ∧ y 1 = x 0 then 1 else 0

/-- PDF p.10, literal Eq.(22): this is an unnormalized vector, with amplitude
1/d, not 1/sqrt(d). It is never used as a unit quantum state. -/
def printedBell (n : ℕ) : EuclideanSpace ℂ (Copies (Qubits n) 2) :=
  WithLp.toLp 2 fun x => if x 0 = x 1 then ((2 : ℂ) ^ n)⁻¹ else 0

/-- PDF pp.9–10: orthogonal matrices in the fixed basis, represented as real unitaries. -/
def orthogonalMatrices (n : ℕ) : Set (Mat (Qubits n)) :=
  {V | V ∈ Matrix.unitaryGroup (Qubits n) ℂ ∧ ∀ x y, (V x y).im = 0}

/-- PDF pp.12–14: the local unitary action, with the same local gate applied
across copies only when its tensor power is subsequently taken. -/
def localUnitaryMatrices (n : ℕ) : Set (Mat (Qubits n)) :=
  {V | ∃ u : Fin n → Matrix.unitaryGroup Bool ℂ,
    V = fun x y => ∏ j, (u j : Mat Bool) (x j) (y j)}

/-- PDF p.14, Eq.(39): physical copy permutations independently at each site.
This formula performs the copy/site shuffle explicitly and retains all kernels. -/
def localPermutation (n k : ℕ) (p : Fin n → Equiv.Perm (Fin k)) :
    Mat (Copies (Qubits n) k) :=
  fun y x => if y = (fun c j => x ((p j).symm c) j) then 1 else 0

/-- PDF pp.13–14: tensor product of two-copy site operators, returned to
copy-major order by the explicit coordinate map (c,j) ↦ (j,c). -/
def pairedSiteProduct {n : ℕ} (F : Fin n → Mat (Copies Bool 2)) :
    Mat (Copies (Qubits n) 2) :=
  fun x y => ∏ j, F j (fun c => x c j) (fun c => y c j)

/-- PDF pp.13–14: swap just the sites in Q, and identity on its complement. -/
def subsystemSwap {n : ℕ} (Q : Finset (Fin n)) : Mat (Copies (Qubits n) 2) :=
  pairedSiteProduct fun j => if j ∈ Q then copySwap Bool else 1

/-- PDF pp.12–14: full separability for a pure state, rather than separability
across just one bipartition. -/
def FullyProduct {n : ℕ} (rho : Mat (Qubits n)) : Prop :=
  ∃ psi : Fin n → EuclideanSpace ℂ Bool,
    (∀ j, IsState (psi j)) ∧ rho = pureDensity (prodState psi)

/-- PDF p.12, Eq.(29): the stated local-unitary-invariant entanglement measure. -/
structure EntanglementMeasure (n : ℕ) where
  value : Mat (Qubits n) → ℝ
  range : ∀ rho, IsPure rho → value rho ∈ Set.Icc 0 1
  invariant : DomainInvariant (localUnitaryMatrices n) {rho | IsPure rho} value
  zero : ∀ rho, IsPure rho → (value rho = 0 ↔ FullyProduct rho)

/-- PDF p.12, Eq.(29): pure states in the zero or fixed-positive-E class. -/
def entanglementDomain {n : ℕ} (E : EntanglementMeasure n) (b : ℝ) :
    Set (Mat (Qubits n)) :=
  {rho | IsPure rho ∧ (E.value rho = 0 ∨ E.value rho = b)}

/-- PDF p.13, Eq.(35): the averaged single-site impurity observable. -/
def globalImpurityObservable (n : ℕ) : Mat (Copies (Qubits n) 2) :=
  ((2 : ℂ) / n) • ∑ j : Fin n, (1 - subsystemSwap {j})

/-- PDF p.14, Eq.(37): literal tensor product of I+SWAP on Q, identity elsewhere. -/
def concentratableObservable {n : ℕ} (Q : Finset (Fin n)) :
    Mat (Copies (Qubits n) 2) :=
  1 - ((2 : ℂ) ^ Q.card)⁻¹ •
    pairedSiteProduct (fun j => if j ∈ Q then 1 + copySwap Bool else 1)

/-- PDF p.15: the physical permutation of site registers. -/
def sitePermutation {n : ℕ} (p : Equiv.Perm (Fin n)) : Mat (Qubits n) :=
  fun y x => if y = x ∘ p.symm then 1 else 0

/-- PDF p.15: all site permutations as a represented group action. -/
def sitePermutationMatrices (n : ℕ) : Set (Mat (Qubits n)) :=
  Set.range (sitePermutation (n := n))

/-- PDF p.15, Eq.(43): span of the full set of collective one-qubit unitaries. -/
def collectiveSpan (n : ℕ) : Submodule ℂ (Mat (Qubits n)) :=
  Submodule.span ℂ {T | ∃ A : Matrix.unitaryGroup Bool ℂ,
    T = fun x y => ∏ j : Fin n, (A : Mat Bool) (x j) (y j)}

/-- PDF p.5: the 0-copy power is the scalar identity, not a zero-dimensional register. -/
example {I : Type*} (A : Mat I) (x y : Copies I 0) : tensorPower 0 A x y = 1 := by
  simp [tensorPower]

/-- PDF p.3: one copy reproduces the original matrix entries. -/
example {I : Type*} (A : Mat I) (x y : Copies I 1) :
    tensorPower 1 A x y = A (x 0) (y 0) := by
  simp [tensorPower]

/-- PDF p.5: the zero observable belongs to the tensorCommutant. -/
example {I : Type} [Fintype I] (k : ℕ) (G : Set (Mat I)) :
    (0 : Mat (Copies I k)) ∈ tensorCommutant k G := by
  intro V hV
  simp

/-- PDF p.8: two copies of |0> are fixed by the swap. -/
example : copySwap Bool (fun _ => false) (fun _ => false) = 1 := by
  simp [copySwap]

/-- PDF p.13: subsystem coordinates retain the actual site, not the first site. -/
example {n : ℕ} (F : Fin n → Mat (Copies Bool 2))
    (x y : Copies (Qubits n) 2) :
    pairedSiteProduct F x y = ∏ j, F j (fun c => x c j) (fun c => y c j) := rfl

/-- PDF p.15, Eq.(41), and Appendix G p.29: embed a one-qubit operator on a
specified site and identity on every other site. Reuse the accepted Fin-indexed
site operator through the frozen bitstring/index equivalence. -/
def siteEmbedding {n : ℕ} (j : Fin n) (A : Mat Bool) : Mat (Qubits n) :=
  fun x y => QAlgorithms.Papers.Independent.Renew46.P24.siteOperator n A j
    (bitsEquivFin n x) (bitsEquivFin n y)

/-- PDF pp.14–15, Eq.(41): unordered edges occur once, via i<j. -/
def graphHamiltonian {n : ℕ} (G : SimpleGraph (Fin n)) : Mat (Qubits n) := by
  classical
  exact (∑ i : Fin n, ∑ j : Fin n,
    if i < j ∧ G.Adj i j then siteEmbedding i pauliZ * siteEmbedding j pauliZ else 0) +
    ∑ i : Fin n, siteEmbedding i pauliX

/-- PDF pp.14–15, Eqs.(40)–(41): the actual Ising graph evolution, sign -itH. -/
def graphEvolution {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℝ) : Mat (Qubits n) :=
  NormedSpace.exp (-(Complex.I * (t : ℂ)) • graphHamiltonian G)

/-- PDF p.14, Eq.(40): encode a graph by conjugating the fixed fiduciary density. -/
def graphEncoding {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℝ)
    (rho : Mat (Qubits n)) : Mat (Qubits n) := conjSuperop (graphEvolution G t) rho

/-- PDF p.16, Eq.(44): the constructed composition of consecutive maps. -/
def composeLayers {A : ℕ → Type*} (f : ∀ j, A j → A (j+1)) :
    (m : ℕ) → A 0 → A m
  | 0 => id
  | m+1 => f m ∘ composeLayers f m

/-- PDF p.25, Hypothesis Class 3: only an ancilla observable is measured. -/
structure AncillaModel (I : Type*) [Fintype I] [DecidableEq I] where
  unitary : Matrix.unitaryGroup (Bool × Copies I 2) ℂ
  observable : Mat Bool
  hermitian : observable.IsHermitian

/-- PDF p.25, Eq.(D1): the effective ancilla-only measurement. -/
def AncillaModel.effective {I : Type*} [Fintype I] [DecidableEq I]
    (M : AncillaModel I) : Mat (Bool × Copies I 2) :=
  (M.unitary : Mat (Bool × Copies I 2)).conjTranspose *
    Matrix.kronecker M.observable (1 : Mat (Copies I 2)) * M.unitary

/-- PDF p.25, Eq.(D1): ancilla |0>, followed by two identical data copies. -/
def AncillaModel.response {I : Type*} [Fintype I] [DecidableEq I]
    (M : AncillaModel I) (rho : Mat I) : ℝ :=
  ((M.unitary : Mat (Bool × Copies I 2)) *
    Matrix.kronecker (pureDensity (ket false)) (tensorPower 2 rho) *
    (M.unitary : Mat (Bool × Copies I 2)).conjTranspose *
    Matrix.kronecker M.observable (1 : Mat (Copies I 2))).trace.re

/-- PDF p.25: the constructed controlled-SWAP test H-CSWAP-H. -/
def swapTestMatrix (I : Type*) [Fintype I] [DecidableEq I] :
    Mat (Bool × Copies I 2) :=
  Matrix.kronecker hadamard (1 : Mat (Copies I 2)) * controlled (copySwap I) *
    Matrix.kronecker hadamard (1 : Mat (Copies I 2))

/-- PDF p.26, Fig.1: a CNOT on named wires; wire 0 is the ancilla. -/
def cnot3 (control target : Fin 3) : Mat (Qubits 3) :=
  fun y x => if y = Function.update x target (xor (x target) (x control)) then 1 else 0

/-- PDF p.26, Fig.1: evaluate the printed gate list in chronological order. -/
def runGates : List (Mat (Qubits 3)) → Mat (Qubits 3)
  | [] => 1
  | g :: gs => runGates gs * g

/-- PDF p.26, Fig.1(a): the complete printed native-gate SWAP-test circuit.
Simultaneous gates on different wires are ordered ancilla first. -/
def circuit1 : Mat (Qubits 3) :=
  runGates [siteEmbedding 0 hadamard, cnot3 1 2, siteEmbedding 1 hadamard,
    cnot3 1 2, siteEmbedding 2 gateT.conjTranspose, cnot3 0 2,
    siteEmbedding 2 gateT, cnot3 1 2, siteEmbedding 2 gateT.conjTranspose,
    cnot3 0 2, siteEmbedding 1 gateT, cnot3 0 1, siteEmbedding 0 gateT,
    siteEmbedding 1 gateT.conjTranspose, cnot3 0 1, siteEmbedding 0 hadamard]

/-- PDF p.26, Fig.1(b): W=T†H as specified in the caption. -/
def circuitW : Mat Bool := gateT.conjTranspose * hadamard

/-- PDF p.26, Fig.1(b): the complete printed circuit from Ref.[61]. -/
def circuit2 : Mat (Qubits 3) :=
  runGates [siteEmbedding 0 circuitW, cnot3 1 2, cnot3 2 0,
    siteEmbedding 0 circuitW.conjTranspose, cnot3 0 1,
    siteEmbedding 0 circuitW, cnot3 2 0, siteEmbedding 0 circuitW.conjTranspose]

/-- PDF p.26, Eq.(D4): Z on the ancilla times SWAP on the two data qubits. -/
def targetObservable3 : Mat (Qubits 3) :=
  fun y x => pauliZ (y 0) (x 0) *
    (if y 1 = x 2 ∧ y 2 = x 1 then 1 else 0)

/-- PDF p.26: realignment across the ancilla/data operator bipartition.
Rows index ancilla output/input; columns index data output/input. The accepted
realignment is transported through Fin.cons with each paired index reversed. -/
def ancillaRealignment (U : Mat (Qubits 3)) :
    Matrix (Bool × Bool) (Qubits 2 × Qubits 2) ℂ :=
  let bipartite : Mat (Bool × Qubits 2) :=
    fun x y => U (Fin.cons x.1 x.2) (Fin.cons y.1 y.2)
  fun a b => QAlgorithms.Papers.Independent.Information100.P03.realignment bipartite
    (a.2, a.1) (b.2, b.1)

/-- PDF p.26: operator Schmidt rank is the rank of the realigned matrix,
not the rank of U or the Schmidt rank of an output state. -/
def operatorSchmidtRank (U : Mat (Qubits 3)) : ℕ :=
  Module.finrank ℂ (LinearMap.range (Matrix.toLin' (ancillaRealignment U)))

/-- PDF p.26: left and right local unitary equivalence across ancilla/data. -/
def LocallyEquivalent (U V : Mat (Qubits 3)) : Prop :=
  ∃ (A C : Matrix.unitaryGroup Bool ℂ) (B D : Matrix.unitaryGroup (Qubits 2) ℂ),
    V = Mul.mul (α := Mat (Qubits 3))
      (Mul.mul (α := Mat (Qubits 3))
        (fun (x y : Qubits 3) => Matrix.kronecker (A : Mat Bool) (B : Mat (Qubits 2))
          (x 0, fun i => x i.succ) (y 0, fun i => y i.succ)) U)
      (fun (x y : Qubits 3) => Matrix.kronecker (C : Mat Bool) (D : Mat (Qubits 2))
        (x 0, fun i => x i.succ) (y 0, fun i => y i.succ))

/-- PDF p.26: a CNOT flips its target when its control is one. -/
example : cnot3 0 1 ![true,true,false] ![true,false,false] = 1 := by
  have h : (![true,true,false] : Qubits 3) =
      Function.update (![true,false,false] : Qubits 3) 1 true := by
    funext i
    fin_cases i <;> simp [Function.update]
  simp [cnot3, h]

/-- PDF p.26: no gates means identity. -/
example : runGates [] = 1 := rfl

/-- PDF pp.26–27, Lemma 2: posterior class-0 probability at the atom X=c,
with equal class priors. Each measure is the conditional sampling law in its
class. The factors 1/2 cancel; no density at a point is used. -/
def posteriorAt {Omega : Type*} [MeasurableSpace Omega]
    (mu0 mu1 : Measure Omega) (X : Omega → ℝ) (c : ℝ) : ℝ :=
  (mu0 {w | X w = c}).toReal /
    ((mu0 {w | X w = c}).toReal + (mu1 {w | X w = c}).toReal)

/-- PDF p.28, Eq.(F2): finite-index Haar unitary transported to the frozen
bitstring basis using the accepted most-significant-bit convention. -/
def haarOutput (n : ℕ) (rho O : Mat (Qubits n))
    (u : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) : ℝ :=
  let V : Mat (Qubits n) := fun x y => (u : Mat (Fin (2^n))) (bitsEquivFin n x) (bitsEquivFin n y)
  (O * conjSuperop V rho).trace.re

/-- PDF p.29, Eq.(G3), adapted from Ref.[32]: tied real parameters and the
same Hermitian one-site operators at every site. Each unordered edge is counted once. -/
def qgcnnGenerator {n a b : ℕ} (G : SimpleGraph (Fin n))
    (W : Fin a → ℝ) (B : Fin b → ℝ) (O : Fin a → Mat Bool) (R : Fin b → Mat Bool) :
    Mat (Qubits n) := by
  classical
  exact (∑ i : Fin n, ∑ j : Fin n, if i < j ∧ G.Adj i j then
    ∑ r : Fin a, (W r : ℂ) • (siteEmbedding i (O r) * siteEmbedding j (O r)) else 0) +
    ∑ v : Fin n, ∑ r : Fin b, (B r : ℂ) • siteEmbedding v (R r)

/-- PDF p.5: a separated term really acts on the requested copy j. -/
example {I : Type*} {k : ℕ} (j : Fin k) (A : Mat I)
    (B : Mat ({c : Fin k // c ≠ j} → I)) (x y : Copies I k) :
    slotFactor j A B x y = A (x j) (y j) *
      B (fun c => x c.1) (fun c => y c.1) := rfl

/-- PDF p.5: multiplying the zero matrix by i does not create a nonzero operator. -/
example {I : Type*} : (0 : Mat I) ∈ timesI ({0} : Set (Mat I)) := by
  exact ⟨0, by simp, by simp⟩

/-- PDF p.15: the identity site permutation is the identity matrix. -/
example (n : ℕ) : sitePermutation (1 : Equiv.Perm (Fin n)) = 1 := by
  ext x y
  rfl

/-- PDF p.16: no intermediate layer leaves the input intact. -/
example {A : ℕ → Type*} (f : ∀ j, A j → A (j+1)) (x : A 0) :
    composeLayers f 0 x = x := rfl

/-- PDF pp.26–27: zero class-0 atom gives zero misclassification posterior. -/
example {Omega : Type*} [MeasurableSpace Omega] (mu0 mu1 : Measure Omega)
    (X : Omega → ℝ) (c : ℝ) (hzero : mu0 {w | X w = c} = 0) :
    posteriorAt mu0 mu1 X c = 0 := by
  simp [posteriorAt, hzero]

end QAlgorithms.Papers.Independent.Advance50.P50


