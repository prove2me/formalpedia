-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P01
-- name    : QAlgorithms_Papers_Independent_Gap20_P01
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T20:10:52.186536+00:00
-- url     : https://prove2.me/theorems/62213d2b-a2de-4470-a192-ae01a9a9057b
-- title:
--   Definitions for Efficient Quantum Circuits for Schur and Clebsch-Gordan Transforms
-- statement:
--   The objects the formalized statements of *Efficient Quantum Circuits for Schur and Clebsch-Gordan Transforms* (arXiv:quant-ph/0407082) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SpinRegister`: PDF p.2, Fig.1: integer register values (twice J, twice m, spin bit). Integer arithmetic is used before restriction to physical labels, so subtraction never truncates. False is physical spin -1/2.
--   - `SpinVector`: PDF p.2, Fig.1: finite linear combinations of logical register kets. These are logical multiwire operations, with no elementary-gate cost assigned.
--   - `spinSign`: PDF p.2: twice the spin carried by the input bit.
--   - `addMagnetic`: PDF p.2, Fig.1, first logical operation: m becomes m+s.
--   - `rotationCos`: PDF pp.2--3, Eq.(6): the two coefficients cos(theta), sin(theta), with both spin and magnetic numbers doubled. Only physical sectors are used by the theorem; the total formula outside them makes no physical claim.
--   - `rotationSin`: PDF pp.2--3, Eq.(6): the nonnegative sine of the source rotation.
--   - `rotateBranch`: PDF pp.2--3, Fig.1: the second logical operation is the J,m'-controlled real rotation [[cos,-sin],[sin,cos]] on the spin/path bit.
--   - `addSpin`: PDF p.2, Fig.1: the third logical operation updates J to J+p. The remaining bit records the lower/upper branch p=-1/2,+1/2.
--   - `qubitCGTarget`: PDF p.2, Eq.(6): independently specified exact CG analysis of one input basis ket, using the accepted add-spin-1/2 coefficients. At j=0 the lower coefficient is zero; its integer address -1 is not a physical output state.
--   - `FiniteIrrep`: PDF p.3: a based complex irrep has positive dimension. Irreducibility is invariance only of the zero and full subspaces, not an orthogonality assumption.
--   - `IrrepEquivalent`: PDF p.3: equivalence of two finite based irreps by inverse intertwiners.
--   - `FiniteDual`: PDF p.3: a complete set of inequivalent irreducible unitary representations. The trivial coefficient is explicitly named to initialize Fig.3. No Schur orthogonality or correctness of the measurement is assumed in this structure.
--   - `FourierLabel`: PDF p.3, Eq.(7): auxiliary Fourier labels, with lambda-dependent row and column ranges, not their unpadded Cartesian overestimate.
--   - `fourierPlus`: PDF p.3, Eq.(7), exactly the printed plus convention.
--   - `fourierMinus`: PDF pp.3--4, explicit correction to Eq.(7): replace g by g^-1. With this convention the measured name is mu rather than its dual, and the alpha and beta locations agree with the intended Eq.(11).
--   - `controlledRep`: PDF p.3, Fig.3: the actual coherently controlled physical representation. Having classically specified circuits for individual R(g) is not this primitive.
--   - `figureThree`: PDF pp.3--4, Fig.3: inverse Fourier transform, controlled R, Fourier transform, in chronological order. The inverse is the adjoint, with no free group-inversion gate. This is a composition of three supplied primitives.
--   - `auxiliaryStart`: PDF pp.3--4, initialization forced by Eq.(10): the trivial Fourier coefficient, whose inverse transform is the normalized uniform group vector.
--   - `ReducingLabel`: PDF pp.3--4, Eq.(8): full reducing labels, including zero multiplicities.
--   - `reducingAction`: PDF p.4, Eq.(9): the representation in its reducing coordinates.
--   - `ReducingBasis`: PDF pp.3--4, Eqs.(8)--(9): an orthonormal reducing basis of R. This is the source's chosen basis, not a hypothesis that the Fig.3 circuit works. Both inverse identities are required: no omitted physical subspace.
--   - `applyRect`: Rectangular matrix action in the fixed Euclidean convention.
--   - `reducingCoefficients`: PDF p.3, Eq.(8): the source coefficients are computed from the actual physical input; they are not independently supplied or assumed.
--   - `auxiliaryFactor`: PDF p.4, last paragraph: an available operation A_mu on the extracted alpha coordinate, controlled by mu, leaving beta alone. Its synthesis cost is not declared free or bounded for arbitrary matrices.
--   - `physicalFactor`: PDF p.4: the corresponding independently defined physical irrep-factor operation, identity on each multiplicity j and A_mu on its irrep coordinate k.
--   - `physicalCode`: PDF p.1: the computational word as a base-d integer, first qudit most significant, using the frozen most-significant-first qubit encoding.
--   - `encodedPhysical`: PDF pp.1--2: physical input embedded in m qubits; unused leading wires are zero when m >= n ceil(log_2 d). The theorem enforces this inequality.
--   - `shapeNumber`: PDF pp.2,4: a fixed padded numeric lambda code, independent of epsilon. The n row lengths are digits in base n+1; rows beyond the height are zero. Thus decoding is ordinary bounded-length positional arithmetic.
--   - `shapeWidth`: Width of the fixed shape register, polynomial in n and independent of d.
--   - `reportsShape`: PDF p.4: a label event is read directly from the leading shape register. The theorem guards the natural subtraction by shapeWidth n <= m.
--   - `invalidShape`: PDF p.4: unused padded output codes are an explicit additional event.
--   - `spechtMatrix`: PDF pp.3--4: any orthonormal coordinates of the Specht representation may be used for the ideal Fourier measurement; the row coordinates are summed out. No circuit efficiency for this arbitrary coordinate choice is asserted.
--   - `idealSchurAmplitude`: PDF pp.3--4, corrected Eq.(10) specialized to R=P. The coefficient is sqrt(dim P_lambda)/|S_n|, including the initial uniform superposition factor.
-- source:
--   Efficient Quantum Circuits for Schur and Clebsch-Gordan Transforms, arXiv:quant-ph/0407082v4, https://arxiv.org/abs/quant-ph/0407082v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P01
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P09

/-!
Bacon--Chuang--Harrow, quant-ph/0407082v4, PDF pp.1--4.
The audited accepted scalar CG formula is imported from Renew46.P01.
Representation and elementary-gate predicates are reused from Support21.P09.
The full general-d compiler and independently coordinated cascade are deferred;
the arbitrary polar-normalized Schur map is not substituted for those targets.
The finite-group statements explicitly correct Eq.(7) by replacing g with g^-1.
-/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexConjugate

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Gap20.P01

open QAlgorithms.Papers.Independent.Support21.P09 (Rep UnitaryRep elementaryGates)

/-- PDF p.2, Fig.1: integer register values (twice J, twice m, spin bit).
Integer arithmetic is used before restriction to physical labels, so subtraction
never truncates. False is physical spin -1/2. -/
abbrev SpinRegister := ℤ × ℤ × Bool

/-- PDF p.2, Fig.1: finite linear combinations of logical register kets.
These are logical multiwire operations, with no elementary-gate cost assigned. -/
abbrev SpinVector := SpinRegister →₀ ℂ

/-- PDF p.2: twice the spin carried by the input bit. -/
def spinSign (b : Bool) : ℤ := if b then 1 else -1

/-- PDF p.2, Fig.1, first logical operation: m becomes m+s. -/
def addMagnetic : SpinVector →ₗ[ℂ] SpinVector :=
  Finsupp.linearCombination ℂ fun x =>
    Finsupp.single (x.1, x.2.1 + spinSign x.2.2, x.2.2) 1

/-- PDF pp.2--3, Eq.(6): the two coefficients cos(theta), sin(theta),
with both spin and magnetic numbers doubled. Only physical sectors are used
by the theorem; the total formula outside them makes no physical claim. -/
def rotationCos (j m : ℤ) : ℝ :=
  Real.sqrt (((j : ℝ) + (m : ℝ) + 1) / (2 * ((j : ℝ) + 1)))

/-- PDF pp.2--3, Eq.(6): the nonnegative sine of the source rotation. -/
def rotationSin (j m : ℤ) : ℝ :=
  Real.sqrt (((j : ℝ) - (m : ℝ) + 1) / (2 * ((j : ℝ) + 1)))

/-- PDF pp.2--3, Fig.1: the second logical operation is the J,m'-controlled
real rotation [[cos,-sin],[sin,cos]] on the spin/path bit. -/
def rotateBranch : SpinVector →ₗ[ℂ] SpinVector :=
  Finsupp.linearCombination ℂ fun x =>
    Finsupp.single (x.1, x.2.1, false)
      (if x.2.2 then -(rotationSin x.1 x.2.1 : ℂ) else (rotationCos x.1 x.2.1 : ℂ)) +
    Finsupp.single (x.1, x.2.1, true)
      (if x.2.2 then (rotationCos x.1 x.2.1 : ℂ) else (rotationSin x.1 x.2.1 : ℂ))

/-- PDF p.2, Fig.1: the third logical operation updates J to J+p.
The remaining bit records the lower/upper branch p=-1/2,+1/2. -/
def addSpin : SpinVector →ₗ[ℂ] SpinVector :=
  Finsupp.linearCombination ℂ fun x =>
    Finsupp.single (x.1 + spinSign x.2.2, x.2.1, x.2.2) 1

/-- PDF p.2, Eq.(6): independently specified exact CG analysis of one input
basis ket, using the accepted add-spin-1/2 coefficients. At j=0 the lower
coefficient is zero; its integer address -1 is not a physical output state. -/
def qubitCGTarget (j : ℕ) (m : ℤ) (b : Bool) : SpinVector :=
  let M := m + spinSign b
  Finsupp.single ((j : ℤ) - 1, M, false)
    (QAlgorithms.Papers.Independent.Renew46.P01.addHalfCG j (j - 1) m M b : ℂ) +
  Finsupp.single ((j : ℤ) + 1, M, true)
    (QAlgorithms.Papers.Independent.Renew46.P01.addHalfCG j (j + 1) m M b : ℂ)

example (j m : ℤ) :
    addMagnetic (Finsupp.single (j, m, false) 1) =
      Finsupp.single (j, m - 1, false) 1 := by
  simp [addMagnetic, spinSign, sub_eq_add_neg]

example (j m : ℤ) :
    addSpin (Finsupp.single (j, m, true) 1) =
      Finsupp.single (j + 1, m, true) 1 := by
  simp [addSpin, spinSign]

/-- PDF p.3: a based complex irrep has positive dimension. Irreducibility is
invariance only of the zero and full subspaces, not an orthogonality assumption. -/
structure FiniteIrrep (G : Type) [Group G] where
  dim : ℕ
  positive : 0 < dim
  rep : Rep G (Fin dim)
  unitary : UnitaryRep rep
  irreducible : ∀ V : Submodule ℂ (Fin dim → ℂ),
    (∀ g v, v ∈ V → (rep g).mulVec v ∈ V) → V = ⊥ ∨ V = ⊤

/-- PDF p.3: equivalence of two finite based irreps by inverse intertwiners. -/
def IrrepEquivalent {G : Type} [Group G] (A B : FiniteIrrep G) : Prop :=
  ∃ T : Matrix (Fin A.dim) (Fin B.dim) ℂ,
  ∃ S : Matrix (Fin B.dim) (Fin A.dim) ℂ,
    T * S = 1 ∧ S * T = 1 ∧ ∀ g, A.rep g * T = T * B.rep g

/-- PDF p.3: a complete set of inequivalent irreducible unitary representations.
The trivial coefficient is explicitly named to initialize Fig.3. No Schur
orthogonality or correctness of the measurement is assumed in this structure. -/
structure FiniteDual (G L : Type) [Group G] where
  irrep : L → FiniteIrrep G
  inequivalent : ∀ a b, a ≠ b → ¬ IrrepEquivalent (irrep a) (irrep b)
  complete : ∀ A : FiniteIrrep G, ∃ a, IrrepEquivalent A (irrep a)
  trivial : L
  trivialDim : (irrep trivial).dim = 1
  trivialEntry : ∀ g i j, (irrep trivial).rep g i j = 1

variable {G L I : Type} [Group G] [Fintype G] [Fintype L]
  [Fintype I]

/-- PDF p.3, Eq.(7): auxiliary Fourier labels, with lambda-dependent row
and column ranges, not their unpadded Cartesian overestimate. -/
abbrev FourierLabel (D : FiniteDual G L) :=
  (a : L) × (Fin (D.irrep a).dim × Fin (D.irrep a).dim)

/-- PDF p.3, Eq.(7), exactly the printed plus convention. -/
def fourierPlus (D : FiniteDual G L) : Matrix (FourierLabel D) G ℂ :=
  fun a g => (Real.sqrt ((D.irrep a.1).dim / (Fintype.card G : ℝ)) : ℂ) *
    (D.irrep a.1).rep g a.2.1 a.2.2

/-- PDF pp.3--4, explicit correction to Eq.(7): replace g by g^-1.
With this convention the measured name is mu rather than its dual, and the
alpha and beta locations agree with the intended Eq.(11). -/
def fourierMinus (D : FiniteDual G L) : Matrix (FourierLabel D) G ℂ :=
  fun a g => (Real.sqrt ((D.irrep a.1).dim / (Fintype.card G : ℝ)) : ℂ) *
    (D.irrep a.1).rep g⁻¹ a.2.1 a.2.2

/-- PDF p.3, Fig.3: the actual coherently controlled physical representation.
Having classically specified circuits for individual R(g) is not this primitive. -/
def controlledRep (R : Rep G I) : Matrix (G × I) (G × I) ℂ :=
  fun x y => if x.1 = y.1 then R x.1 x.2 y.2 else 0

/-- PDF pp.3--4, Fig.3: inverse Fourier transform, controlled R, Fourier
transform, in chronological order. The inverse is the adjoint, with no free
group-inversion gate. This is a composition of three supplied primitives. -/
def figureThree (D : FiniteDual G L) (R : Rep G I) :
    Matrix (FourierLabel D × I) (FourierLabel D × I) ℂ :=
  (fourierMinus D ⊗ₖ (1 : Matrix I I ℂ)) * controlledRep R *
    ((fourierMinus D)ᴴ ⊗ₖ (1 : Matrix I I ℂ))

/-- PDF pp.3--4, initialization forced by Eq.(10): the trivial Fourier
coefficient, whose inverse transform is the normalized uniform group vector. -/
def auxiliaryStart (D : FiniteDual G L) : EuclideanSpace ℂ (FourierLabel D) :=
  ket ⟨D.trivial, (⟨0, (D.irrep D.trivial).positive⟩,
    ⟨0, (D.irrep D.trivial).positive⟩)⟩

/-- PDF pp.3--4, Eq.(8): full reducing labels, including zero multiplicities. -/
abbrev ReducingLabel (D : FiniteDual G L) (multiplicity : L → ℕ) :=
  (a : L) × (Fin (multiplicity a) × Fin (D.irrep a).dim)

/-- PDF p.4, Eq.(9): the representation in its reducing coordinates. -/
def reducingAction (D : FiniteDual G L) (multiplicity : L → ℕ) (g : G) :
    Matrix (ReducingLabel D multiplicity) (ReducingLabel D multiplicity) ℂ :=
  Matrix.blockDiagonal' fun a =>
    (1 : Matrix (Fin (multiplicity a)) (Fin (multiplicity a)) ℂ) ⊗ₖ
      (D.irrep a).rep g

/-- PDF pp.3--4, Eqs.(8)--(9): an orthonormal reducing basis of R.
This is the source's chosen basis, not a hypothesis that the Fig.3 circuit
works. Both inverse identities are required: no omitted physical subspace. -/
structure ReducingBasis (D : FiniteDual G L) (R : Rep G I) where
  multiplicity : L → ℕ
  synthesis : Matrix I (ReducingLabel D multiplicity) ℂ
  columns : synthesisᴴ * synthesis = 1
  spans : synthesis * synthesisᴴ = 1
  intertwines : ∀ g, R g * synthesis =
    synthesis * reducingAction D multiplicity g

/-- Rectangular matrix action in the fixed Euclidean convention. -/
def applyRect {A B : Type} [Fintype B] (M : Matrix A B ℂ)
    (v : EuclideanSpace ℂ B) : EuclideanSpace ℂ A :=
  WithLp.toLp 2 (M.mulVec (WithLp.ofLp v))

/-- PDF p.3, Eq.(8): the source coefficients are computed from the actual
physical input; they are not independently supplied or assumed. -/
def reducingCoefficients (D : FiniteDual G L) (R : Rep G I)
    (B : ReducingBasis D R) (psi : EuclideanSpace ℂ I) :
    EuclideanSpace ℂ (ReducingLabel D B.multiplicity) :=
  applyRect B.synthesisᴴ psi

example (D : FiniteDual G L) (R : Rep G I) (g : G) (i j : I) :
    controlledRep R (g, i) (g, j) = R g i j := by
  simp [controlledRep]

example {A B : Type} [Fintype B] (M : Matrix A B ℂ)
    (v : EuclideanSpace ℂ B) (a : A) :
    applyRect M v a = ∑ b, M a b * v b := rfl

/-- PDF p.4, last paragraph: an available operation A_mu on the extracted
alpha coordinate, controlled by mu, leaving beta alone. Its synthesis cost
is not declared free or bounded for arbitrary matrices. -/
def auxiliaryFactor (D : FiniteDual G L)
    (A : ∀ a, Matrix.unitaryGroup (Fin (D.irrep a).dim) ℂ) :
    Matrix (FourierLabel D) (FourierLabel D) ℂ :=
  Matrix.blockDiagonal' fun a =>
    (A a : Matrix (Fin (D.irrep a).dim) (Fin (D.irrep a).dim) ℂ) ⊗ₖ
      (1 : Matrix (Fin (D.irrep a).dim) (Fin (D.irrep a).dim) ℂ)

/-- PDF p.4: the corresponding independently defined physical irrep-factor
operation, identity on each multiplicity j and A_mu on its irrep coordinate k. -/
def physicalFactor (D : FiniteDual G L) (R : Rep G I)
    (B : ReducingBasis D R)
    (A : ∀ a, Matrix.unitaryGroup (Fin (D.irrep a).dim) ℂ) : Matrix I I ℂ :=
  B.synthesis *
    (Matrix.blockDiagonal' (fun a : L =>
      (1 : Matrix (Fin (B.multiplicity a)) (Fin (B.multiplicity a)) ℂ) ⊗ₖ
        (A a : Matrix (Fin (D.irrep a).dim) (Fin (D.irrep a).dim) ℂ)) :
      Matrix (ReducingLabel D B.multiplicity) (ReducingLabel D B.multiplicity) ℂ) *
    B.synthesisᴴ

/-- PDF p.1: the computational word as a base-d integer, first qudit most
significant, using the frozen most-significant-first qubit encoding. -/
def physicalCode (n d m : ℕ) (x : Fin n → Fin d) : Qubits m :=
  natToBits m (∑ i : Fin n, (x i).val * d ^ (n - 1 - i.val))

/-- PDF pp.1--2: physical input embedded in m qubits; unused leading wires
are zero when m >= n ceil(log_2 d). The theorem enforces this inequality. -/
def encodedPhysical {n d : ℕ} (m : ℕ)
    (psi : EuclideanSpace ℂ (Fin n → Fin d)) : EuclideanSpace ℂ (Qubits m) :=
  ∑ x : Fin n → Fin d, psi x • ket (physicalCode n d m x)

/-- PDF pp.2,4: a fixed padded numeric lambda code, independent of epsilon.
The n row lengths are digits in base n+1; rows beyond the height are zero.
Thus decoding is ordinary bounded-length positional arithmetic. -/
def shapeNumber {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n) : ℕ :=
  ∑ i : Fin n, lambda.val.rowLen i.val * (n + 1) ^ (n - 1 - i.val)

/-- Width of the fixed shape register, polynomial in n and independent of d. -/
def shapeWidth (n : ℕ) : ℕ := n * Nat.clog 2 (n + 1)

/-- PDF p.4: a label event is read directly from the leading shape register.
The theorem guards the natural subtraction by shapeWidth n <= m. -/
def reportsShape {d n : ℕ} (m : ℕ) (lambda : QAlgorithms.Schur.Partition d n)
    (z : Qubits m) : Prop :=
  bitsToNat z / 2 ^ (m - shapeWidth n) = shapeNumber lambda

/-- PDF p.4: unused padded output codes are an explicit additional event. -/
def invalidShape {d n : ℕ} (m : ℕ) (z : Qubits m) : Prop :=
  ∀ lambda : QAlgorithms.Schur.Partition d n, ¬ reportsShape m lambda z

/-- PDF pp.3--4: any orthonormal coordinates of the Specht representation
may be used for the ideal Fourier measurement; the row coordinates are
summed out. No circuit efficiency for this arbitrary coordinate choice is asserted. -/
def spechtMatrix {d n : ℕ} (lambda : QAlgorithms.Schur.Partition d n)
    (g : Equiv.Perm (Fin n)) :
    Matrix (Fin (Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda)))
      (Fin (Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda))) ℂ :=
  fun a b => inner ℂ (stdOrthonormalBasis ℂ (QAlgorithms.Schur.spechtSpace lambda) a)
    (QAlgorithms.Schur.spechtRepresentation lambda g
      (stdOrthonormalBasis ℂ (QAlgorithms.Schur.spechtSpace lambda) b))

/-- PDF pp.3--4, corrected Eq.(10) specialized to R=P. The coefficient is
sqrt(dim P_lambda)/|S_n|, including the initial uniform superposition factor. -/
def idealSchurAmplitude {d n : ℕ} (psi : EuclideanSpace ℂ (Fin n → Fin d))
    (lambda : QAlgorithms.Schur.Partition d n)
    (a b : Fin (Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda)))
    (x : Fin n → Fin d) : ℂ :=
  (Real.sqrt (Module.finrank ℂ (QAlgorithms.Schur.spechtSpace lambda)) /
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ) : ℂ) *
  ∑ g : Equiv.Perm (Fin n), spechtMatrix lambda g⁻¹ a b *
    act (QAlgorithms.Schur.tensorPermutation d n g) psi x

example : shapeWidth 0 = 0 := rfl

example (g : Gate) (hg : g.arity = 1) (hu : g.IsUnitary) :
    g ∈ elementaryGates := by
  exact ⟨Or.inl hg, hu⟩

end QAlgorithms.Papers.Independent.Gap20.P01


