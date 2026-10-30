-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
-- name    : QAlgorithms_Papers_Independent_Extend50_P31
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T22:24:36.714502+00:00
-- url     : https://prove2.me/theorems/24fa6919-f7d2-4ccd-a63b-c52edd609bd8
-- title:
--   Definitions for Structure of irreducibly covariant quantum channels for finite groups
-- statement:
--   The objects the formalized statements of *Structure of irreducibly covariant quantum channels for finite groups* (arXiv:1610.05657) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `EndMat`: PDF pp.4--7: complex-linear endomorphisms on every operator.
--   - `rowVec`: PDF p.4, Eq.(5): row vectorization, also for rectangular matrices.
--   - `rowMatrixRepresentative`: PDF pp.5--6, Eqs.(8),(15): entries in the fixed matrix-unit basis.
--   - `fromMat`: The inverse coordinate representation, acting on every operator.
--   - `IsPaperChannel`: PDF p.8 Definition 7; complete positivity is the frozen all-ancilla definition.
--   - `UnitaryIrrep`: PDF p.7: an ordinary unitary irreducible representation, with positive dimension. Irreducibility means that every complex invariant linear subspace is zero or the whole space.
--   - `RepEquivalent`: PDF p.9: equivalence of representations is an invertible intertwiner.
--   - `IrrepFamily`: PDF pp.9--10: complete, inequivalent, coordinate-fixed unitary irreducibles.
--   - `character`: PDF p.8: character of a fixed-coordinate irrep.
--   - `conjugationMap`: PDF p.7 Eq.(25), conjugation on the full operator space.
--   - `tensorConjugate`: PDF pp.7--8 Eqs.(24),(28): entrywise conjugation on the second tensor factor.
--   - `IsIrrepCovariant`: PDF p.8 Eq.(31), on every operator, without positivity or TP.
--   - `representationCommutant`: PDF p.9 Eq.(36), as an actual complex linear subspace.
--   - `SimplyReducible`: PDF p.11 Eq.(47): an invertible intertwiner to exactly one copy of each listed irrep. This predicate contains no character-projector facts.
--   - `Data`: Only the section's standing assumptions, PDF pp.7--11 and Assumption 1 p.17.
--   - `OccurringIrrep`: PDF p.11 Eq.(47): only the occurring irreducible labels.
--   - `Row`: PDF pp.18--19: one coordinate for every fine irrep basis index, with multiplicity.
--   - `centralMatrix`: PDF p.11 Eq.(49), computed for every irrep, including absent ones.
--   - `centralMap`: PDF p.12 Eq.(54), a group average of conjugation maps.
--   - `fineMatrix`: PDF p.12 Eq.(57), diagonal matrix-coefficient average in the fixed irrep basis.
--   - `fineMap`: PDF p.12 Eq.(59), before any rank conclusion is supplied.
--   - `rawMatrix`: PDF pp.31,36,40: the raw (unnormalized) matrix, including zero pivots.
--   - `pivotWeight`: PDF p.13 Eq.(66): real diagonal weight of the positive rank-one projector.
--   - `normalizedMatrix`: PDF p.13 Eq.(62): normalization is computed, and used only at positive pivots.
--   - `Pivots`: PDF p.14 Remark 23: one independently chosen positive pivot for each fine sector.
--   - `eigenmatrix`: PDF pp.13--14: the selected eigenmatrix, with no assumed normalization.
--   - `choiVector`: PDF p.15 Eq.(74): transpose, with no coefficient conjugation.
--   - `muAt`: PDF p.15 Eq.(77): the eigenvalue for any pivot.
--   - `spectralMatrix`: PDF p.19 Eq.(95): rectangular transform, one row per fine sector.
--   - `spectralMap`: PDF pp.11--12 Eq.(53): spectral map with arbitrary complex sector coefficients.
--   - `trivialCoefficient`: Extract the trivial coefficient without assuming the conclusion that id belongs to theta.
--   - `choiEigenvalueVector`: PDF p.16 Eq.(80).
--   - `NonnegativeScalar`: Complex inequalities mean membership in the embedded nonnegative real scalars.
--   - `scaledSimplex`: PDF p.20 Eq.(104): all eigenvalues, including multiplicities, sum to n.
--   - `spectralGram`: PDF p.19 Eqs.(96)--(98), the Gram matrix is computed from M.
--   - `leftInverse`: PDF p.19 Eq.(96); invertibility of spectralGram is a theorem conclusion.
--   - `pivotKrausFamily`: PDF p.18, corrected by Appendix D: sqrt(choiEigenvalueVector) times unvec(v) transposed.
--   - `classCoefficients`: PDF p.21 Eq.(109); note g, not g inverse.
--   - `conjugacyClass`: PDF p.10 Eq.(46), finite conjugacy class.
--   - `classAverage`: PDF pp.22--23 Eq.(116), the conjugacy-class averaging matrix.
--   - `characterMatrix`: PDF p.22 Definition 53: the character matrix.
--   - `doubleSumMu`: PDF p.16 Eq.(83) and p.15 Eq.(79).
--   - `squaredSumEpsilon`: PDF p.16 Eq.(82), corrected |G|^-3 prefactor (see Appendix B p.39 Eq.(185)).
--   - `HasDecomposition`: PDF p.9 Eq.(34), with actual multiplicity spaces and an intertwining equivalence.
--   - `permutationSign`: Sign character in the paper's Examples 11,12 and Section 8.3.
--   - `DoubletDecomposition`: PDF pp.9--10 Eqs.(39),(40): actual id + sign + doublet intertwining decomposition.
--   - `flatIndex`: Fixed-coordinate flattening for the explicit 4 by 4 matrices, row order 00,01,10,11.
--   - `tensorFour`: Reindex a printed 4 by 4 matrix to tensor coordinates.
--   - `quaternionQ1`: PDF p.24 Eq.(124): Q1 and Q2 generate the concrete quaternion doublet.
--   - `quaternionQ2`: PDF p.24 Eq.(124), Q2.
--   - `quaternionRepresentation`: PDF p.24 Eq.(124), using Mathlib's a^j and x*a^j constructors.
--   - `quaternionCharacter`: PDF p.24 Table 1, ordered id,t1,t2,t3, for the four one-dimensional characters.
--   - `QuaternionDecomposition`: PDF p.24 Eq.(125), with the Table 1 character-labelled one-dimensional summands.
--   - `quaternionSuperMatrix`: PDF p.25 Eq.(127), with real coefficients a=l_t1, b=l_t2, c=l_t3.
--   - `quaternionMap`: PDF p.25 Eq.(127): the concrete map, on every operator.
--   - `quaternionChoiMatrix`: PDF p.25 Eq.(128).
--   - `quaternionEigenvalues`: PDF p.25 Eq.(129), including all multiplicities, order id,t1,t2,t3.
--   - `QuaternionCP`: PDF p.25 Eq.(129), the tetrahedron rather than its containing cube.
--   - `quaternionTransform`: PDF pp.25--26 Eqs.(130),(131), with the corrected minus sign in the third row.
--   - `quaternionKraus`: PDF p.26 Eq.(134), corrected eigenvalue labels t1,t2,t3, ordered id,t1,t2,t3.
--   - `HasOrthonormalSpectrum`: Orthonormal complete eigensystem; eigenvalues are listed with multiplicity.
--   - `EpsilonRealization`: PDF p.26 Eq.(135), choiEigenvalueVector realization in the source's fixed coordinate basis.
--   - `s3Map`: PDF p.26 Eq.(137), s=l_sign and t=l_lambda.
--   - `s3Eigenvalues`: PDF p.27 Eq.(140), order id,sign,lambda_1,lambda_2.
--   - `S3CP`: PDF p.27 Eq.(142), the full triangle.
--   - `s3Kraus`: PDF p.27 Eq.(143), order id,sign,lambda_1,lambda_2.
--   - `s3Transform`: PDF p.27 Eq.(139), rectangular 4 by 3 spectral transform.
--   - `s3Inverse`: PDF p.27 Eq.(141), a left inverse on the spectral range, not necessarily the Gram inverse.
--   - `permutationFixedCount`: Fixed-point count, used to identify S4 partition labels independently of a coordinate basis.
--   - `s4StandardCharacter`: S4 standard character, partition (3,1), source PDF p.28.
--   - `s4DoubletCharacter`: S4 doublet character, partition (2,2), computed from fixed points of g and g squared.
--   - `s4TwistCharacter`: S4 sign twist of the standard character, partition (2,1,1).
--   - `mapByCharacter`: Eq.(54), allowing named concrete characters instead of a full family of labels.
--   - `S4TripletDecomposition`: PDF p.28 Eq.(145), actual summands of dimensions 1,3,2,3.
--   - `s4Map`: PDF p.28, spectral family constructed by character projectors, not printed Eq.(148).
--   - `s4Eigenvalues`: PDF p.29 Eq.(149), order id, three (3,1), two (2,2), three (2,1,1) eigenvalues.
--   - `QuaternionPPT`: PDF p.31 Eq.(155), the four additional PPT inequalities.
-- source:
--   Structure of irreducibly covariant quantum channels for finite groups, arXiv:1610.05657v2, https://arxiv.org/abs/1610.05657v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17
import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P37
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P16
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P75

/-!
Statements from Mozrzymas--Studzinski--Datta, arXiv:1610.05657v2.
Pinned accepted definitions and the remaining paper-local substrate use the paper's row vectorization and unnormalized, input-first Choi
matrix. No theorem about the constructed projectors is a field of the input data.
Source corrections are identified at the affected declarations and in MODERATION_NOTES.md.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Extend50.P31

-- Exact pinned definitions; paper-specific interfaces below retain distinct names.
open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)
open QAlgorithms.Papers.Independent.Frontier18.P17 (hs)
open QAlgorithms.Papers.Independent.Bridge50.P37 (hsAdjoint)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)
open QAlgorithms.Papers.Independent.Dependency50.P26 (TracePreserving)
open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)
open QAlgorithms.Papers.Independent.Information100.P75 (phase)

/-- PDF pp.4--7: complex-linear endomorphisms on every operator. -/
abbrev EndMat (n : ℕ) := Mat n →ₗ[ℂ] Mat n

/-- PDF p.4, Eq.(5): row vectorization, also for rectangular matrices. -/
def rowVec {d e : ℕ} : Matrix (Fin d) (Fin e) ℂ ≃ₗ[ℂ] ((Fin d × Fin e) → ℂ) where
  toFun X p := X p.1 p.2
  invFun v i j := v (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- PDF pp.5--6, Eqs.(8),(15): entries in the fixed matrix-unit basis. -/
def rowMatrixRepresentative {n : ℕ} (Phi : EndMat n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  fun p q => Phi (matrixUnit q.1 q.2) p.1 p.2

/-- The inverse coordinate representation, acting on every operator. -/
def fromMat {n : ℕ} (M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ) : EndMat n :=
  rowVec.symm.toLinearMap.comp (M.mulVecLin.comp rowVec.toLinearMap)

/-- PDF p.8 Definition 7; complete positivity is the frozen all-ancilla definition. -/
def IsPaperChannel {d e : ℕ} (Phi : Mat d →ₗ[ℂ] Mat e) : Prop :=
  QAlgorithms.Entanglement.IsCompletelyPositive Phi ∧ TracePreserving Phi

/-- PDF p.7: an ordinary unitary irreducible representation, with positive dimension.
Irreducibility means that every complex invariant linear subspace is zero or the whole space. -/
structure UnitaryIrrep (G : Type*) [Group G] (n : ℕ) where
  rho : G → Mat n
  positive : 0 < n
  one : rho 1 = 1
  mul : ∀ g h, rho (g*h) = rho g * rho h
  unitary : ∀ g, (rho g)ᴴ * rho g = 1 ∧ rho g * (rho g)ᴴ = 1
  irreducible : ∀ S : Submodule ℂ (Fin n → ℂ),
    (∀ g v, v ∈ S → (rho g).mulVec v ∈ S) → S = ⊥ ∨ S = ⊤

/-- PDF p.9: equivalence of representations is an invertible intertwiner. -/
def RepEquivalent {G : Type*} {d e : ℕ} (U : G → Mat d) (V : G → Mat e) : Prop :=
  ∃ T : (Fin d → ℂ) ≃ₗ[ℂ] (Fin e → ℂ),
    ∀ g x, T ((U g).mulVec x) = (V g).mulVec (T x)

/-- PDF pp.9--10: complete, inequivalent, coordinate-fixed unitary irreducibles. -/
structure IrrepFamily (G A : Type*) [Group G] where
  dim : A → ℕ
  irrep : (a : A) → UnitaryIrrep G (dim a)
  trivial : A
  trivial_dim : dim trivial = 1
  trivial_action : ∀ g, (irrep trivial).rho g = 1
  inequivalent : ∀ a b, RepEquivalent (irrep a).rho (irrep b).rho → a = b
  complete : ∀ d (V : UnitaryIrrep G d), ∃ a, RepEquivalent V.rho (irrep a).rho

/-- PDF p.8: character of a fixed-coordinate irrep. -/
def character {G : Type*} [Group G] {n : ℕ} (U : UnitaryIrrep G n) (g : G) : ℂ :=
  Matrix.trace (U.rho g)

/-- PDF p.7 Eq.(25), conjugation on the full operator space. -/
def conjugationMap {G : Type*} [Group G] {n : ℕ} (U : UnitaryIrrep G n) (g : G) : EndMat n :=
  sandwich (U.rho g) (U.rho g)ᴴ

/-- PDF pp.7--8 Eqs.(24),(28): entrywise conjugation on the second tensor factor. -/
def tensorConjugate {G : Type*} [Group G] {n : ℕ} (U : UnitaryIrrep G n) (g : G) :=
  Matrix.kronecker (U.rho g) (fun i j => conj (U.rho g i j))

/-- PDF p.8 Eq.(31), on every operator, without positivity or TP. -/
def IsIrrepCovariant {G : Type*} [Group G] {n : ℕ} (U : UnitaryIrrep G n) (Phi : EndMat n) : Prop :=
  ∀ g X, Phi (conjugationMap U g X) = conjugationMap U g (Phi X)

/-- PDF p.9 Eq.(36), as an actual complex linear subspace. -/
def representationCommutant {G I : Type*} [Fintype I] [DecidableEq I]
    (R : G → Matrix I I ℂ) : Submodule ℂ (Matrix I I ℂ) where
  carrier := {M | ∀ g, M * R g = R g * M}
  zero_mem' := by simp
  add_mem' := by intro M N hM hN g; simp [add_mul, mul_add, hM g, hN g]
  smul_mem' := by intro c M hM g; simpa [Matrix.smul_mul, Matrix.mul_smul] using congrArg (c • ·) (hM g)

/-- PDF p.11 Eq.(47): an invertible intertwiner to exactly one copy of each listed irrep.
This predicate contains no character-projector facts. -/
def SimplyReducible {G A : Type*} [Group G] [DecidableEq A] {n : ℕ}
    (U : UnitaryIrrep G n) (F : IrrepFamily G A) (theta : Finset A) : Prop :=
  ∃ T : ((Fin n × Fin n) → ℂ) ≃ₗ[ℂ]
      ((a : {a // a ∈ theta}) → Fin (F.dim a.val) → ℂ),
    ∀ g v a, T ((tensorConjugate U g).mulVec v) a =
      ((F.irrep a.val).rho g).mulVec (T v a)

/-- Only the section's standing assumptions, PDF pp.7--11 and Assumption 1 p.17. -/
structure Data (G A : Type*) [Group G] [Fintype G] [Fintype A] [DecidableEq A] (n : ℕ) where
  U : UnitaryIrrep G n
  F : IrrepFamily G A
  theta : Finset A
  decomposition : SimplyReducible U F theta

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

/-- PDF p.11 Eq.(47): only the occurring irreducible labels. -/
abbrev OccurringIrrep (D : Data G A n) := {a // a ∈ D.theta}

/-- PDF pp.18--19: one coordinate for every fine irrep basis index, with multiplicity. -/
abbrev Row (D : Data G A n) := Σ a : OccurringIrrep D, Fin (D.F.dim a.val)

/-- PDF p.11 Eq.(49), computed for every irrep, including absent ones. -/
def centralMatrix (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  ((F.dim a : ℂ) / Fintype.card G) •
    ∑ g : G, character (F.irrep a) g⁻¹ • tensorConjugate U g

/-- PDF p.12 Eq.(54), a group average of conjugation maps. -/
def centralMap (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A) : EndMat n :=
  ((F.dim a : ℂ) / Fintype.card G) •
    ∑ g : G, character (F.irrep a) g⁻¹ • conjugationMap U g

/-- PDF p.12 Eq.(57), diagonal matrix-coefficient average in the fixed irrep basis. -/
def fineMatrix (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A)
    (i : Fin (F.dim a)) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
  ((F.dim a : ℂ) / Fintype.card G) •
    ∑ g : G, (F.irrep a).rho g⁻¹ i i • tensorConjugate U g

/-- PDF p.12 Eq.(59), before any rank conclusion is supplied. -/
def fineMap (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A)
    (i : Fin (F.dim a)) : EndMat n :=
  ((F.dim a : ℂ) / Fintype.card G) •
    ∑ g : G, (F.irrep a).rho g⁻¹ i i • conjugationMap U g

/-- PDF pp.31,36,40: the raw (unnormalized) matrix, including zero pivots. -/
def rawMatrix (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A)
    (i : Fin (F.dim a)) (p : Fin n × Fin n) : Mat n :=
  fineMap U F a i (matrixUnit p.1 p.2)

/-- PDF p.13 Eq.(66): real diagonal weight of the positive rank-one projector. -/
def pivotWeight (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A)
    (i : Fin (F.dim a)) (p : Fin n × Fin n) : ℝ :=
  (fineMatrix U F a i p p).re

/-- PDF p.13 Eq.(62): normalization is computed, and used only at positive pivots. -/
def normalizedMatrix (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A)
    (i : Fin (F.dim a)) (p : Fin n × Fin n) : Mat n :=
  ((Real.sqrt (pivotWeight U F a i p))⁻¹ : ℂ) • rawMatrix U F a i p

/-- PDF p.14 Remark 23: one independently chosen positive pivot for each fine sector. -/
structure Pivots (D : Data G A n) where
  pivot : Row D → Fin n × Fin n
  positive : ∀ r, 0 < pivotWeight D.U D.F r.1.val r.2 (pivot r)

/-- PDF pp.13--14: the selected eigenmatrix, with no assumed normalization. -/
def eigenmatrix (D : Data G A n) (P : Pivots D) (r : Row D) : Mat n :=
  normalizedMatrix D.U D.F r.1.val r.2 (P.pivot r)

/-- PDF p.15 Eq.(74): transpose, with no coefficient conjugation. -/
def choiVector (D : Data G A n) (P : Pivots D) (r : Row D) : (Fin n × Fin n) → ℂ :=
  rowVec (eigenmatrix D P r)ᵀ

/-- PDF p.15 Eq.(77): the eigenvalue for any pivot. -/
def muAt (D : Data G A n) (a : A) (r : Row D) (p : Fin n × Fin n) : ℂ :=
  ((D.F.dim a : ℂ) / Fintype.card G) * ∑ g : G,
    character (D.F.irrep a) g⁻¹ *
      (Complex.normSq (Matrix.trace (normalizedMatrix D.U D.F r.1.val r.2 p * (D.U.rho g)ᴴ)) : ℂ)

/-- PDF p.19 Eq.(95): rectangular transform, one row per fine sector. -/
def spectralMatrix (D : Data G A n) (P : Pivots D) : Matrix (Row D) (OccurringIrrep D) ℂ :=
  fun r a => muAt D a.val r (P.pivot r)

/-- PDF pp.11--12 Eq.(53): spectral map with arbitrary complex sector coefficients. -/
def spectralMap (D : Data G A n) (l : OccurringIrrep D → ℂ) : EndMat n :=
  ∑ a : OccurringIrrep D, l a • centralMap D.U D.F a.val

/-- Extract the trivial coefficient without assuming the conclusion that id belongs to theta. -/
def trivialCoefficient (D : Data G A n) (l : OccurringIrrep D → ℂ) : ℂ :=
  ∑ a : OccurringIrrep D, if a.val = D.F.trivial then l a else 0

/-- PDF p.16 Eq.(80). -/
def choiEigenvalueVector (D : Data G A n) (P : Pivots D) (l : OccurringIrrep D → ℂ) : Row D → ℂ :=
  (spectralMatrix D P).mulVec l

/-- Complex inequalities mean membership in the embedded nonnegative real scalars. -/
def NonnegativeScalar (z : ℂ) : Prop := z.im = 0 ∧ 0 ≤ z.re

/-- PDF p.20 Eq.(104): all eigenvalues, including multiplicities, sum to n. -/
def scaledSimplex (D : Data G A n) : Set (Row D → ℂ) :=
  {e | (∀ r, NonnegativeScalar (e r)) ∧ ∑ r, e r = (n : ℂ)}

/-- PDF p.19 Eqs.(96)--(98), the Gram matrix is computed from M. -/
def spectralGram (D : Data G A n) (P : Pivots D) :=
  (spectralMatrix D P)ᴴ * spectralMatrix D P

/-- PDF p.19 Eq.(96); invertibility of spectralGram is a theorem conclusion. -/
def leftInverse (D : Data G A n) (P : Pivots D) :=
  (spectralGram D P)⁻¹ * (spectralMatrix D P)ᴴ

/-- PDF p.18, corrected by Appendix D: sqrt(choiEigenvalueVector) times unvec(v) transposed. -/
def pivotKrausFamily (D : Data G A n) (P : Pivots D) (l : OccurringIrrep D → ℂ) (r : Row D) : Mat n :=
  (Real.sqrt (choiEigenvalueVector D P l r).re : ℂ) • (rowVec.symm (choiVector D P r))ᵀ

/-- PDF p.21 Eq.(109); note g, not g inverse. -/
def classCoefficients (D : Data G A n) (f : G → ℂ) (a : OccurringIrrep D) : ℂ :=
  (∑ g, character (D.F.irrep a.val) g * f g) /
    ((Fintype.card G : ℂ) * D.F.dim a.val)

/-- PDF p.10 Eq.(46), finite conjugacy class. -/
def conjugacyClass (g : G) : Finset G :=
  Finset.univ.filter (fun h => ∃ k : G, h = k * g * k⁻¹)

/-- PDF pp.22--23 Eq.(116), the conjugacy-class averaging matrix. -/
def classAverage : Matrix G G ℂ :=
  fun g h => if h ∈ conjugacyClass g then (Fintype.card {x // x ∈ conjugacyClass g} : ℂ)⁻¹ else 0

/-- PDF p.22 Definition 53: the character matrix. -/
def characterMatrix (F : IrrepFamily G A) : Matrix G A ℂ :=
  fun g a => character (F.irrep a) g⁻¹

/-- PDF p.16 Eq.(83) and p.15 Eq.(79). -/
def doubleSumMu (D : Data G A n) (a : A) (r : Row D) (p : Fin n × Fin n) : ℂ :=
  ((D.F.dim a : ℂ) * D.F.dim r.1.val /
      ((pivotWeight D.U D.F r.1.val r.2 p : ℂ) * (Fintype.card G : ℂ)^2)) *
    ∑ g : G, ∑ h : G, character (D.F.irrep a) g⁻¹ *
      (D.F.irrep r.1.val).rho h⁻¹ r.2 r.2 *
      D.U.rho g⁻¹ p.2 p.1 * D.U.rho (h*g*h⁻¹) p.1 p.2

/-- PDF p.16 Eq.(82), corrected |G|^-3 prefactor (see Appendix B p.39 Eq.(185)). -/
def squaredSumEpsilon (D : Data G A n) (l : OccurringIrrep D → ℂ)
    (r : Row D) (p : Fin n × Fin n) : ℂ :=
  ((Fintype.card G : ℂ)^3)⁻¹ * ∑ g : G, ∑ a : OccurringIrrep D,
    l a * (D.F.dim a.val : ℂ) * character (D.F.irrep a.val) g⁻¹ *
      (Complex.normSq (((D.F.dim r.1.val : ℂ) /
        (Real.sqrt (pivotWeight D.U D.F r.1.val r.2 p) : ℂ)) *
        ∑ h : G, (D.F.irrep r.1.val).rho h⁻¹ r.2 r.2 *
          D.U.rho (h⁻¹*g⁻¹*h) p.2 p.1) : ℂ)

/-- Sanity: the row-vectorized (0,1) matrix unit occupies coordinate (0,1). -/
example : rowVec (matrixUnit (0 : Fin 2) 1) (0,1) = 1 := by
  change (Matrix.single (0 : Fin 2) 1 (1 : ℂ)) 0 1 = 1
  simp [Matrix.single]

/-- Sanity: Choi uses input-first coordinates even for a rectangular map. -/
example {d e : ℕ} (Phi : Mat d →ₗ[ℂ] Mat e) (i j : Fin d) (k l : Fin e) :
    choi Phi (i,k) (j,l) = Phi (matrixUnit i j) k l := rfl

/-- Sanity: a zero pivot never generates a spurious nonzero normalized matrix. -/
example (U : UnitaryIrrep G n) (F : IrrepFamily G A) (a : A)
    (i : Fin (F.dim a)) (p : Fin n × Fin n) (h : pivotWeight U F a i p = 0) :
    normalizedMatrix U F a i p = 0 := by
  simp [normalizedMatrix, h]

/-- Sanity: phase zero is the scalar one. -/
example : phase 0 = 1 := by simp [phase]

/-- PDF p.9 Eq.(34), with actual multiplicity spaces and an intertwining equivalence. -/
def HasDecomposition (U : UnitaryIrrep G n) (F : IrrepFamily G A) (m : A → ℕ) : Prop :=
  ∃ T : ((Fin n × Fin n) → ℂ) ≃ₗ[ℂ]
      ((a : A) → Fin (m a) → Fin (F.dim a) → ℂ),
    ∀ g v a j, T ((tensorConjugate U g).mulVec v) a j =
      ((F.irrep a).rho g).mulVec (T v a j)

/-- Sign character in the paper's Examples 11,12 and Section 8.3. -/
def permutationSign {k : ℕ} (g : Equiv.Perm (Fin k)) : ℂ :=
  ((Equiv.Perm.sign g : ℤ) : ℂ)

/-- PDF pp.9--10 Eqs.(39),(40): actual id + sign + doublet intertwining decomposition. -/
def DoubletDecomposition {k : ℕ} (U : UnitaryIrrep (Equiv.Perm (Fin k)) 2) : Prop :=
  ∃ T : ((Fin 2 × Fin 2) → ℂ) ≃ₗ[ℂ] (ℂ × ℂ × (Fin 2 → ℂ)),
    ∀ g v, T ((tensorConjugate U g).mulVec v) =
      ((T v).1, permutationSign g * (T v).2.1, (U.rho g).mulVec (T v).2.2)

/-- Fixed-coordinate flattening for the explicit 4 by 4 matrices, row order 00,01,10,11. -/
def flatIndex (p : Fin 2 × Fin 2) : Fin 4 := Fin.ofNat 4 (2*p.1.val + p.2.val)

/-- Reindex a printed 4 by 4 matrix to tensor coordinates. -/
def tensorFour (M : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun p q => M (flatIndex p) (flatIndex q)

/-- PDF p.24 Eq.(124): Q1 and Q2 generate the concrete quaternion doublet. -/
def quaternionQ1 : Mat 2 := !![Complex.I, 0; 0, -Complex.I]

/-- PDF p.24 Eq.(124), Q2. -/
def quaternionQ2 : Mat 2 := !![0, 1; -1, 0]

/-- PDF p.24 Eq.(124), using Mathlib's a^j and x*a^j constructors. -/
def quaternionRepresentation : QuaternionGroup 2 → Mat 2
  | .a j => quaternionQ1 ^ j.val
  | .xa j => quaternionQ2 * quaternionQ1 ^ j.val

/-- PDF p.24 Table 1, ordered id,t1,t2,t3, for the four one-dimensional characters. -/
def quaternionCharacter (a : Fin 4) : QuaternionGroup 2 → ℂ
  | .a j => if a = 0 ∨ a = 2 then 1 else (-1 : ℂ)^j.val
  | .xa j => if a = 0 then 1 else if a = 1 then (-1 : ℂ)^j.val
      else if a = 2 then -1 else -((-1 : ℂ)^j.val)

/-- PDF p.24 Eq.(125), with the Table 1 character-labelled one-dimensional summands. -/
def QuaternionDecomposition (U : UnitaryIrrep (QuaternionGroup 2) 2) : Prop :=
  ∃ T : ((Fin 2 × Fin 2) → ℂ) ≃ₗ[ℂ] (Fin 4 → ℂ),
    ∀ g v a, T ((tensorConjugate U g).mulVec v) a = quaternionCharacter a g * T v a

/-- PDF p.25 Eq.(127), with real coefficients a=l_t1, b=l_t2, c=l_t3. -/
def quaternionSuperMatrix (a b c : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (1/2 : ℂ) • !![1+(b : ℂ), 0, 0, 1-(b : ℂ);
    0, (a : ℂ)+(c : ℂ), (c : ℂ)-(a : ℂ), 0; 0, (c : ℂ)-(a : ℂ), (a : ℂ)+(c : ℂ), 0; 1-(b : ℂ), 0, 0, 1+(b : ℂ)]

/-- PDF p.25 Eq.(127): the concrete map, on every operator. -/
def quaternionMap (a b c : ℝ) : EndMat 2 := fromMat (tensorFour (quaternionSuperMatrix a b c))

/-- PDF p.25 Eq.(128). -/
def quaternionChoiMatrix (a b c : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (1/2 : ℂ) • !![1+(b : ℂ), 0, 0, (a : ℂ)+(c : ℂ);
    0, 1-(b : ℂ), (c : ℂ)-(a : ℂ), 0; 0, (c : ℂ)-(a : ℂ), 1-(b : ℂ), 0; (a : ℂ)+(c : ℂ), 0, 0, 1+(b : ℂ)]

/-- PDF p.25 Eq.(129), including all multiplicities, order id,t1,t2,t3. -/
def quaternionEigenvalues (a b c : ℝ) : Fin 4 → ℝ :=
  ![(1+a+b+c)/2, (1+a-b-c)/2, (1-a+b-c)/2, (1-a-b+c)/2]

/-- PDF p.25 Eq.(129), the tetrahedron rather than its containing cube. -/
def QuaternionCP (a b c : ℝ) : Prop :=
  0 ≤ (1+a+b+c)/2 ∧ 0 ≤ (1+a-b-c)/2 ∧ 0 ≤ (1-a+b-c)/2 ∧ 0 ≤ (1-a-b+c)/2

/-- PDF pp.25--26 Eqs.(130),(131), with the corrected minus sign in the third row. -/
def quaternionTransform : Matrix (Fin 4) (Fin 4) ℂ :=
  (1/2 : ℂ) • !![1,1,1,1; 1,1,-1,-1; 1,-1,1,-1; 1,-1,-1,1]

/-- PDF p.26 Eq.(134), corrected eigenvalue labels t1,t2,t3, ordered id,t1,t2,t3. -/
def quaternionKraus (a b c : ℝ) (r : Fin 4) : Mat 2 :=
  (Real.sqrt (quaternionEigenvalues a b c r / 2) : ℂ) •
    (![1, quaternionQ2, !![-1,0;0,1], !![0,1;1,0]] : Fin 4 → Mat 2) r

/-- Orthonormal complete eigensystem; eigenvalues are listed with multiplicity. -/
def HasOrthonormalSpectrum {k d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (values : Fin k → ℝ) : Prop :=
  ∃ v : Fin k → (Fin d × Fin d) → ℂ,
    (∀ i j, (∑ p, conj (v i p) * v j p) = if i = j then 1 else 0) ∧
    Submodule.span ℂ (Set.range v) = ⊤ ∧
    ∀ i, M.mulVec (v i) = (values i : ℂ) • v i

/-- PDF p.26 Eq.(135), choiEigenvalueVector realization in the source's fixed coordinate basis. -/
def EpsilonRealization (U : UnitaryIrrep (Equiv.Perm (Fin 3)) 2) : Prop :=
  let w := Complex.exp (((2*Real.pi/3 : ℝ) : ℂ) * Complex.I)
  U.rho (Equiv.swap 0 1) = !![0,1;1,0] ∧
  U.rho (Equiv.swap 1 2) = !![0,w^2;w,0]

/-- PDF p.26 Eq.(137), s=l_sign and t=l_lambda. -/
def s3Map (s t : ℝ) : EndMat 2 := quaternionMap t s t

/-- PDF p.27 Eq.(140), order id,sign,lambda_1,lambda_2. -/
def s3Eigenvalues (s t : ℝ) : Fin 4 → ℝ :=
  ![(1+s)/2+t, (1+s)/2-t, (1-s)/2, (1-s)/2]

/-- PDF p.27 Eq.(142), the full triangle. -/
def S3CP (s t : ℝ) : Prop := -1 ≤ s ∧ s ≤ 1 ∧ |t| ≤ (1+s)/2

/-- PDF p.27 Eq.(143), order id,sign,lambda_1,lambda_2. -/
def s3Kraus (s t : ℝ) : Fin 4 → Mat 2 :=
  ![(Real.sqrt (s3Eigenvalues s t 0 / 2) : ℂ) • 1,
    (Real.sqrt (s3Eigenvalues s t 1 / 2) : ℂ) • !![-1,0;0,1],
    (Real.sqrt (s3Eigenvalues s t 2) : ℂ) • !![0,0;1,0],
    (Real.sqrt (s3Eigenvalues s t 3) : ℂ) • !![0,1;0,0]]

/-- PDF p.27 Eq.(139), rectangular 4 by 3 spectral transform. -/
def s3Transform : Matrix (Fin 4) (Fin 3) ℂ :=
  (1/2 : ℂ) • !![1,1,2;1,1,-2;1,-1,0;1,-1,0]

/-- PDF p.27 Eq.(141), a left inverse on the spectral range, not necessarily the Gram inverse. -/
def s3Inverse : Matrix (Fin 3) (Fin 4) ℂ :=
  (1/2 : ℂ) • !![1,1,1,1;1,1,-1,-1;1,-1,0,0]

/-- Fixed-point count, used to identify S4 partition labels independently of a coordinate basis. -/
def permutationFixedCount {k : ℕ} (g : Equiv.Perm (Fin k)) : ℕ :=
  (Finset.univ.filter (fun i => g i = i)).card

/-- S4 standard character, partition (3,1), source PDF p.28. -/
def s4StandardCharacter (g : Equiv.Perm (Fin 4)) : ℂ := (permutationFixedCount g : ℂ) - 1

/-- S4 doublet character, partition (2,2), computed from fixed points of g and g squared. -/
def s4DoubletCharacter (g : Equiv.Perm (Fin 4)) : ℂ :=
  ((permutationFixedCount g : ℂ)^2 + (permutationFixedCount (g*g) : ℂ))/2 - 2*(permutationFixedCount g : ℂ)

/-- S4 sign twist of the standard character, partition (2,1,1). -/
def s4TwistCharacter (g : Equiv.Perm (Fin 4)) : ℂ :=
  permutationSign g * s4StandardCharacter g

/-- Eq.(54), allowing named concrete characters instead of a full family of labels. -/
def mapByCharacter {H : Type*} [Group H] [Fintype H] {d : ℕ}
    (U : UnitaryIrrep H d) (dimension : ℕ) (chi : H → ℂ) : EndMat d :=
  ((dimension : ℂ) / Fintype.card H) • ∑ g : H, chi g⁻¹ • conjugationMap U g

/-- PDF p.28 Eq.(145), actual summands of dimensions 1,3,2,3. -/
def S4TripletDecomposition (U : UnitaryIrrep (Equiv.Perm (Fin 4)) 3)
    (V : UnitaryIrrep (Equiv.Perm (Fin 4)) 2)
    (W : UnitaryIrrep (Equiv.Perm (Fin 4)) 3) : Prop :=
  ∃ T : ((Fin 3 × Fin 3) → ℂ) ≃ₗ[ℂ]
      (ℂ × (Fin 3 → ℂ) × (Fin 2 → ℂ) × (Fin 3 → ℂ)),
    ∀ g v, T ((tensorConjugate U g).mulVec v) =
      ((T v).1, (U.rho g).mulVec (T v).2.1,
        (V.rho g).mulVec (T v).2.2.1, (W.rho g).mulVec (T v).2.2.2)

/-- PDF p.28, spectral family constructed by character projectors, not printed Eq.(148). -/
def s4Map (U : UnitaryIrrep (Equiv.Perm (Fin 4)) 3) (a b c : ℝ) : EndMat 3 :=
  mapByCharacter U 1 (fun _ => 1) + (a : ℂ) • mapByCharacter U 3 s4StandardCharacter +
    (b : ℂ) • mapByCharacter U 2 s4DoubletCharacter + (c : ℂ) • mapByCharacter U 3 s4TwistCharacter

/-- PDF p.29 Eq.(149), order id, three (3,1), two (2,2), three (2,1,1) eigenvalues. -/
def s4Eigenvalues (a b c : ℝ) : Fin 9 → ℝ :=
  ![(1+3*a+2*b+3*c)/3,
    (2+3*a-2*b-3*c)/6, (2+3*a-2*b-3*c)/6, (2+3*a-2*b-3*c)/6,
    (2-3*a+4*b-3*c)/6, (2-3*a+4*b-3*c)/6,
    (2-3*a-2*b+3*c)/6, (2-3*a-2*b+3*c)/6, (2-3*a-2*b+3*c)/6]

/-- PDF p.31 Eq.(155), the four additional PPT inequalities. -/
def QuaternionPPT (a b c : ℝ) : Prop :=
  0 ≤ (1-a-b-c)/2 ∧ 0 ≤ (1+a+b-c)/2 ∧ 0 ≤ (1+a-b+c)/2 ∧ 0 ≤ (1-a+b+c)/2

/-- Sanity: row order is 00,01,10,11. -/
example : flatIndex (0,1) = 1 ∧ flatIndex (1,0) = 2 := by decide

/-- Sanity: quaternion depolarization has four unnormalized Choi eigenvalues 1/2. -/
example : quaternionEigenvalues 0 0 0 = ![1/2,1/2,1/2,1/2] := by
  norm_num [quaternionEigenvalues]

/-- Sanity: the S3 identity parameter pair has unnormalized Choi eigenvalues 2,0,0,0. -/
example : s3Eigenvalues 1 1 = ![2,0,0,0] := by norm_num [s3Eigenvalues]

end QAlgorithms.Papers.Independent.Extend50.P31


