-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01
-- name    : QAlgorithms_Papers_Independent_Gap50repair_P01
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T06:12:15.501478+00:00
-- url     : https://prove2.me/theorems/b52e5504-253f-4d11-9c90-9904e4e12e18
-- title:
--   Definitions for The Conley-Zehnder index for a path of symplectic matrices
-- statement:
--   The objects the formalized statements of *The Conley-Zehnder index for a path of symplectic matrices* (arXiv:1201.3728) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Coord`: Grouped coordinates, PDF pp.4–5.
--   - `GroupedRealMatrix`
--   - `CMat`
--   - `omegaMatrix`: Standard symplectic form and compatible complex structure, PDF p.4.
--   - `jMatrix`
--   - `omegaR`: Bilinear forms; no conjugation is hidden in omegaC, PDF pp.4,11.
--   - `omegaC`
--   - `IsOrthogonal`: Orthogonality and complex linearity, PDF p.5.
--   - `CommutesWithComplexStructure`
--   - `complexActionMatrix`: Complex matrix of a complex-linear real action, PDF p.5; entrywise complexification itself is imported from the pinned library.
--   - `complexActionDet`: Definition 6; used on complex-linear real matrices, PDF p.6.
--   - `IsUnitaryReal`: Independent unitary predicate from Definition 4, PDF p.5.
--   - `SymplecticSpace`
--   - `UnitarySpace`
--   - `ComplexUnitary`
--   - `SpecialUnitary`
--   - `UnitCircle`
--   - `IsSymmetricLie`: Symmetric part of the symplectic Lie algebra, PDF p.6 (4).
--   - `SymmetricLieSpace`
--   - `polarP`: Positive symmetric square root of A^T A, by choice; fallback only off domain, pp.6–7.
--   - `polarU`: Computed polar projection, PDF p.42.
--   - `shifted`: Shift and stable generalized eigenspace; exponent 2n reaches the stable kernel, pp.13–14.
--   - `generalizedSpace`
--   - `IsEigenvalue`
--   - `eigenvalues`: Distinct eigenvalues and algebraic multiplicities, PDF p.14.
--   - `algebraicMultiplicity`
--   - `kreinPositive`: Real positive inertia of Im Omega(z,conj z) on E_lambda. The finite search bound is the ambient real dimension 4n, PDF pp.12–15.
--   - `spectralRotation`: Rotation from the spectral formula (18), PDF p.15. Real inertia and the negative real multiplicity are even, so these natural divisions are exact halves.
--   - `IsWindingLift`: Oriented real lift: a positive full turn has theta(t)=t and degree +1, pp.35,56.
--   - `winding`: Degree of a based continuous circle loop, PDF p.35; zero fallback off domain.
--   - `IsPath`: Continuous symplectic path with arbitrary endpoints, PDF pp.35,47.
--   - `IsAdmissible`: Definition 32. Positive duration is supplied by binders, PDF p.35.
--   - `wPlus`: Fixed reference representatives, PDF p.32 (35)–(37).
--   - `wMinus`
--   - `unitPath`: Positive affine reparametrization, PDF pp.38,43–44.
--   - `IsExtension`: Admissible extension of Definition 33, PDF p.35.
--   - `chosenExtension`: Choice is over actual extensions, not over index axioms; existence is concluded, p.35.
--   - `conleyZehnder`: Genuine integer degree construction, Definition 33, PDF p.35.
--   - `integerPower`: All integer powers, including inverse powers, PDF p.15.
--   - `HasNilpotentHeight`: Maximal nilpotent height on the generalized space, PDF p.17.
--   - `restrictedKernel`: Kernel restricted to E_lambda, PDF p.17 (23).
--   - `GeneralizedQuotient`
--   - `FixedHomotopic`: Compact-rectangle homotopy with fixed endpoints, PDF pp.38,46.
--   - `AdmissiblyHomotopic`: Homotopy through SP(n); the final endpoint may move in Sp*, PDF p.37.
--   - `catenate`: Catenation normalized to [0,1], PDF pp.38,46.
--   - `translatedCatenate`: Lemma 36's translated catenation: the second argument is 2t-T, PDF p.38.
--   - `mergeBlocks`: Sum on a coordinate half, used to retain grouped order, PDF p.16.
--   - `symplecticSum`: Symplectic direct sum with the source's coordinate permutation, PDF p.16.
--   - `positiveInertia`: Maximum positive-subspace dimension in a finite real ambient space, pp.44–49.
--   - `formSignature`: Positive minus negative inertia, also on degenerate forms and zero spaces, pp.44–49.
--   - `matrixSignature`
--   - `exponentialPath`: Exponential and small-symmetric normalization data, PDF pp.36,52.
--   - `IsSmallSymmetric`
--   - `sMinus`: The explicitly constructed S^-, not a variable supplied by a hypothesis, PDF p.41.
--   - `referenceMinus`
--   - `complexLinearPart`: Complex-linear part and determinant normalized by absolute value, PDF p.42 (45).
--   - `normalizedDet`
--   - `shear`: Upper shear of Definition 53, PDF p.51.
--   - `crossingSpace`: Graph-reference kernel or vertical-reference intersection pulled back by A, PDF pp.47,58. These are different subspaces.
--   - `pathDerivative`: One-sided endpoint derivatives via the interval, PDF pp.44–50.
--   - `crossingBilinear`: Pullback crossing form Omega(A v,A' w), PDF pp.49,58. On ker(A-I) this is v^T S w; for RS2 the pullback subspace is V intersect A^-1 V.
--   - `crossingSignature`
--   - `crossings`: Interior crossing set, Definitions 44,50, PDF pp.46,49.
--   - `IsRegular`: Smoothness and nondegeneracy at every crossing, including endpoints, p.49. Nondegeneracy on the zero space is valid. Finiteness is not assumed.
--   - `interiorCrossingSum`: Finite sum; off the finite domain the fallback is zero, PDF p.49.
--   - `regularIndex`: Half-integer crossing value, PDF pp.46,49.
--   - `regularPathRepresentative`: Smooth regular representative with fixed-endpoint homotopy, PDF p.46. Choice imposes no index value or invariance assumption.
--   - `robbinSalamon`: Graph Robbin–Salamon index reconstructed by Definitions 44,46 and (52), pp.46–49.
--   - `robbinSalamonVertical`: Separate vertical-reference index of section 7.5, PDF p.58.
--   - `IsHalfIntegerFamily`: Half-integer family, with arbitrary endpoint degeneracies, PDF pp.47,53.
--   - `RsCore`: Homotopy/catenation/zero core shared by the characterizations, PDF pp.52–56.
--   - `RsFourAxioms`: Four axioms: normalization includes singular and zero S, PDF p.52.
--   - `RsProduct`: Dimension-family product, PDF pp.53,56.
--   - `RsSevenAxioms`: Seven properties, including generalization, naturality and -tB shear, PDF p.53.
--   - `RsSixAxioms`: Six properties, with distinct nondegenerate-signature and shear normalizations, p.56.
--   - `CzThreeAxioms`: Homotopy, loop and signature characterization, PDF p.40.
--   - `RotationAxiomsTwo`: Theorem 10(1)–(3), dimension two, PDF pp.8,11.
--   - `graphSpace`: Graph as an actual linear subspace, PDF p.47.
--   - `IsGraphLagrangian`: Lagrangian in the doubled form -Omega direct_sum Omega, PDF p.47.
--   - `RotationFamilyAxioms`: Four rotation axioms for the positive-dimension family of Theorem 10, PDF p.8. Functions are compared only on symplectic matrices in dimensions n>=1.
--   - `kreinPairing`: Real Krein form before restricting to E_lambda; conjugate the second vector explicitly, PDF pp.12,15, formula (18).
--   - `firstKindMultiplicity`: Multiplicity of an eigenvalue of the first kind, Definition 17 and Remark 18, PDF p.15. At +1 and -1 use half the complex generalized dimension; elsewhere on S1 use half the real positive inertia.
--   - `ImageIndexAxioms`: Five image-index properties on all positive dimensions, PDF p.58. Homotopy is the full iff for paths with the same matrix endpoints.
-- source:
--   The Conley-Zehnder index for a path of symplectic matrices, arXiv:1201.3728v2, https://arxiv.org/abs/1201.3728v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P10
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P02

/-! Jean Gutt, arXiv:1201.3728v2. Grouped x,y coordinates. Complexification and symplecticity reuse pinned
definitions; remaining concepts are paper local.
Winding uses oriented real lifts. Compilation pending. -/

noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

namespace QAlgorithms.Papers.Independent.Gap50repair.P01

attribute [local instance] Classical.propDecidable

-- Pinned entrywise complexification and symplecticity. The latter uses -Omega0;
-- preserving -Omega0 is equivalent to preserving Omega0, with identical coordinates.
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic)

/-- Grouped coordinates, PDF pp.4–5. -/
abbrev Coord (n : ℕ) := Fin n ⊕ Fin n

abbrev GroupedRealMatrix (n : ℕ) := Matrix (Coord n) (Coord n) ℝ

abbrev CMat (n : ℕ) := Matrix (Coord n) (Coord n) ℂ

/-- Standard symplectic form and compatible complex structure, PDF p.4. -/
def omegaMatrix (n : ℕ) : GroupedRealMatrix n := Matrix.fromBlocks 0 1 (-1) 0

def jMatrix (n : ℕ) : GroupedRealMatrix n := -omegaMatrix n

/-- Bilinear forms; no conjugation is hidden in omegaC, PDF pp.4,11. -/
def omegaR {n : ℕ} (v w : Coord n → ℝ) : ℝ :=
  ∑ i, (v (Sum.inl i)*w (Sum.inr i) - v (Sum.inr i)*w (Sum.inl i))

def omegaC {n : ℕ} (v w : Coord n → ℂ) : ℂ :=
  ∑ i, (v (Sum.inl i)*w (Sum.inr i) - v (Sum.inr i)*w (Sum.inl i))

/-- Orthogonality and complex linearity, PDF p.5. -/
def IsOrthogonal {n : ℕ} (A : GroupedRealMatrix n) : Prop := A.transpose*A = 1

def CommutesWithComplexStructure {n : ℕ} (A : GroupedRealMatrix n) : Prop := A*jMatrix n = jMatrix n*A

/-- Complex matrix of a complex-linear real action, PDF p.5; entrywise
complexification itself is imported from the pinned library. -/
def complexActionMatrix {n : ℕ} (A : GroupedRealMatrix n) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (A (Sum.inl i) (Sum.inl j) : ℂ) + Complex.I*(A (Sum.inr i) (Sum.inl j) : ℂ)

/-- Definition 6; used on complex-linear real matrices, PDF p.6. -/
def complexActionDet {n : ℕ} (A : GroupedRealMatrix n) : ℂ := (complexActionMatrix A).det

/-- Independent unitary predicate from Definition 4, PDF p.5. -/
def IsUnitaryReal {n : ℕ} (A : GroupedRealMatrix n) : Prop :=
  CommutesWithComplexStructure A ∧ (complexActionMatrix A).conjTranspose * complexActionMatrix A = 1

abbrev SymplecticSpace (n : ℕ) := {A : GroupedRealMatrix n // IsSymplectic A}

abbrev UnitarySpace (n : ℕ) := {A : GroupedRealMatrix n // IsUnitaryReal A}

abbrev ComplexUnitary (n : ℕ) :=
  {A : Matrix (Fin n) (Fin n) ℂ // A.conjTranspose*A = 1}

abbrev SpecialUnitary (n : ℕ) := {A : ComplexUnitary n // A.val.det = 1}

abbrev UnitCircle := {z : ℂ // ‖z‖ = 1}

/-- Symmetric part of the symplectic Lie algebra, PDF p.6 (4). -/
def IsSymmetricLie {n : ℕ} (S : GroupedRealMatrix n) : Prop :=
  S.transpose = S ∧ S.transpose*omegaMatrix n + omegaMatrix n*S = 0

abbrev SymmetricLieSpace (n : ℕ) := {S : GroupedRealMatrix n // IsSymmetricLie S}

/-- Positive symmetric square root of A^T A, by choice; fallback only off domain, pp.6–7. -/
def polarP {n : ℕ} (A : GroupedRealMatrix n) : GroupedRealMatrix n :=
  if h : ∃ P : GroupedRealMatrix n, P.transpose = P ∧ P.PosDef ∧ P*P = A.transpose*A
  then Classical.choose h else 1

/-- Computed polar projection, PDF p.42. -/
def polarU {n : ℕ} (A : GroupedRealMatrix n) : GroupedRealMatrix n := A*(polarP A)⁻¹

/-- Shift and stable generalized eigenspace; exponent 2n reaches the stable kernel, pp.13–14. -/
def shifted {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) : Module.End ℂ (Coord n → ℂ) :=
  Matrix.toLin' (complexify A) - z • 1

def generalizedSpace {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) : Submodule ℂ (Coord n → ℂ) :=
  LinearMap.ker (shifted A z ^ (2*n))

def IsEigenvalue {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) : Prop :=
  ∃ v : Coord n → ℂ, v ≠ 0 ∧ shifted A z v = 0

/-- Distinct eigenvalues and algebraic multiplicities, PDF p.14. -/
def eigenvalues {n : ℕ} (A : GroupedRealMatrix n) : Finset ℂ := (complexify A).charpoly.roots.toFinset

def algebraicMultiplicity {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) : ℕ :=
  Polynomial.rootMultiplicity z (complexify A).charpoly

/-- Real positive inertia of Im Omega(z,conj z) on E_lambda. The finite search
bound is the ambient real dimension 4n, PDF pp.12–15. -/
def kreinPositive {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) : ℕ :=
  ((Finset.range (4*n+1)).filter fun k => ∃ W : Submodule ℝ (Coord n → ℂ),
    W ≤ (generalizedSpace A z).restrictScalars ℝ ∧ Module.finrank ℝ W = k ∧
    ∀ v ∈ W, v ≠ 0 → 0 < (omegaC v (fun i => star (v i))).im).sup id

/-- Rotation from the spectral formula (18), PDF p.15. Real inertia and the
negative real multiplicity are even, so these natural divisions are exact halves. -/
def spectralRotation {n : ℕ} (A : GroupedRealMatrix n) : ℂ :=
  (-1 : ℂ)^((∑ z ∈ (eigenvalues A).filter (fun z => z.im = 0 ∧ z.re < 0),
    algebraicMultiplicity A z)/2) *
  ∏ z ∈ (eigenvalues A).filter (fun z => ‖z‖ = 1 ∧ z ≠ 1 ∧ z ≠ -1),
    z^(kreinPositive A z/2)

/-- Oriented real lift: a positive full turn has theta(t)=t and degree +1, pp.35,56. -/
def IsWindingLift (f : ℝ → ℂ) (T : ℝ) (k : ℤ) : Prop :=
  ∃ theta : ℝ → ℝ, ContinuousOn theta (Set.Icc 0 T) ∧ theta 0 = 0 ∧
    theta T = (k : ℝ) ∧ ∀ t ∈ Set.Icc 0 T,
      f t = Complex.exp (2*(Real.pi : ℂ)*Complex.I*(theta t : ℂ))

/-- Degree of a based continuous circle loop, PDF p.35; zero fallback off domain. -/
def winding (f : ℝ → ℂ) (T : ℝ) : ℤ :=
  if h : ∃ k : ℤ, IsWindingLift f T k then Classical.choose h else 0

/-- Continuous symplectic path with arbitrary endpoints, PDF pp.35,47. -/
def IsPath {n : ℕ} (p : ℝ → GroupedRealMatrix n) (T : ℝ) : Prop :=
  ContinuousOn p (Set.Icc 0 T) ∧ ∀ t ∈ Set.Icc 0 T, IsSymplectic (p t)

/-- Definition 32. Positive duration is supplied by binders, PDF p.35. -/
def IsAdmissible {n : ℕ} (p : ℝ → GroupedRealMatrix n) (T : ℝ) : Prop :=
  IsPath p T ∧ p 0 = 1 ∧ (p T-1).det ≠ 0

/-- Fixed reference representatives, PDF p.32 (35)–(37). -/
def wPlus (n : ℕ) : GroupedRealMatrix n := -1

def wMinus (n : ℕ) : GroupedRealMatrix n := Matrix.diagonal fun i => match i with
  | Sum.inl j => if j.val = 0 then 2 else -1
  | Sum.inr j => if j.val = 0 then 1/2 else -1

/-- Positive affine reparametrization, PDF pp.38,43–44. -/
def unitPath {n : ℕ} (p : ℝ → GroupedRealMatrix n) (T : ℝ) : ℝ → GroupedRealMatrix n := fun t => p (T*t)

/-- Admissible extension of Definition 33, PDF p.35. -/
def IsExtension {n : ℕ} (p e : ℝ → GroupedRealMatrix n) : Prop :=
  IsPath e 2 ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, e t = p t) ∧
    (∀ t ∈ Set.Icc (1 : ℝ) 2, (e t-1).det ≠ 0) ∧
    (e 2 = wPlus n ∨ e 2 = wMinus n)

/-- Choice is over actual extensions, not over index axioms; existence is concluded, p.35. -/
def chosenExtension {n : ℕ} (p : ℝ → GroupedRealMatrix n) : ℝ → GroupedRealMatrix n :=
  if h : ∃ e, IsExtension p e then Classical.choose h else p

/-- Genuine integer degree construction, Definition 33, PDF p.35. -/
def conleyZehnder {n : ℕ} (p : ℝ → GroupedRealMatrix n) (T : ℝ) : ℤ :=
  winding (fun t => spectralRotation (chosenExtension (unitPath p T) t)^2) 2

/-- All integer powers, including inverse powers, PDF p.15. -/
def integerPower {n : ℕ} (A : GroupedRealMatrix n) (k : ℤ) : GroupedRealMatrix n :=
  if 0 ≤ k then A^k.toNat else (A⁻¹)^(-k).toNat

/-- Maximal nilpotent height on the generalized space, PDF p.17. -/
def HasNilpotentHeight {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) (p : ℕ) : Prop :=
  (∃ v ∈ generalizedSpace A z, (shifted A z^p) v ≠ 0) ∧
    ∀ v ∈ generalizedSpace A z, (shifted A z^(p+1)) v = 0

/-- Kernel restricted to E_lambda, PDF p.17 (23). -/
def restrictedKernel {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) (j : ℕ) :
    Submodule ℂ (generalizedSpace A z) :=
  (LinearMap.ker (shifted A z^j)).comap (generalizedSpace A z).subtype

abbrev GeneralizedQuotient {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) (j : ℕ) :=
  generalizedSpace A z ⧸ restrictedKernel A z j

/-- Compact-rectangle homotopy with fixed endpoints, PDF pp.38,46. -/
def FixedHomotopic {n : ℕ} (p q : ℝ → GroupedRealMatrix n) (T : ℝ) : Prop :=
  ∃ H : ℝ × ℝ → GroupedRealMatrix n,
    ContinuousOn H (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc 0 T) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc 0 T, IsSymplectic (H (s,t))) ∧
    (∀ t ∈ Set.Icc 0 T, H (0,t) = p t ∧ H (1,t) = q t) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, H (s,0) = p 0 ∧ H (s,T) = p T)

/-- Homotopy through SP(n); the final endpoint may move in Sp*, PDF p.37. -/
def AdmissiblyHomotopic {n : ℕ} (p q : ℝ → GroupedRealMatrix n) : Prop :=
  ∃ H : ℝ × ℝ → GroupedRealMatrix n,
    ContinuousOn H (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, IsAdmissible (fun t => H (s,t)) 1) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, H (0,t) = p t ∧ H (1,t) = q t)

/-- Catenation normalized to [0,1], PDF pp.38,46. -/
def catenate {n : ℕ} (p q : ℝ → GroupedRealMatrix n) : ℝ → GroupedRealMatrix n :=
  fun t => if t ≤ 1/2 then p (2*t) else q (2*t-1)

/-- Lemma 36's translated catenation: the second argument is 2t-T, PDF p.38. -/
def translatedCatenate {n : ℕ} (phi psi : ℝ → GroupedRealMatrix n) (T : ℝ) : ℝ → GroupedRealMatrix n :=
  fun t => if t ≤ T/2 then phi (2*t) else psi (2*t-T)*phi T

/-- Sum on a coordinate half, used to retain grouped order, PDF p.16. -/
def mergeBlocks {n m : ℕ} (F : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin (n+m)) (Fin (n+m)) ℝ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks F 0 0 G)

/-- Symplectic direct sum with the source's coordinate permutation, PDF p.16. -/
def symplecticSum {n m : ℕ} (A : GroupedRealMatrix n) (B : GroupedRealMatrix m) : GroupedRealMatrix (n+m) :=
  Matrix.fromBlocks
    (mergeBlocks (A.submatrix Sum.inl Sum.inl) (B.submatrix Sum.inl Sum.inl))
    (mergeBlocks (A.submatrix Sum.inl Sum.inr) (B.submatrix Sum.inl Sum.inr))
    (mergeBlocks (A.submatrix Sum.inr Sum.inl) (B.submatrix Sum.inr Sum.inl))
    (mergeBlocks (A.submatrix Sum.inr Sum.inr) (B.submatrix Sum.inr Sum.inr))

/-- Maximum positive-subspace dimension in a finite real ambient space, pp.44–49. -/
def positiveInertia {d : Type*} [Fintype d] [DecidableEq d]
    (W : Submodule ℝ (d → ℝ)) (q : (d → ℝ) → ℝ) : ℕ :=
  ((Finset.range (Fintype.card d+1)).filter fun k =>
    ∃ L : Submodule ℝ (d → ℝ), L ≤ W ∧ Module.finrank ℝ L = k ∧
      ∀ v ∈ L, v ≠ 0 → 0 < q v).sup id

/-- Positive minus negative inertia, also on degenerate forms and zero spaces, pp.44–49. -/
def formSignature {d : Type*} [Fintype d] [DecidableEq d]
    (W : Submodule ℝ (d → ℝ)) (q : (d → ℝ) → ℝ) : ℤ :=
  (positiveInertia W q : ℤ) - positiveInertia W (fun v => -q v)

def matrixSignature {d : Type*} [Fintype d] [DecidableEq d]
    (S : Matrix d d ℝ) : ℤ :=
  formSignature ⊤ (fun v => ∑ i, ∑ j, v i*S i j*v j)

/-- Exponential and small-symmetric normalization data, PDF pp.36,52. -/
def exponentialPath {n : ℕ} (S : GroupedRealMatrix n) : ℝ → GroupedRealMatrix n :=
  fun t => NormedSpace.exp (t • (jMatrix n*S))

def IsSmallSymmetric {n : ℕ} (S : GroupedRealMatrix n) : Prop :=
  S.transpose = S ∧ ∀ z ∈ eigenvalues S, ‖z‖ < 2*Real.pi

/-- The explicitly constructed S^-, not a variable supplied by a hypothesis, PDF p.41. -/
def sMinus (n : ℕ) : GroupedRealMatrix n := Matrix.fromBlocks
  (Matrix.diagonal (fun i : Fin n => if i.val = 0 then 0 else 1))
  (Matrix.diagonal (fun i : Fin n => if i.val = 0 then -Real.log 2/Real.pi else 0))
  (Matrix.diagonal (fun i : Fin n => if i.val = 0 then -Real.log 2/Real.pi else 0))
  (Matrix.diagonal (fun i : Fin n => if i.val = 0 then 0 else 1))

def referenceMinus (n : ℕ) : ℝ → GroupedRealMatrix n := exponentialPath (Real.pi • sMinus n)

/-- Complex-linear part and determinant normalized by absolute value, PDF p.42 (45). -/
def complexLinearPart {n : ℕ} (A : GroupedRealMatrix n) : GroupedRealMatrix n :=
  (1/2 : ℝ) • (A-jMatrix n*A*jMatrix n)

def normalizedDet {n : ℕ} (A : GroupedRealMatrix n) : ℂ :=
  complexActionDet (complexLinearPart A)/(‖complexActionDet (complexLinearPart A)‖ : ℂ)

/-- Upper shear of Definition 53, PDF p.51. -/
def shear {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) : GroupedRealMatrix n := Matrix.fromBlocks 1 B 0 1

/-- Graph-reference kernel or vertical-reference intersection pulled back by A,
PDF pp.47,58. These are different subspaces. -/
def crossingSpace {n : ℕ} (vertical : Bool) (A : GroupedRealMatrix n) : Submodule ℝ (Coord n → ℝ) :=
  if vertical then
    LinearMap.ker (Matrix.toLin' (A.submatrix Sum.inl id)) ⊓
      LinearMap.ker (Matrix.toLin' ((1 : GroupedRealMatrix n).submatrix Sum.inl id))
  else LinearMap.ker (Matrix.toLin' (A-1))

/-- One-sided endpoint derivatives via the interval, PDF pp.44–50. -/
def pathDerivative {n : ℕ} (p : ℝ → GroupedRealMatrix n) (t : ℝ) : GroupedRealMatrix n :=
  derivWithin p (Set.Icc (0 : ℝ) 1) t

/-- Pullback crossing form Omega(A v,A' w), PDF pp.49,58. On ker(A-I)
this is v^T S w; for RS2 the pullback subspace is V intersect A^-1 V. -/
def crossingBilinear {n : ℕ} (p : ℝ → GroupedRealMatrix n)
    (t : ℝ) (v w : Coord n → ℝ) : ℝ :=
  omegaR ((p t).mulVec v) ((pathDerivative p t).mulVec w)

def crossingSignature {n : ℕ} (vertical : Bool) (p : ℝ → GroupedRealMatrix n) (t : ℝ) : ℤ :=
  formSignature (crossingSpace vertical (p t)) (fun v => crossingBilinear p t v v)

/-- Interior crossing set, Definitions 44,50, PDF pp.46,49. -/
def crossings {n : ℕ} (vertical : Bool) (p : ℝ → GroupedRealMatrix n) : Set ℝ :=
  {t | t ∈ Set.Ioo (0 : ℝ) 1 ∧ crossingSpace vertical (p t) ≠ ⊥}

/-- Smoothness and nondegeneracy at every crossing, including endpoints, p.49.
Nondegeneracy on the zero space is valid. Finiteness is not assumed. -/
def IsRegular {n : ℕ} (vertical : Bool) (p : ℝ → GroupedRealMatrix n) : Prop :=
  IsPath p 1 ∧ ContDiffOn ℝ ⊤ p (Set.Icc (0 : ℝ) 1) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ crossingSpace vertical (p t),
      (∀ w ∈ crossingSpace vertical (p t), crossingBilinear p t v w = 0) → v = 0

/-- Finite sum; off the finite domain the fallback is zero, PDF p.49. -/
def interiorCrossingSum {n : ℕ} (vertical : Bool) (p : ℝ → GroupedRealMatrix n) : ℤ :=
  if h : (crossings vertical p).Finite then ∑ t ∈ h.toFinset, crossingSignature vertical p t else 0

/-- Half-integer crossing value, PDF pp.46,49. -/
def regularIndex {n : ℕ} (vertical : Bool) (p : ℝ → GroupedRealMatrix n) : ℚ :=
  ((crossingSignature vertical p 0 + 2*interiorCrossingSum vertical p +
    crossingSignature vertical p 1 : ℤ) : ℚ)/2

/-- Smooth regular representative with fixed-endpoint homotopy, PDF p.46.
Choice imposes no index value or invariance assumption. -/
def regularPathRepresentative {n : ℕ} (vertical : Bool) (p : ℝ → GroupedRealMatrix n) : ℝ → GroupedRealMatrix n :=
  if h : ∃ q, IsRegular vertical q ∧ FixedHomotopic p q 1 then Classical.choose h else p

/-- Graph Robbin–Salamon index reconstructed by Definitions 44,46 and (52), pp.46–49. -/
def robbinSalamon {n : ℕ} (p : ℝ → GroupedRealMatrix n) : ℚ := regularIndex false (regularPathRepresentative false p)

/-- Separate vertical-reference index of section 7.5, PDF p.58. -/
def robbinSalamonVertical {n : ℕ} (p : ℝ → GroupedRealMatrix n) : ℚ := regularIndex true (regularPathRepresentative true p)

/-- Half-integer family, with arbitrary endpoint degeneracies, PDF pp.47,53. -/
def IsHalfIntegerFamily (f : ∀ n : ℕ, (ℝ → GroupedRealMatrix n) → ℚ) : Prop :=
  ∀ n, 1 ≤ n → ∀ p, IsPath p 1 → ∃ k : ℤ, f n p = (k : ℚ)/2

/-- Homotopy/catenation/zero core shared by the characterizations, PDF pp.52–56. -/
def RsCore (f : ∀ n : ℕ, (ℝ → GroupedRealMatrix n) → ℚ) : Prop :=
  IsHalfIntegerFamily f ∧
  (∀ n, 1 ≤ n → ∀ p q, IsPath p 1 → IsPath q 1 → FixedHomotopic p q 1 → f n p = f n q) ∧
  (∀ n, 1 ≤ n → ∀ p q, IsPath p 1 → IsPath q 1 → p 1 = q 0 →
    f n (catenate p q) = f n p + f n q) ∧
  (∀ n, 1 ≤ n → ∀ p, IsPath p 1 → ∀ k : ℕ,
    (∀ t ∈ Set.Icc (0 : ℝ) 1, Module.finrank ℝ (crossingSpace false (p t)) = k) → f n p = 0)

/-- Four axioms: normalization includes singular and zero S, PDF p.52. -/
def RsFourAxioms (f : ∀ n : ℕ, (ℝ → GroupedRealMatrix n) → ℚ) : Prop :=
  RsCore f ∧ (∀ n, 1 ≤ n → ∀ S : GroupedRealMatrix n, IsSmallSymmetric S →
    f n (exponentialPath S) = (matrixSignature S : ℚ)/2)

/-- Dimension-family product, PDF pp.53,56. -/
def RsProduct (f : ∀ n : ℕ, (ℝ → GroupedRealMatrix n) → ℚ) : Prop :=
  ∀ n m, 1 ≤ n → 1 ≤ m → ∀ p q, IsPath p 1 → IsPath q 1 →
    f (n+m) (fun t => symplecticSum (p t) (q t)) = f n p + f m q

/-- Seven properties, including generalization, naturality and -tB shear, PDF p.53. -/
def RsSevenAxioms (f : ∀ n : ℕ, (ℝ → GroupedRealMatrix n) → ℚ) : Prop :=
  RsCore f ∧ RsProduct f ∧
  (∀ n, 1 ≤ n → ∀ p, IsAdmissible p 1 → f n p = (conleyZehnder p 1 : ℚ)) ∧
  (∀ n, 1 ≤ n → ∀ p q, IsPath p 1 → IsPath q 1 →
    f n (fun t => q t*p t*(q t)⁻¹) = f n p) ∧
  (∀ n, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℝ, B.transpose = B →
    f n (fun t => shear ((-t) • B)) = (matrixSignature B : ℚ)/2)

/-- Six properties, with distinct nondegenerate-signature and shear normalizations, p.56. -/
def RsSixAxioms (f : ∀ n : ℕ, (ℝ → GroupedRealMatrix n) → ℚ) : Prop :=
  RsCore f ∧ RsProduct f ∧
  (∀ n, 1 ≤ n → ∀ S : GroupedRealMatrix n, IsSmallSymmetric S → S.det ≠ 0 →
    f n (exponentialPath S) = (matrixSignature S : ℚ)/2) ∧
  (∀ n, 1 ≤ n → ∀ B : Matrix (Fin n) (Fin n) ℝ, B.transpose = B →
    f n (fun t => shear ((-t) • B)) = (matrixSignature B : ℚ)/2)

/-- Homotopy, loop and signature characterization, PDF p.40. -/
def CzThreeAxioms {n : ℕ} (f : (ℝ → GroupedRealMatrix n) → ℤ) : Prop :=
  (∀ p q, IsAdmissible p 1 → IsAdmissible q 1 → AdmissiblyHomotopic p q → f p = f q) ∧
  (∀ p phi, IsAdmissible p 1 → IsPath phi 1 → phi 0 = 1 → phi 1 = 1 →
    f (fun t => phi t*p t) = f p + 2*winding (fun t => spectralRotation (phi t)) 1) ∧
  (∀ S : GroupedRealMatrix n, IsSmallSymmetric S → S.det ≠ 0 → 2*f (exponentialPath S) = matrixSignature S)

/-- Small-case sanity for the source's standard form, PDF p.4. -/
example : omegaMatrix 0 = 0 := by ext i; exact Fin.elim0 (i.elim id id)

/-- The imported symplectic predicate fixes the identity, PDF p.4. -/
example (n : ℕ) : IsSymplectic (1 : GroupedRealMatrix n) := by
  simp [IsSymplectic]

/-- First symplectic plane of W^-, PDF p.32. -/
example : wMinus 1 (Sum.inl 0) (Sum.inl 0) = 2 := by simp [wMinus]

example : wMinus 1 (Sum.inr 0) (Sum.inr 0) = (1/2 : ℝ) := by simp [wMinus]

/-- Zero-space signature sanity, PDF pp.44–49. -/
example : matrixSignature (0 : Matrix (Fin 0) (Fin 0) ℝ) = 0 := by
  simp [matrixSignature, formSignature, positiveInertia]

/-- Positive full-turn lift sanity, PDF pp.35,56. -/
example : IsWindingLift
    (fun t => Complex.exp (2*(Real.pi : ℂ)*Complex.I*(t : ℂ))) 1 1 := by
  refine ⟨id, continuous_id.continuousOn, rfl, ?_, ?_⟩
  · norm_num
  · intro t ht
    rfl

/-- Zeroth integer power sanity, PDF p.15. -/
example (n : ℕ) : integerPower (1 : GroupedRealMatrix n) 0 = 1 := by simp [integerPower]

/-- Identity has the full graph-reference kernel, PDF p.47. -/
example (n : ℕ) : crossingSpace false (1 : GroupedRealMatrix n) = ⊤ := by simp [crossingSpace]

/-- The shear's upper-right block is B, PDF p.51. -/
example {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    shear B (Sum.inl i) (Sum.inr j) = B i j := rfl

/-- Theorem 10(1)–(3), dimension two, PDF pp.8,11. -/
def RotationAxiomsTwo (r : GroupedRealMatrix 1 → ℂ) : Prop :=
  ContinuousOn r {A | IsSymplectic A} ∧ (∀ A, IsSymplectic A → ‖r A‖ = 1) ∧
  (∀ A, IsSymplectic A → IsOrthogonal A → r A = complexActionDet A) ∧
  (∀ A K, IsSymplectic A → IsSymplectic K → r (K*A*K⁻¹) = r A) ∧
  (∀ A, IsSymplectic A → (∀ z ∈ eigenvalues A, ‖z‖ ≠ 1) → r A = 1 ∨ r A = -1)

/-- Graph as an actual linear subspace, PDF p.47. -/
def graphSpace {n : ℕ} (A : GroupedRealMatrix n) : Submodule ℝ ((Coord n → ℝ) × (Coord n → ℝ)) :=
  LinearMap.range ((LinearMap.id : (Coord n → ℝ) →ₗ[ℝ] (Coord n → ℝ)).prod (Matrix.toLin' A))

/-- Lagrangian in the doubled form -Omega direct_sum Omega, PDF p.47. -/
def IsGraphLagrangian {n : ℕ} (W : Submodule ℝ ((Coord n → ℝ) × (Coord n → ℝ))) : Prop :=
  Module.finrank ℝ W = 2*n ∧ ∀ v ∈ W, ∀ w ∈ W, -omegaR v.1 w.1 + omegaR v.2 w.2 = 0

/-- Four rotation axioms for the positive-dimension family of Theorem 10,
PDF p.8. Functions are compared only on symplectic matrices in dimensions n>=1. -/
def RotationFamilyAxioms (r : ∀ n : ℕ, GroupedRealMatrix n → ℂ) : Prop :=
  (∀ n, 1 ≤ n → ContinuousOn (r n) {A | IsSymplectic A}) ∧
  (∀ n, 1 ≤ n → ∀ A, IsSymplectic A → ‖r n A‖ = 1) ∧
  (∀ n, 1 ≤ n → ∀ A, IsSymplectic A → IsOrthogonal A →
    r n A = complexActionDet A) ∧
  (∀ n, 1 ≤ n → ∀ A K, IsSymplectic A → IsSymplectic K →
    r n (K*A*K⁻¹) = r n A) ∧
  (∀ n, 1 ≤ n → ∀ A, IsSymplectic A →
    (∀ z ∈ eigenvalues A, ‖z‖ ≠ 1) → r n A = 1 ∨ r n A = -1) ∧
  (∀ n m, 1 ≤ n → 1 ≤ m → ∀ A : GroupedRealMatrix n, ∀ B : GroupedRealMatrix m,
    IsSymplectic A → IsSymplectic B →
      r (n+m) (symplecticSum A B) = r n A*r m B)

/-- Circle-range sanity in the first positive dimension. -/
example (r : ∀ n : ℕ, GroupedRealMatrix n → ℂ) (hr : RotationFamilyAxioms r)
    (A : GroupedRealMatrix 1) (hA : IsSymplectic A) : ‖r 1 A‖ = 1 :=
  hr.2.1 1 (by norm_num) A hA

/-- Real Krein form before restricting to E_lambda; conjugate the second
vector explicitly, PDF pp.12,15, formula (18). -/
def kreinPairing {n : ℕ} (v w : Coord n → ℂ) : ℝ :=
  (omegaC v (fun i => star (w i))).im

/-- Zero-vector sanity for the real Krein form. -/
example {n : ℕ} (v : Coord n → ℂ) : kreinPairing v 0 = 0 := by
  simp [kreinPairing, omegaC]

/-- Multiplicity of an eigenvalue of the first kind, Definition 17 and
Remark 18, PDF p.15. At +1 and -1 use half the complex generalized dimension;
elsewhere on S1 use half the real positive inertia. -/
def firstKindMultiplicity {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) : ℕ :=
  if ‖z‖ < 1 then algebraicMultiplicity A z
  else if ‖z‖ = 1 then
    if z = 1 ∨ z = -1 then Module.finrank ℂ (generalizedSpace A z)/2
    else kreinPositive A z/2
  else 0

/-- Inside-circle multiplicity sanity, including repeated roots. -/
example {n : ℕ} (A : GroupedRealMatrix n) (z : ℂ) (hz : ‖z‖ < 1) :
    firstKindMultiplicity A z = algebraicMultiplicity A z := by
  simp [firstKindMultiplicity, hz]

/-- The -1 case uses the half-dimension convention of Definition 17. -/
example {n : ℕ} (A : GroupedRealMatrix n) :
    firstKindMultiplicity A (-1) = Module.finrank ℂ (generalizedSpace A (-1))/2 := by
  simp [firstKindMultiplicity]

/-- Five image-index properties on all positive dimensions, PDF p.58.
Homotopy is the full iff for paths with the same matrix endpoints. -/
def ImageIndexAxioms (f : ∀ n : ℕ, (ℝ → GroupedRealMatrix n) → ℚ) : Prop :=
  IsHalfIntegerFamily f ∧
  (∀ n, 1 ≤ n → ∀ p q : ℝ → GroupedRealMatrix n,
    IsPath p 1 → IsPath q 1 → p 0 = q 0 → p 1 = q 1 →
      (FixedHomotopic p q 1 ↔ f n p = f n q)) ∧
  (∀ n, 1 ≤ n → ∀ p q : ℝ → GroupedRealMatrix n,
    IsPath p 1 → IsPath q 1 → p 1 = q 0 → f n (catenate p q) = f n p + f n q) ∧
  RsProduct f ∧
  (∀ n, 1 ≤ n → ∀ p : ℝ → GroupedRealMatrix n, IsPath p 1 → ∀ k : ℕ, k ≤ n →
    (∀ t ∈ Set.Icc (0 : ℝ) 1, Module.finrank ℝ (crossingSpace true (p t)) = k) →
    f n p = 0) ∧
  (∀ n, 1 ≤ n → ∀ B : ℝ → Matrix (Fin n) (Fin n) ℝ,
    ContinuousOn B (Set.Icc (0 : ℝ) 1) →
    (∀ t ∈ Set.Icc (0 : ℝ) 1, (B t).transpose = B t) →
    f n (fun t => shear (B t)) =
      (matrixSignature (B 0) : ℚ)/2 - (matrixSignature (B 1) : ℚ)/2)

/-- Definitional sanity: the image characterization includes the actual
half-integer range condition, rather than an unrestricted rational range. -/
example (f : ∀ n : ℕ, (ℝ → GroupedRealMatrix n) → ℚ) (hf : ImageIndexAxioms f) :
    IsHalfIntegerFamily f := hf.1

end QAlgorithms.Papers.Independent.Gap50repair.P01


