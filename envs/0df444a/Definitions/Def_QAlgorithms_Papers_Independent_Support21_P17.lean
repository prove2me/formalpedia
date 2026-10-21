-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17
-- name    : QAlgorithms_Papers_Independent_Support21_P17
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T04:37:26.958761+00:00
-- url     : https://prove2.me/theorems/8fa22d9d-f206-4ff0-b6b6-c948b516cbf5
-- title:
--   Definitions for Radon-Nikodym derivatives of quantum operations
-- statement:
--   The objects the formalized statements of *Radon-Nikodym derivatives of quantum operations* (arXiv:math-ph/0303056) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `SeparableHilbertSpace`: PDF pp.2–3: a complex separable Hilbert space; the zero space is permitted.
--   - `HilbertEndomorphism`: PDF p.2: bounded complex-linear endomorphisms.
--   - `completedTensorVector`: PDF p.3, (5): an elementary tensor in the completed space.
--   - `compress`: PDF p.3: compression by a bounded dilation operator.
--   - `ultraweak`: PDF p.3: the ultraweak topology, concretely induced by the trace-class tests.
--   - `ConcreteUltraweakNormal`: PDF p.3: normality relative to the specified faithful concrete realization of A.
--   - `GramCompletelyPositive`: PDF p.3, (1): the complex Gram sum is real and nonnegative; inner products are conjugate-linear in their first argument. This is complete positivity, not positivity.
--   - `IsNormalCP`: PDF p.4: CP(A;H) contains normal CP maps.
--   - `CompletelyDominated`: PDF p.4: complete domination is positivity of the entire difference map.
--   - `IsMinimal`: PDF p.3: minimality is the closed linear span of all pi(a)V eta.
--   - `CommutesWithRepresentation`: PDF p.7: the commutant of the represented algebra.
--   - `PositiveContraction`: PDF p.7: a positive contraction, in operator order.
--   - `IsCanonical`: PDF pp.3,8: canonical tensor dilations are minimal.
--   - `IsSubunitalNormalCP`: PDF pp.4–5: a quantum operation is normal, CP, and subunital.
--   - `IsUnitalNormalCP`: PDF p.4: channels are unital Heisenberg-picture maps.
--   - `UniformlyEquivalent`: PDF p.12: mutual domination by constants strictly greater than one.
--   - `IsInducedKraus`: PDF pp.3,9, (5): the fixed Kraus family is induced by a complete environment basis.
--   - `KernelContraction`: PDF pp.9–10: kernel order is positive-definite order.
--   - `HasKernelExpansion`: PDF p.9: double Kraus series in the strong topology, with independent finite rectangular truncations. Absolute operator-norm summability is not asserted.
--   - `BlockVector`: PDF p.5, (7): the finite direct sum used for matrix amplifications.
--   - `applyOperatorBlocks`: PDF p.5: a block operator acts on the Hilbert direct sum with its L2 norm.
--   - `cbValues`: PDF p.5: all amplified output norms on the full operator-norm unit ball.
--   - `completelyBoundedNorm`: PDF p.5: CB norm. The set contains zero; on the CP maps and differences of CP maps below it is bounded above. It therefore never uses the junk unbounded real supremum.
--   - `scaledChoi`: PDF p.14: output-first RN coordinate F_T=m J(T), not the normalized Choi state.
--   - `tracialDerivative`: PDF p.15: the full derivative relative to the tracial preparation channel. This is the generalized (bounded c-domination) derivative, not necessarily a contraction.
--   - `fromScaledChoi`: PDF pp.14–15, (12): the inverse RN coordinate map, defined on every matrix.
--   - `tracialV`: PDF p.14: the constructed canonical dilation of the tracial preparation channel.
--   - `tracialPreparation`: PDF p.14: the tracial preparation channel Phi_(m,n).
--   - `matrixCBNorm`: PDF p.5: finite-dimensional CB norm with all ancilla dimensions and the full operator-norm unit ball. Every finite-dimensional complex-linear map is CB.
--   - `matrixRank`: PDF p.15: algebraic rank of a finite matrix, including rank zero.
--   - `finiteHilbert`: PDF pp.14–15: the physical finite-dimensional Hilbert space with its fixed basis.
--   - `matrixOp`: PDF p.14: the bounded operator represented by a matrix in the fixed basis.
--   - `IsMatrixCanonical`: PDF p.15: minimal tensor dilation of a matrix map, allowing an arbitrary separable environment before its finite dimensionality has been concluded.
--   - `densityInverse`: PDF p.16: the faithful state's density inverse, used only in finite dimension.
--   - `faithfulChoi`: PDF p.16: weighted RN coordinates. Strict positivity of p is a theorem hypothesis.
--   - `faithfulPreparation`: PDF p.16: the preparation channel Phi_omega(A)=omega(A)I.
--   - `faithfulV`: PDF p.16: the constructed weighted Stinespring isometry, in input/output/input order.
--   - `bellCompression`: PDF pp.15–16: compression of F2 tensor F1 by the normalized intermediate Bell vector. The factor order is d,n,n,m, and the two middle indices are identified.
-- source:
--   Radon-Nikodym derivatives of quantum operations, arXiv:math-ph/0303056v3, https://arxiv.org/abs/math-ph/0303056v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P50
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

/-! Raginsky, arXiv:math-ph/0303056v3. Page numbers are PDF pages.
The Heisenberg convention is used throughout. Compatible accepted interfaces are imported; new paper-local definitions have complete bodies.
The four defective printed assertions and the two trace-class interface gaps are recorded
in the unit's HARD.md; no finite-dimensional replacement is made for a general result. -/

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct
open Filter

namespace QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)
open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)
open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)
open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

/-- PDF pp.2–3: a complex separable Hilbert space; the zero space is permitted. -/
structure SeparableHilbertSpace where
  carrier : Type
  [normed : NormedAddCommGroup carrier]
  [innerProduct : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]
  [separable : TopologicalSpace.SeparableSpace carrier]

attribute [instance] SeparableHilbertSpace.normed SeparableHilbertSpace.innerProduct SeparableHilbertSpace.complete SeparableHilbertSpace.separable

/-- Use a bundled Hilbert space as its underlying vector type. -/
instance separableHilbertCoeSort : CoeSort SeparableHilbertSpace Type := ⟨SeparableHilbertSpace.carrier⟩

/-- PDF p.2: bounded complex-linear endomorphisms. -/
abbrev HilbertEndomorphism (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] := H →L[ℂ] H

/-- PDF p.3, (5): an elementary tensor in the completed space. -/
def completedTensorVector {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (x : H) (y : E) : NoiseSpace H E :=
  (UniformSpace.Completion.toComplL :
    TensorProduct ℂ H E →L[ℂ] NoiseSpace H E) (TensorProduct.tmul ℂ x y)

/-- PDF p.3: compression by a bounded dilation operator. -/
def compress {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (V : H →L[ℂ] K) (B : HilbertEndomorphism K) : HilbertEndomorphism H :=
  (ContinuousLinearMap.adjoint V).comp (B.comp V)

/-- PDF p.3: the ultraweak topology, concretely induced by the trace-class tests. -/
def ultraweak (H : SeparableHilbertSpace) : TopologicalSpace (HilbertEndomorphism H) :=
  TopologicalSpace.induced
    (fun A : HilbertEndomorphism H => fun t : UltraweakTest H =>
      ∑' n, inner ℂ (t.left n) (A (t.right n))) inferInstance

/-- PDF p.3: normality relative to the specified faithful concrete realization of A. -/
def ConcreteUltraweakNormal {A : Type*} [CStarAlgebra A] {G H : SeparableHilbertSpace}
    (rho : A →⋆ₐ[ℂ] HilbertEndomorphism G) (T : A →ₗ[ℂ] HilbertEndomorphism H) : Prop :=
  @Continuous A (HilbertEndomorphism H) (TopologicalSpace.induced rho (ultraweak G)) (ultraweak H) T

/-- PDF p.3, (1): the complex Gram sum is real and nonnegative; inner products
are conjugate-linear in their first argument. This is complete positivity, not positivity. -/
def GramCompletelyPositive {A : Type*} [CStarAlgebra A] {H : SeparableHilbertSpace}
    (T : A →ₗ[ℂ] HilbertEndomorphism H) : Prop :=
  ∀ (n : ℕ) (a : Fin n → A) (eta : Fin n → H),
    let z := ∑ i, ∑ j, inner ℂ (eta i) (T (star (a i) * a j) (eta j))
    z.im = 0 ∧ 0 ≤ z.re

/-- PDF p.4: CP(A;H) contains normal CP maps. -/
def IsNormalCP {A : Type*} [CStarAlgebra A] {G H : SeparableHilbertSpace}
    (rho : A →⋆ₐ[ℂ] HilbertEndomorphism G) (T : A →ₗ[ℂ] HilbertEndomorphism H) : Prop :=
  GramCompletelyPositive T ∧ ConcreteUltraweakNormal rho T

/-- PDF p.4: complete domination is positivity of the entire difference map. -/
def CompletelyDominated {A : Type*} [CStarAlgebra A] {H : SeparableHilbertSpace}
    (S T : A →ₗ[ℂ] HilbertEndomorphism H) : Prop := GramCompletelyPositive (T - S)

/-- PDF p.3: minimality is the closed linear span of all pi(a)V eta. -/
def IsMinimal {A : Type*} [CStarAlgebra A] {H K : SeparableHilbertSpace}
    (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (V : H →L[ℂ] K) : Prop :=
  (Submodule.span ℂ {z : K | ∃ a : A, ∃ eta : H, z = pi a (V eta)}).topologicalClosure = ⊤

/-- PDF p.7: the commutant of the represented algebra. -/
def CommutesWithRepresentation {A : Type*} [CStarAlgebra A] {K : SeparableHilbertSpace}
    (pi : A →⋆ₐ[ℂ] HilbertEndomorphism K) (F : HilbertEndomorphism K) : Prop :=
  ∀ a, (pi a).comp F = F.comp (pi a)

/-- PDF p.7: a positive contraction, in operator order. -/
def PositiveContraction {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (F : HilbertEndomorphism K) : Prop :=
  F.IsPositive ∧ (ContinuousLinearMap.id ℂ K - F).IsPositive

/-- PDF pp.3,8: canonical tensor dilations are minimal. -/
def IsCanonical {H K E : SeparableHilbertSpace} (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K)
    (V : K →L[ℂ] NoiseSpace H E) : Prop :=
  (∀ A, T A = compress V (completedTensorMap A (ContinuousLinearMap.id ℂ E))) ∧
  (Submodule.span ℂ {z : NoiseSpace H E |
    ∃ A : HilbertEndomorphism H, ∃ eta : K, z = completedTensorMap A (ContinuousLinearMap.id ℂ E) (V eta)}).topologicalClosure = ⊤

/-- PDF pp.4–5: a quantum operation is normal, CP, and subunital. -/
def IsSubunitalNormalCP {H K : SeparableHilbertSpace} (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) : Prop :=
  IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T ∧
    (ContinuousLinearMap.id ℂ K - T (ContinuousLinearMap.id ℂ H)).IsPositive

/-- PDF p.4: channels are unital Heisenberg-picture maps. -/
def IsUnitalNormalCP {H K : SeparableHilbertSpace} (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) : Prop :=
  IsNormalCP (StarAlgHom.id ℂ (HilbertEndomorphism H)) T ∧
    T (ContinuousLinearMap.id ℂ H) = ContinuousLinearMap.id ℂ K

/-- PDF p.12: mutual domination by constants strictly greater than one. -/
def UniformlyEquivalent {H K : SeparableHilbertSpace} (S T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) : Prop :=
  ∃ c d : ℝ, 1 < c ∧ 1 < d ∧ CompletelyDominated S ((c : ℂ) • T) ∧ CompletelyDominated T ((d : ℂ) • S)

/-- PDF pp.3,9, (5): the fixed Kraus family is induced by a complete environment basis. -/
def IsInducedKraus {H K E : SeparableHilbertSpace} {X : Type}
    (e : HilbertBasis X ℂ E) (V : K →L[ℂ] NoiseSpace H E) (W : X → K →L[ℂ] H) : Prop :=
  ∀ eta, HasSum (fun x => completedTensorVector (W x eta) (e x)) (V eta)

/-- PDF pp.9–10: kernel order is positive-definite order. -/
def KernelContraction {X : Type} (C : X → X → ℂ) : Prop :=
  PositiveKernel C ∧ PositiveKernel (fun x y => (if x = y then 1 else 0) - C x y)

/-- PDF p.9: double Kraus series in the strong topology, with independent finite
rectangular truncations. Absolute operator-norm summability is not asserted. -/
def HasKernelExpansion {H K : SeparableHilbertSpace} {X : Type}
    (W : X → K →L[ℂ] H) (C : X → X → ℂ) (S : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) : Prop :=
  ∀ (A : HilbertEndomorphism H) (eta : K),
    Tendsto (fun s : Finset X × Finset X =>
      ∑ x ∈ s.1, ∑ y ∈ s.2,
        C x y • (ContinuousLinearMap.adjoint (W x)) (A (W y eta)))
      atTop (𝓝 (S A eta))

/-- PDF p.5, (7): the finite direct sum used for matrix amplifications. -/
abbrev BlockVector (H : SeparableHilbertSpace) (n : ℕ) := PiLp 2 (fun _ : Fin n => H)

/-- PDF p.5: a block operator acts on the Hilbert direct sum with its L2 norm. -/
def applyOperatorBlocks {H : SeparableHilbertSpace} {n : ℕ} (M : Fin n → Fin n → HilbertEndomorphism H)
    (x : BlockVector H n) : BlockVector H n :=
  WithLp.toLp 2 (fun i => ∑ j, M i j (x j))

/-- PDF p.5: all amplified output norms on the full operator-norm unit ball. -/
def cbValues {H K : SeparableHilbertSpace} (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) : Set ℝ :=
  {r | ∃ (n : ℕ) (M : Fin n → Fin n → HilbertEndomorphism H) (x : BlockVector K n),
    (∀ y : BlockVector H n, ‖applyOperatorBlocks M y‖ ≤ ‖y‖) ∧ ‖x‖ ≤ 1 ∧
    r = ‖applyOperatorBlocks (fun i j => T (M i j)) x‖}

/-- PDF p.5: CB norm. The set contains zero; on the CP maps and differences of CP
maps below it is bounded above. It therefore never uses the junk unbounded real supremum. -/
def completelyBoundedNorm {H K : SeparableHilbertSpace} (T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K) : ℝ := sSup (cbValues T)

/-- Sanity for the completed tensor convention: a zero left vector gives zero. -/
example {H E : SeparableHilbertSpace} (e : E) : completedTensorVector (0 : H) e = 0 := by
  simp [completedTensorVector]

/-- Sanity for complete positivity: the zero map is CP, including the empty Gram sum. -/
example {A : Type*} [CStarAlgebra A] {H : SeparableHilbertSpace} :
    GramCompletelyPositive (0 : A →ₗ[ℂ] HilbertEndomorphism H) := by
  intro n a eta
  simp

/-- Sanity for the CP order: every map is completely dominated by itself. -/
example {A : Type*} [CStarAlgebra A] {H : SeparableHilbertSpace} (T : A →ₗ[ℂ] HilbertEndomorphism H) : CompletelyDominated T T := by
  unfold CompletelyDominated
  rw [sub_self]
  intro n a eta
  simp

/-- PDF p.14: output-first RN coordinate F_T=m J(T), not the normalized Choi state. -/
def scaledChoi {m n : ℕ} (T : Lin m n) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  fun p q => (m : ℂ) * T (Matrix.single p.2 q.2 1) p.1 q.1

/-- PDF p.15: the full derivative relative to the tracial preparation channel.
This is the generalized (bounded c-domination) derivative, not necessarily a contraction. -/
def tracialDerivative {m n : ℕ} (T : Lin m n) :
    Matrix (Fin m × (Fin n × Fin m)) (Fin m × (Fin n × Fin m)) ℂ :=
  Matrix.kronecker (1 : M m) (scaledChoi T)

/-- PDF pp.14–15, (12): the inverse RN coordinate map, defined on every matrix. -/
def fromScaledChoi {m n : ℕ} (F : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) : Lin m n :=
  coefficientMap (fun mu nu i j => (m : ℂ)⁻¹ * F (mu, i) (nu, j))

/-- PDF p.14: the constructed canonical dilation of the tracial preparation channel. -/
def tracialV (m n : ℕ) : Matrix (Fin m × (Fin n × Fin m)) (Fin n) ℂ :=
  fun p nu => if p.1 = p.2.2 ∧ p.2.1 = nu then ((Real.sqrt (m : ℝ))⁻¹ : ℝ) else 0

/-- PDF p.14: the tracial preparation channel Phi_(m,n). -/
def tracialPreparation (m n : ℕ) : Lin m n :=
  coefficientMap (fun mu nu i j => if mu = nu ∧ i = j then (m : ℂ)⁻¹ else 0)

/-- PDF p.5: finite-dimensional CB norm with all ancilla dimensions and the full
operator-norm unit ball. Every finite-dimensional complex-linear map is CB. -/
def matrixCBNorm {m n : ℕ} (T : Lin m n) : ℝ :=
  sSup {r : ℝ | ∃ (a : ℕ) (X : Matrix (Fin a × Fin m) (Fin a × Fin m) ℂ),
    specNorm X ≤ 1 ∧ r = specNorm (idTensorSuperop T X)}

/-- PDF p.15: algebraic rank of a finite matrix, including rank zero. -/
def matrixRank {I : Type*} [Fintype I] (F : Matrix I I ℂ) : ℕ :=
  Module.finrank ℂ (LinearMap.range F.mulVecLin)

/-- PDF pp.14–15: the physical finite-dimensional Hilbert space with its fixed basis. -/
def finiteHilbert (m : ℕ) : SeparableHilbertSpace where
  carrier := EuclideanSpace ℂ (Fin m)

/-- PDF p.14: the bounded operator represented by a matrix in the fixed basis. -/
def matrixOp {m : ℕ} (A : M m) : HilbertEndomorphism (finiteHilbert m) :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

/-- PDF p.15: minimal tensor dilation of a matrix map, allowing an arbitrary separable
environment before its finite dimensionality has been concluded. -/
def IsMatrixCanonical {m n : ℕ} (T : Lin m n) (E : SeparableHilbertSpace)
    (V : finiteHilbert n →L[ℂ] NoiseSpace (finiteHilbert m) E) : Prop :=
  (∀ A, matrixOp (T A) = compress V (completedTensorMap (matrixOp A) (ContinuousLinearMap.id ℂ E))) ∧
  (Submodule.span ℂ {z : NoiseSpace (finiteHilbert m) E |
    ∃ A : M m, ∃ eta : finiteHilbert n,
      z = completedTensorMap (matrixOp A) (ContinuousLinearMap.id ℂ E) (V eta)}).topologicalClosure = ⊤

/-- PDF p.16: the faithful state's density inverse, used only in finite dimension. -/
def densityInverse {m : ℕ} (p : Fin m → ℝ) : M m :=
  Matrix.diagonal (fun i => (p i : ℂ)⁻¹)

/-- PDF p.16: weighted RN coordinates. Strict positivity of p is a theorem hypothesis. -/
def faithfulChoi {m n : ℕ} (p : Fin m → ℝ) (T : Lin m n) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  fun x y => ((Real.sqrt (p x.2 * p y.2) : ℝ) : ℂ)⁻¹ *
    T (Matrix.single x.2 y.2 1) x.1 y.1

/-- PDF p.16: the preparation channel Phi_omega(A)=omega(A)I. -/
def faithfulPreparation {m : ℕ} (n : ℕ) (p : Fin m → ℝ) : Lin m n :=
  coefficientMap (fun mu nu i j => if mu = nu ∧ i = j then (p i : ℂ) else 0)

/-- PDF p.16: the constructed weighted Stinespring isometry, in input/output/input order. -/
def faithfulV {m : ℕ} (n : ℕ) (p : Fin m → ℝ) :
    Matrix (Fin m × (Fin n × Fin m)) (Fin n) ℂ :=
  fun x nu => if x.1 = x.2.2 ∧ x.2.1 = nu then (Real.sqrt (p x.1) : ℝ) else 0

/-- PDF pp.15–16: compression of F2 tensor F1 by the normalized intermediate Bell
vector. The factor order is d,n,n,m, and the two middle indices are identified. -/
def bellCompression {m n d : ℕ}
    (F2 : Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ)
    (F1 : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ :=
  fun x y => (n : ℂ)⁻¹ * ∑ mu, ∑ nu, F2 (x.1, mu) (y.1, nu) * F1 (mu, x.2) (nu, y.2)

/-- Sanity: a zero coefficient array gives the zero complex-linear map. -/
example {m n : ℕ} : coefficientMap (fun (_ _ : Fin n) (_ _ : Fin m) => 0) = 0 := by
  ext A mu nu
  change (∑ i, ∑ j, (0 : ℂ) * A i j) = 0
  simp

/-- Sanity: the zero map has zero output-first RN coordinate. -/
example {m n : ℕ} : scaledChoi (0 : Lin m n) = 0 := by
  ext x y
  simp [scaledChoi]

end QAlgorithms.Papers.Independent.Support21.P17


