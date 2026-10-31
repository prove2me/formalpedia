-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23
-- name    : QAlgorithms_Papers_Independent_Intake100_P23
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T16:36:31.074797+00:00
-- url     : https://prove2.me/theorems/c3a66996-177b-4df1-a659-98ec2d1718a4
-- title:
--   Definitions for Introduction to representations of the canonical commutation and anticommutation relations
-- statement:
--   The objects the formalized statements of *Introduction to representations of the canonical commutation and anticommutation relations* (arXiv:math-ph/0511030) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsCCR`: PDF p.9, (9): unitary Weyl representation with the source's minus sign.
--   - `Antisymmetric`: PDF pp.6,9: antisymmetry of the real bilinear form, without nondegeneracy.
--   - `FormNondegenerate`: PDF p.6: nondegeneracy tests every vector in the first argument.
--   - `WeylRegular`: PDF p.10: strong continuity along every real one-parameter subgroup.
--   - `HilbertIrreducible`: PDF pp.10,15: no nontrivial closed complex invariant subspace.
--   - `Cyclic`: PDF p.10: density of the complex linear span of the Weyl orbit.
--   - `GaussianCharacteristic`: PDF p.38, (70): symmetric covariance and its Gaussian characteristic function. The equation at zero forces normalization; no positivity assumption is added.
--   - `QuasiFreeCCR`: PDF p.38: existence of a cyclic quasi-free vector.
--   - `EquivalentCCR`: PDF p.10: unitary equivalence between possibly different representation spaces.
--   - `SamePhase`: PDF pp.13,17: equality modulo a scalar of absolute value one.
--   - `PreservesWeylForm`: PDF pp.6,13: preservation of the specified real bilinear form.
--   - `ImplementsCCR`: PDF p.13, (23): U implements the specified transformation.
--   - `canonicalPlane`: PDF pp.1,11, (16): one-degree canonical symplectic form.
--   - `IsCAR`: PDF p.14, (25)--(26): real linearity, self-adjointness, and factor-2 CAR. Continuity of the label map is a consequence, not an input assumption.
--   - `EquivalentCAR`: PDF p.15: equivalence intertwines all bounded CAR fields.
--   - `ConjugatesCAR`: PDF p.17, (32): implementation of an orthogonal transformation.
--   - `tensorOperator`: PDF p.7: bounded tensor action on the completed Hilbert tensor product. The canonical completion embedding is uniformly inducing and has dense range, so this extension uses its actual branch rather than the zero default.
--   - `sumForm`: PDF p.10: direct-sum bilinear form.
--   - `spinX`: PDF p.16: sigma_1 entries in the ordered basis (false,true).
--   - `pauliYEntry`: PDF p.16: the accepted Pauli Y matrix reindexed by false=0, true=1. Its upper-right entry is -i and lower-left entry is +i.
--   - `pauliZEntry`: PDF p.16: sigma_3 entries diag(1,-1).
--   - `jordanWignerEven`: PDF p.16: ordered Jordan-Wigner generators on the n-fold qubit tensor basis.
--   - `jordanWignerParity`: PDF p.16: I_n is the product of sigma_3 in all n slots; I_0 is 1.
--   - `jordanWignerOdd`: PDF p.16: add the specified signed parity as the last odd-dimensional generator.
--   - `MatrixCAR`: PDF p.14: the finite tuple form of CAR, equivalent to its real-linear extension.
--   - `pairFirst`: PDF p.38: first index of pair j, converted from one-based source notation.
--   - `pairSecond`: PDF p.38: second index of pair j.
--   - `pairings`: PDF pp.38,46: pairings have ordered entries and ordered first elements.
--   - `carMoment`: PDF p.46: ordered field moments; the product acts on the ket from the right.
--   - `FermionicQuasiFree`: PDF p.46: fermionic Wick rule, with the normalized-state convention explicitly correcting the source's omission. Without normalization, zero would satisfy Wick.
--   - `carCovariance`: PDF p.46, (83): real covariance extracted from 1/i times the commutator moment.
--   - `decompositionPlus`: PDF p.61: the complex part of the closed real subspace.
--   - `decompositionMinus`: PDF p.61: the complex part of its real orthogonal complement.
--   - `decompositionOne`: PDF p.61: the two real orthogonal summands defining W_1.
--   - `decompositionZero`: PDF p.61: W_0 is the complement of W_+, W_-, and W_1. The printed final W_0 on the right is corrected to W_1, as forced by the subsequent decompositions. This source correction awaits independent moderation.
--   - `decompositionPieces`: PDF p.61: components in the displayed order W_+, W_0, W_1, W_-.
--   - `ComplexInvariant`: PDF p.61: a real subspace is also complex when stable under multiplication by i.
--   - `GeneralPositionIn`: PDF p.61: general position inside a specified complex ambient subspace; all complements are taken inside that ambient subspace.
--   - `MultiplicityHilbert`: PDF pp.12,17: a Hilbert space used as an existential multiplicity witness. The carrier is arbitrary and may be zero; this bundle contains no representation or theorem-specific equations.
--   - `scalarHilbertSpace`: Sanity: the scalar multiplicity space is a genuine bundled Hilbert space.
--   - `OperatorCAR`: PDF pp.14,17: bounded tuple CAR, with no finite-dimensionality restriction on H.
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, https://arxiv.org/abs/math-ph/0511030v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P41
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P03

/-!
Statements from Jan Derezinski, arXiv:math-ph/0511030v2.
Arbitrary complex Hilbert spaces, first-conjugate-linear inner products.
Compilation and independent moderation are pending the batch handoff.
-/

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P23

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.9, (9): unitary Weyl representation with the source's minus sign. -/
def IsCCR (omega : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (W : Y → H →L[ℂ] H) : Prop :=
  (∀ y, W y ∈ unitary (H →L[ℂ] H)) ∧
  ∀ y z, W y * W z = Complex.exp (-Complex.I * (omega y z : ℂ) / 2) • W (y + z)

/-- PDF pp.6,9: antisymmetry of the real bilinear form, without nondegeneracy. -/
def Antisymmetric (omega : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) : Prop :=
  ∀ y z, omega y z = -omega z y

/-- PDF p.6: nondegeneracy tests every vector in the first argument. -/
def FormNondegenerate (omega : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) : Prop :=
  ∀ z, (∀ y, omega y z = 0) → z = 0

/-- PDF p.10: strong continuity along every real one-parameter subgroup. -/
def WeylRegular (W : Y → H →L[ℂ] H) : Prop :=
  ∀ y v, Continuous (fun t : ℝ => W (t • y) v)

/-- PDF pp.10,15: no nontrivial closed complex invariant subspace. -/
def HilbertIrreducible (F : Y → H →L[ℂ] H) : Prop :=
  ∀ V : Submodule ℂ H, IsClosed (V : Set H) →
    (∀ y v, v ∈ V → F y v ∈ V) → V = ⊥ ∨ V = ⊤

/-- PDF p.10: density of the complex linear span of the Weyl orbit. -/
def Cyclic (W : Y → H →L[ℂ] H) (v : H) : Prop :=
  Dense (Submodule.span ℂ (Set.range (fun y => W y v)) : Set H)

/-- PDF p.38, (70): symmetric covariance and its Gaussian characteristic function.
The equation at zero forces normalization; no positivity assumption is added. -/
def GaussianCharacteristic (W : Y → H →L[ℂ] H) (v : H)
    (eta : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) : Prop :=
  (∀ y z, eta y z = eta z y) ∧
  ∀ y, inner ℂ v (W y v) = Complex.exp (-(eta y y : ℂ) / 4)

/-- PDF p.38: existence of a cyclic quasi-free vector. -/
def QuasiFreeCCR (W : Y → H →L[ℂ] H) : Prop :=
  ∃ v eta, Cyclic W v ∧ GaussianCharacteristic W v eta

/-- PDF p.10: unitary equivalence between possibly different representation spaces. -/
def EquivalentCCR {H2 : Type*} [NormedAddCommGroup H2] [InnerProductSpace ℂ H2]
    (W1 : Y → H →L[ℂ] H) (W2 : Y → H2 →L[ℂ] H2) : Prop :=
  ∃ U : H ≃ₗᵢ[ℂ] H2, ∀ y v, U (W1 y v) = W2 y (U v)

/-- PDF pp.13,17: equality modulo a scalar of absolute value one. -/
def SamePhase (U V : H →L[ℂ] H) : Prop :=
  ∃ c : ℂ, ‖c‖ = 1 ∧ V = c • U

/-- PDF pp.6,13: preservation of the specified real bilinear form. -/
def PreservesWeylForm (omega : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (r : Y → Y) : Prop :=
  ∀ y z, omega (r y) (r z) = omega y z

/-- PDF p.13, (23): U implements the specified transformation. -/
def ImplementsCCR (W : Y → H →L[ℂ] H) (r : Y → Y) (U : H →L[ℂ] H) : Prop :=
  ∀ y, U * W y * star U = W (r y)

/-- PDF pp.1,11, (16): one-degree canonical symplectic form. -/
def canonicalPlane : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v => u.1 * v.2 - v.1 * u.2
      map_add' := by intros; dsimp; ring
      map_smul' := by intros; dsimp; ring }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    change (u.1 + v.1) * w.2 - w.1 * (u.2 + v.2) =
      (u.1 * w.2 - w.1 * u.2) + (v.1 * w.2 - w.1 * v.2)
    ring
  map_smul' t u := by
    apply LinearMap.ext
    intro w
    change (t * u.1) * w.2 - w.1 * (t * u.2) =
      t * (u.1 * w.2 - w.1 * u.2)
    ring

/-- Sanity: the coordinate pair has symplectic pairing +1. -/
example : canonicalPlane (1, 0) (0, 1) = 1 := by norm_num [canonicalPlane]

/-- Sanity: zero form and identity unitaries satisfy the Weyl definition. -/
example : IsCCR (0 : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (fun _ => (1 : H →L[ℂ] H)) := by
  constructor
  · intro y; exact one_mem _
  · intro y z; simp

/-- Sanity: the identity belongs to its own scalar phase class. -/
example : SamePhase (1 : H →L[ℂ] H) 1 := by
  exact ⟨1, by simp, by simp⟩

section CAR

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- PDF p.14, (25)--(26): real linearity, self-adjointness, and factor-2 CAR.
Continuity of the label map is a consequence, not an input assumption. -/
def IsCAR (phi : E → H →L[ℂ] H) : Prop :=
  (∀ x y, phi (x + y) = phi x + phi y) ∧
  (∀ (t : ℝ) x, phi (t • x) = t • phi x) ∧
  (∀ x, star (phi x) = phi x) ∧
  ∀ x y, phi x * phi y + phi y * phi x = (2 * (inner ℝ x y : ℂ)) • (1 : H →L[ℂ] H)

/-- PDF p.15: equivalence intertwines all bounded CAR fields. -/
def EquivalentCAR {H2 : Type*} [NormedAddCommGroup H2] [InnerProductSpace ℂ H2]
    (phi1 : E → H →L[ℂ] H) (phi2 : E → H2 →L[ℂ] H2) : Prop :=
  ∃ U : H ≃ₗᵢ[ℂ] H2, ∀ y v, U (phi1 y v) = phi2 y (U v)

/-- PDF p.17, (32): implementation of an orthogonal transformation. -/
def ConjugatesCAR (phi : E → H →L[ℂ] H) (r : E → E) (U : H →L[ℂ] H) : Prop :=
  ∀ y, U * phi y * star U = phi (r y)

/-- Sanity: the scalar one-generator CAR has the source's factor 2. -/
example (x y : ℝ) :
    (x : ℂ) * (y : ℂ) + (y : ℂ) * (x : ℂ) = 2 * ((x * y : ℝ) : ℂ) := by
  push_cast
  ring

end CAR

section CompletedTensor

variable {H1 H2 : Type*}
variable [NormedAddCommGroup H1] [InnerProductSpace ℂ H1] [CompleteSpace H1]
variable [NormedAddCommGroup H2] [InnerProductSpace ℂ H2] [CompleteSpace H2]

/-- PDF p.7: bounded tensor action on the completed Hilbert tensor product.
The canonical completion embedding is uniformly inducing and has dense range,
so this extension uses its actual branch rather than the zero default. -/
def tensorOperator (A : H1 →L[ℂ] H1) (B : H2 →L[ℂ] H2) :
    UniformSpace.Completion (TensorProduct ℂ H1 H2) →L[ℂ]
      UniformSpace.Completion (TensorProduct ℂ H1 H2) :=
  ((UniformSpace.Completion.toComplL : TensorProduct ℂ H1 H2 →L[ℂ]
      UniformSpace.Completion (TensorProduct ℂ H1 H2)).comp (TensorProduct.mapL A B)).extend
    UniformSpace.Completion.toComplL

/-- Sanity: completed tensor action has the prescribed simple-tensor values. -/
example (A : H1 →L[ℂ] H1) (B : H2 →L[ℂ] H2) (x : H1) (y : H2) :
    tensorOperator A B ((TensorProduct.tmul ℂ x y : TensorProduct ℂ H1 H2) :
      UniformSpace.Completion (TensorProduct ℂ H1 H2)) =
    ((TensorProduct.tmul ℂ (A x) (B y) : TensorProduct ℂ H1 H2) :
      UniformSpace.Completion (TensorProduct ℂ H1 H2)) := by
  exact ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) _

/-- PDF p.10: direct-sum bilinear form. -/
def sumForm {Y1 Y2 : Type*} [AddCommGroup Y1] [Module ℝ Y1]
    [AddCommGroup Y2] [Module ℝ Y2]
    (a : Y1 →ₗ[ℝ] Y1 →ₗ[ℝ] ℝ) (b : Y2 →ₗ[ℝ] Y2 →ₗ[ℝ] ℝ) :
    (Y1 × Y2) →ₗ[ℝ] (Y1 × Y2) →ₗ[ℝ] ℝ where
  toFun u :=
    { toFun := fun v => a u.1 v.1 + b u.2 v.2
      map_add' := by intros; simp; abel
      map_smul' := by intros; simp; ring }
  map_add' u v := by
    apply LinearMap.ext
    intro w
    change a (u.1 + v.1) w.1 + b (u.2 + v.2) w.2 =
      (a u.1 w.1 + b u.2 w.2) + (a v.1 w.1 + b v.2 w.2)
    simp only [map_add, LinearMap.add_apply]
    ring
  map_smul' t u := by
    apply LinearMap.ext
    intro w
    change a (t • u.1) w.1 + b (t • u.2) w.2 =
      t * (a u.1 w.1 + b u.2 w.2)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring

/-- Sanity: the direct sum of zero forms has zero pairing. -/
example (u v : Y × Y) : sumForm (0 : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) 0 u v = 0 := by
  simp [sumForm]

end CompletedTensor

section Projections

open scoped ClosedSubmodule

end Projections

section FiniteCAR

/-- PDF p.16: sigma_1 entries in the ordered basis (false,true). -/
def spinX (s t : Bool) : ℂ := if s = t then 0 else 1

/-- PDF p.16: the accepted Pauli Y matrix reindexed by false=0, true=1.
Its upper-right entry is -i and lower-left entry is +i. -/
def pauliYEntry (s t : Bool) : ℂ :=
  QAlgorithms.Papers.Independent.Dependency50.P41.spinY
    (if s then 1 else 0) (if t then 1 else 0)

/-- PDF p.16: sigma_3 entries diag(1,-1). -/
def pauliZEntry (s t : Bool) : ℂ := if s = t then (if s then -1 else 1) else 0

/-- PDF p.16: ordered Jordan-Wigner generators on the n-fold qubit tensor basis. -/
def jordanWignerEven (n : ℕ) (k : Fin (2 * n)) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ := fun s t =>
  ∏ j : Fin n,
    if j.val < k.val / 2 then pauliZEntry (s j) (t j)
    else if j.val = k.val / 2 then
      if k.val % 2 = 0 then spinX (s j) (t j) else pauliYEntry (s j) (t j)
    else if s j = t j then 1 else 0

/-- PDF p.16: I_n is the product of sigma_3 in all n slots; I_0 is 1. -/
def jordanWignerParity (n : ℕ) : Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  fun s t => ∏ j : Fin n, pauliZEntry (s j) (t j)

/-- PDF p.16: add the specified signed parity as the last odd-dimensional generator. -/
def jordanWignerOdd (n : ℕ) (c : ℂ) (k : Fin (2 * n + 1)) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  if h : k.val < 2 * n then jordanWignerEven n ⟨k.val, h⟩ else c • jordanWignerParity n

/-- PDF p.14: the finite tuple form of CAR, equivalent to its real-linear extension. -/
def MatrixCAR {d : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (G : Fin d → Matrix B B ℂ) : Prop :=
  (∀ k, (G k).conjTranspose = G k) ∧
  ∀ k l, G k * G l + G l * G k = if k = l then (2 : ℂ) • (1 : Matrix B B ℂ) else 0

/-- Sanity: the sigma_2 upper-right sign is exactly the printed sign. -/
example : pauliYEntry false true = -Complex.I := rfl

/-- Sanity: the vacuum tensor power has I_0=1, including its unique matrix entry. -/
example (s t : Fin 0 → Bool) : jordanWignerParity 0 s t = 1 := by
  simp [jordanWignerParity]

end FiniteCAR

section FermionicCovariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- PDF p.38: first index of pair j, converted from one-based source notation. -/
def pairFirst {m : ℕ} (j : Fin m) : Fin (2 * m) := ⟨2 * j.val, by omega⟩

/-- PDF p.38: second index of pair j. -/
def pairSecond {m : ℕ} (j : Fin m) : Fin (2 * m) := ⟨2 * j.val + 1, by omega⟩

/-- PDF pp.38,46: pairings have ordered entries and ordered first elements. -/
def pairings (m : ℕ) : Finset (Equiv.Perm (Fin (2 * m))) := by
  classical
  exact Finset.univ.filter (fun s =>
    (∀ j : Fin m, s (pairFirst j) < s (pairSecond j)) ∧
      ∀ j k : Fin m, j < k → s (pairFirst j) < s (pairFirst k))

/-- PDF p.46: ordered field moments; the product acts on the ket from the right. -/
def carMoment (phi : E → H →L[ℂ] H) (v : H) {n : ℕ} (ys : Fin n → E) : ℂ :=
  inner ℂ v (((List.ofFn (fun j => phi (ys j))).prod) v)

/-- PDF p.46: fermionic Wick rule, with the normalized-state convention explicitly
correcting the source's omission. Without normalization, zero would satisfy Wick. -/
def FermionicQuasiFree (phi : E → H →L[ℂ] H) (v : H) : Prop :=
  ‖v‖ = 1 ∧
  (∀ m : ℕ, 0 < m → ∀ ys : Fin (2 * m - 1) → E, carMoment phi v ys = 0) ∧
  ∀ m : ℕ, 0 < m → ∀ ys : Fin (2 * m) → E,
    carMoment phi v ys = ∑ s ∈ pairings m,
      ((s.sign : ℤ) : ℂ) * ∏ j : Fin m,
        inner ℂ v ((phi (ys (s (pairFirst j))) * phi (ys (s (pairSecond j)))) v)

/-- PDF p.46, (83): real covariance extracted from 1/i times the commutator moment. -/
def carCovariance (phi : E → H →L[ℂ] H) (v : H) (x y : E) : ℝ :=
  (-Complex.I * inner ℂ v ((phi x * phi y - phi y * phi x) v)).re

/-- Sanity: the empty ordered product has moment equal to the squared norm. -/
example (phi : E → H →L[ℂ] H) (v : H) (ys : Fin 0 → E) :
    carMoment phi v ys = inner ℂ v v := by simp [carMoment]

/-- Sanity: the covariance at two identical labels vanishes. -/
example (phi : E → H →L[ℂ] H) (v : H) (x : E) : carCovariance phi v x x = 0 := by
  simp [carCovariance]

end FermionicCovariance

section FourPartDecomposition

open scoped ClosedSubmodule

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- PDF p.61: the complex part of the closed real subspace. -/
def decompositionPlus (V : ClosedSubmodule ℝ F) := V ⊓ V.mulI

/-- PDF p.61: the complex part of its real orthogonal complement. -/
def decompositionMinus (V : ClosedSubmodule ℝ F) := Vᗮ ⊓ V.mulIᗮ

/-- PDF p.61: the two real orthogonal summands defining W_1. -/
def decompositionOne (V : ClosedSubmodule ℝ F) :=
  (V ⊓ V.symplComp) ⊔ (V.mulI ⊓ Vᗮ)

/-- PDF p.61: W_0 is the complement of W_+, W_-, and W_1.
The printed final W_0 on the right is corrected to W_1, as forced by the
subsequent decompositions. This source correction awaits independent moderation. -/
def decompositionZero (V : ClosedSubmodule ℝ F) :=
  (decompositionPlus V ⊔ decompositionMinus V ⊔ decompositionOne V)ᗮ

/-- PDF p.61: components in the displayed order W_+, W_0, W_1, W_-. -/
def decompositionPieces (V : ClosedSubmodule ℝ F) : Fin 4 → ClosedSubmodule ℝ F :=
  ![decompositionPlus V, decompositionZero V, decompositionOne V, decompositionMinus V]

/-- PDF p.61: a real subspace is also complex when stable under multiplication by i. -/
def ComplexInvariant (V : ClosedSubmodule ℝ F) : Prop :=
  ∀ x : F, x ∈ V → Complex.I • x ∈ V

/-- PDF p.61: general position inside a specified complex ambient subspace;
all complements are taken inside that ambient subspace. -/
def GeneralPositionIn (A B : ClosedSubmodule ℝ F) : Prop :=
  A ≤ B ∧ A ⊓ A.mulI = ⊥ ∧
    (B ⊓ Aᗮ) ⊓ (B ⊓ A.mulIᗮ) = ⊥ ∧ (B ⊓ Aᗮ) ⊓ A.mulI = ⊥

/-- Sanity: the zero real subspace has no W_+ component. -/
example : decompositionPlus (⊥ : ClosedSubmodule ℝ F) = ⊥ := by
  simp [decompositionPlus]

end FourPartDecomposition

section FiniteMultiplicity

universe u

/-- PDF pp.12,17: a Hilbert space used as an existential multiplicity witness.
The carrier is arbitrary and may be zero; this bundle contains no representation
or theorem-specific equations. -/
structure MultiplicityHilbert where
  carrier : Type u
  [normed : NormedAddCommGroup carrier]
  [inner : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]

attribute [instance] MultiplicityHilbert.normed MultiplicityHilbert.inner MultiplicityHilbert.complete

/-- Sanity: the scalar multiplicity space is a genuine bundled Hilbert space. -/
def scalarHilbertSpace : MultiplicityHilbert where
  carrier := ℂ
  normed := inferInstance
  inner := inferInstance
  complete := inferInstance

example : scalarHilbertSpace.carrier = ℂ := rfl

/-- Sanity: a pure tensor with a zero factor is zero after completion. -/
example {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] (y : B) :
    tensorVector (0 : A) y = 0 := by simp [tensorVector]

/-- PDF pp.14,17: bounded tuple CAR, with no finite-dimensionality restriction on H. -/
def OperatorCAR {d : ℕ} (G : Fin d → H →L[ℂ] H) : Prop :=
  (∀ k, star (G k) = G k) ∧
  ∀ k l, G k * G l + G l * G k = if k = l then (2 : ℂ) • (1 : H →L[ℂ] H) else 0

end FiniteMultiplicity

end QAlgorithms.Papers.Independent.Intake100.P23


