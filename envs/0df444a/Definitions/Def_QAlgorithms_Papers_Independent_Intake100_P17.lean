-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P17
-- name    : QAlgorithms_Papers_Independent_Intake100_P17
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T16:23:42.316855+00:00
-- url     : https://prove2.me/theorems/6a39a4c2-b592-40dd-bb13-c30831d5ece2
-- title:
--   Definitions for Reflection Positivity and Conformal Symmetry
-- statement:
--   The objects the formalized statements of *Reflection Positivity and Conformal Symmetry* (arXiv:1206.2039) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ComplexNonneg`: Nonnegative complex numbers, with reality stated explicitly (Definition 1.5, p. 8).
--   - `ReflectionAction`: A unitary action of the symmetric group, written as a G-action and a compatible unitary involution. No continuity is imposed in §1.1 (p. 7).
--   - `ThetaPositive`: Theta-positivity is positivity on every vector, without normalization (Definition 1.2, p. 7). The source's first-linear inner product is translated by swapping arguments.
--   - `orbitSpan`: The closed linear span of the S-orbit of a subspace (Definition 1.9, p. 10).
--   - `OSCompletion`: A realization of the completed semidefinite quotient of P (Definition 1.2, p. 7). The dense linear map and its prescribed inner products characterize exactly the quotient by the nullspace and its Hilbert completion, up to a unique unitary fixing the image. This is output data in Lemma 1.4, never an assumed induced representation.
--   - `compressionSet`: The compression set is computed from the given action and domain (Example 1.7(b), p. 9).
--   - `ReflectionPositiveReal`: Reflection positivity for (R, -id, (0,infinity)) in the scalar case (Definition 1.8, pp. 9, 17). No normalization at zero is imposed.
--   - `RealVector`: Euclidean vector group with the source's n coordinates (Notation, pp. 5-6).
--   - `spatialReflection`: The sharp involution keeps time and negates spatial coordinates (p. 36).
--   - `HalfSpace`: The open half-space excludes the origin and requires a positive dimension (p. 36).
--   - `halfSpaceKernel`: The semigroup covariance k(x+y-sharp), with no inversion at a singular point (p. 36).
--   - `OpenBall`: The open ball, including its center (Proposition 6.2, p. 36).
--   - `ballKernel`: The ball kernel is defined directly at zero; real powers use a positive base (p. 36).
-- source:
--   Reflection Positivity and Conformal Symmetry, arXiv:1206.2039v2, https://arxiv.org/abs/1206.2039v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32

noncomputable section

open scoped BigOperators Topology
open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intake100.P17

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

/-- Nonnegative complex numbers, with reality stated explicitly (Definition 1.5, p. 8). -/
def ComplexNonneg (z : ℂ) : Prop := z.im = 0 ∧ 0 ≤ z.re

-- Reuse the pinned finite-support Gram-form predicate; no local copy is declared.
example {X : Type} : PositiveKernel (fun (_ _ : X) => (0 : ℂ)) := by
  intro s z
  simp

/-- A unitary action of the symmetric group, written as a G-action and a compatible
unitary involution. No continuity is imposed in §1.1 (p. 7). -/
structure ReflectionAction (G : Type*) [Group G] (tau : G ≃* G)
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  pi : G → E ≃ₗᵢ[ℂ] E
  one_apply : ∀ v, pi 1 v = v
  mul_apply : ∀ g h v, pi (g * h) v = pi g (pi h v)
  theta : E ≃ₗᵢ[ℂ] E
  theta_involutive : Function.Involutive theta
  covariance : ∀ g v, theta (pi g (theta v)) = pi (tau g) v

/-- Theta-positivity is positivity on every vector, without normalization (Definition 1.2, p. 7).
The source's first-linear inner product is translated by swapping arguments. -/
def ThetaPositive {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (theta : E ≃ₗᵢ[ℂ] E) (P : Submodule ℂ E) : Prop :=
  ∀ v ∈ P, ComplexNonneg (inner ℂ v (theta v))

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (theta : E ≃ₗᵢ[ℂ] E) : ThetaPositive theta ⊥ := by
  intro v hv
  have hv0 : v = 0 := by simpa using hv
  subst v
  simp [ComplexNonneg]

/-- The closed linear span of the S-orbit of a subspace (Definition 1.9, p. 10). -/
def orbitSpan {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {tau : G ≃* G} (R : ReflectionAction G tau E) (S : Set G)
    (F : Submodule ℂ E) : Submodule ℂ E :=
  (Submodule.span ℂ {v | ∃ s ∈ S, ∃ w ∈ F, v = R.pi s w}).topologicalClosure

example {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {tau : G ≃* G} (R : ReflectionAction G tau E) (F : Submodule ℂ E) :
    orbitSpan R ∅ F = ⊥ := by
  simp [orbitSpan]

/-- A realization of the completed semidefinite quotient of P (Definition 1.2, p. 7).
The dense linear map and its prescribed inner products characterize exactly the quotient
by the nullspace and its Hilbert completion, up to a unique unitary fixing the image.
This is output data in Lemma 1.4, never an assumed induced representation. -/
structure OSCompletion {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : Submodule ℂ E) (theta : E ≃ₗᵢ[ℂ] E) where
  Carrier : Type
  [normed : NormedAddCommGroup Carrier]
  [innerSpace : InnerProductSpace ℂ Carrier]
  [complete : CompleteSpace Carrier]
  quotientMap : P →ₗ[ℂ] Carrier
  dense : DenseRange quotientMap
  inner_quotient : ∀ v w, inner ℂ (quotientMap v) (quotientMap w) =
    inner ℂ (v : E) (theta (w : E))

attribute [instance] OSCompletion.normed OSCompletion.innerSpace OSCompletion.complete

example {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : Submodule ℂ E) [CompleteSpace P] :
    Nonempty (OSCompletion P (LinearIsometryEquiv.refl ℂ E)) := by
  exact ⟨{
    Carrier := P
    quotientMap := LinearMap.id
    dense := fun x => subset_closure ⟨x, rfl⟩
    inner_quotient := fun _ _ => rfl
  }⟩

/-- The compression set is computed from the given action and domain (Example 1.7(b), p. 9). -/
def compressionSet {G X : Type*} [Group G] [MulAction G X] (D : Set X) : Set G :=
  {g | ∀ x ∈ D, g • x ∈ D}

example {G X : Type*} [Group G] [MulAction G X] :
    compressionSet (G := G) (∅ : Set X) = Set.univ := by
  ext g
  simp [compressionSet]

example {G E : Type*} [Group G] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (tau : G ≃* G) : Nonempty (ReflectionAction G tau E) := by
  exact ⟨{
    pi := fun _ => LinearIsometryEquiv.refl ℂ E
    one_apply := fun _ => rfl
    mul_apply := fun _ _ _ => rfl
    theta := LinearIsometryEquiv.refl ℂ E
    theta_involutive := fun _ => rfl
    covariance := fun _ _ => rfl
  }⟩

/-- Reflection positivity for (R, -id, (0,infinity)) in the scalar case (Definition 1.8,
pp. 9, 17). No normalization at zero is imposed. -/
def ReflectionPositiveReal (phi : ℝ → ℂ) : Prop :=
  PositiveKernel (fun (x y : ℝ) => phi (x - y)) ∧
  (∀ x, phi (-x) = phi x) ∧
  PositiveKernel (fun (x y : {t : ℝ // 0 < t}) => phi (x.val + y.val))

example : ReflectionPositiveReal (fun _ => (0 : ℂ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s z; simp
  · intro x; rfl
  · intro s z; simp

/-- Euclidean vector group with the source's n coordinates (Notation, pp. 5-6). -/
abbrev RealVector (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The sharp involution keeps time and negates spatial coordinates (p. 36). -/
def spatialReflection {n : ℕ} (x : RealVector n) : RealVector n :=
  WithLp.toLp 2 (fun i => if i.val = 0 then x i else -x i)

example {n : ℕ} (x : RealVector n) : spatialReflection (spatialReflection x) = x := by
  ext i
  by_cases h : i.val = 0 <;> simp [spatialReflection, h]

/-- The open half-space excludes the origin and requires a positive dimension (p. 36). -/
def HalfSpace (n : ℕ) (hn : 0 < n) := {x : RealVector n // 0 < x ⟨0, hn⟩}

/-- The semigroup covariance k(x+y-sharp), with no inversion at a singular point (p. 36). -/
def halfSpaceKernel (n : ℕ) (hn : 0 < n) (s : ℝ) (x y : HalfSpace n hn) : ℂ :=
  ((‖x.val + spatialReflection y.val‖ ^ (-s) : ℝ) : ℂ)

example (n : ℕ) (hn : 0 < n) (x y : HalfSpace n hn) :
    halfSpaceKernel n hn 0 x y = 1 := by
  simp [halfSpaceKernel]

example : Nonempty (HalfSpace 1 (by decide)) := by
  exact ⟨⟨WithLp.toLp 2 (fun _ => 1), by norm_num⟩⟩

/-- The open ball, including its center (Proposition 6.2, p. 36). -/
def OpenBall (n : ℕ) := {x : RealVector n // ‖x‖ < 1}

/-- The ball kernel is defined directly at zero; real powers use a positive base (p. 36). -/
def ballKernel (n : ℕ) (s : ℝ) (x y : OpenBall n) : ℂ :=
  (((1 - 2 * inner ℝ x.val y.val + ‖x.val‖ ^ 2 * ‖y.val‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)

example (n : ℕ) (s : ℝ) :
    ballKernel n s ⟨0, by simp⟩ ⟨0, by simp⟩ = 1 := by
  simp [ballKernel]

end QAlgorithms.Papers.Independent.Intake100.P17


