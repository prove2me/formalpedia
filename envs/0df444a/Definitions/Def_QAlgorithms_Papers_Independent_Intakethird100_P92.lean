-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P92
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P92
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T06:23:27.872605+00:00
-- url     : https://prove2.me/theorems/8e89c083-9847-4865-bb38-806cdf2143b6
-- title:
--   Definitions for Reflection positive one-parameter groups and dilations
-- statement:
--   The objects the formalized statements of *Reflection positive one-parameter groups and dilations* (arXiv:1312.6161) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ReflectionData`: Reflection-positive data, Definition 1.1, PDF p. 5. No quotient identities or operator norm bounds are fields of this structure.
--   - `OSPreSpace`: A distinct algebraic copy of Eplus with no inherited ambient norm. It carries the reflected seminorm of Definition 1.1, PDF p. 5.
--   - `osPreEquiv`: Forget the wrapper before transporting only the algebraic structures (p. 5).
--   - `osCore`: The reflected semidefinite inner product in Mathlib convention, PDF p. 5.
--   - `OS`: The separated Hilbert completion of the reflected seminormed space. Uniform completion identifies points at distance zero, giving the quotient by the theta-form radical followed by completion (Definition 1.1, PDF p. 5).
--   - `toOSPre`: The identity between algebraic copies, with no ambient norm transport (p. 5).
--   - `osQ`: The canonical OS quotient map of Definition 1.1, PDF p. 5.
--   - `osNull`: The computed null subspace in the ambient Hilbert space, PDF p. 5.
--   - `timeZero`: The computed time-zero subspace E0, PDF p. 5.
--   - `osExtension`: The unique continuous quotient extension when it exists, and zero otherwise. The defining property specifies its value on the dense canonical quotient image; it asserts no existence, norm estimate, symmetry, or descent theorem. See Definition 2.1 and Lemma 2.2, PDF pp. 8--9.
--   - `RealUnitaryAction`: An algebraic unitary one-parameter group. Strong continuity is deliberately separate, since Lemma 3.5 (PDF p. 11) does not assume it.
--   - `RealUnitaryAction.StronglyContinuous`: Strong continuity of a unitary group.
--   - `orbitSpan`: The orbit span defining linear cyclicity, PDF p. 11.
--   - `IsCyclic`: A subspace is cyclic if its full real-time orbit has dense linear span.
--   - `unitaryFixedSubspace`: The fixed subspace is computed from all times, PDF p. 11.
--   - `ReflectionGroup`: Definition 3.1, PDF p. 10. Cyclicity is not part of the definition.
--   - `positiveRestriction`: Restrict a positive-time operator to Eplus, with its actual inherited action.
--   - `quantized`: The quotient extension of the actual positive-time action, not an independent operator parameter. Its descent and semigroup properties are Proposition 3.2.
--   - `quantizedFixed`: Fixed vectors of the computed quantized semigroup, all positive times (p. 11).
--   - `quotientImage`: The image q(D), expressed without choosing representatives of D (p. 11).
--   - `domainQ`: Canonical quotient of a vector in an explicitly stated operator domain.
--   - `projectionTo`: Orthogonal projection onto a closed subspace; the zero fallback is unused for the closed spaces in Proposition 3.17. This uses Mathlib's actual projection, not a free map satisfying assumed projection identities.
--   - `projectionOn`: The ambient endomorphism corresponding to the actual orthogonal projection.
--   - `timeZeroQuotient`: Gamma is exactly q restricted to the computed time-zero space, PDF p. 16.
--   - `timeZeroCompression`: The computed compression phi(t)=P U(t) P*, PDF pp. 15--16.
--   - `CompressionMultiplicative`: The multiplicativity condition in Proposition 3.17 concerns positive times.
--   - `MarkovCondition`: The Markov identity uses the three actual orthogonal projections, PDF p. 16.
--   - `IsHermitianForm`: First-linear hermitian forms, for either real or complex scalars, PDF p. 52. No topology, nondegeneracy, or positivity is required on the vector space.
--   - `IsPositiveKernel`: Scalar positive-definite kernels mean nonnegative finite Gram sums, with nonnegative including zero, Definition C.1, PDF p. 51.
--   - `IsTame`: A tame Borel measure on the closed half-line, Definition A.2, PDF p. 43. All kernels are integrated nonnegatively with values in ENNReal.
--   - `IsTemperedMeasure`: Tempered positive measures on Euclidean space mean a finite polynomially weighted nonnegative integral, Appendix A, PDF pp. 42--44.
--   - `stieltjesDensity`: The Stieltjes density, including the extended reciprocal at the origin.
--   - `stieltjesMeasure`: The measure is computed from rho, not independently supplied.
--   - `logReciprocal`: Extended logarithmic singularity at zero; only its [0,1] restriction is used.
--   - `polynomialValue`: Evaluation of a complex polynomial at real Euclidean coordinates.
-- source:
--   Reflection positive one-parameter groups and dilations, arXiv:1312.6161v2, https://arxiv.org/abs/1312.6161v2

import Mathlib

/-! Statements from Neeb--Olafsson, arXiv:1312.6161v2.
The paper uses first-linear inner products; every displayed pairing here uses
Mathlib's conjugate-linear-first convention. No separability or finite dimension
is imposed. All new objects in this file belong only to this paper.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P92

open scoped ComplexConjugate BigOperators NNReal ENNReal
open MeasureTheory

attribute [local instance] Classical.propDecidable

universe u v

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Reflection-positive data, Definition 1.1, PDF p. 5. No quotient identities
or operator norm bounds are fields of this structure. -/
structure ReflectionData where
  plus : Submodule ℂ E
  plus_closed : IsClosed (plus : Set E)
  theta : E ≃ₗᵢ[ℂ] E
  theta_square : ∀ x, theta (theta x) = x
  positive : ∀ x : plus, 0 ≤ (inner ℂ (theta x) (x : E)).re

variable {E}

/-- A distinct algebraic copy of Eplus with no inherited ambient norm.
It carries the reflected seminorm of Definition 1.1, PDF p. 5. -/
structure OSPreSpace (r : ReflectionData E) where
  value : r.plus

/-- Forget the wrapper before transporting only the algebraic structures (p. 5). -/
def osPreEquiv (r : ReflectionData E) : OSPreSpace r ≃ r.plus where
  toFun x := x.value
  invFun x := ⟨x⟩
  left_inv x := by cases x; rfl
  right_inv x := rfl

/-- Algebraic addition transported to the reflected copy, PDF p. 5. -/
instance osPreAddCommGroup (r : ReflectionData E) : AddCommGroup (OSPreSpace r) :=
  (osPreEquiv r).addCommGroup

/-- Scalar multiplication transported without any topology, PDF p. 5. -/
instance osPreModule (r : ReflectionData E) : Module ℂ (OSPreSpace r) :=
  (osPreEquiv r).module ℂ

/-- The reflected semidefinite inner product in Mathlib convention, PDF p. 5. -/
def osCore (r : ReflectionData E) : PreInnerProductSpace.Core ℂ (OSPreSpace r) where
  inner x y := inner ℂ (r.theta (x.value : E)) (y.value : E)
  conj_inner_symm x y := by
    change conj (inner ℂ (r.theta (y.value : E)) (x.value : E)) =
      inner ℂ (r.theta (x.value : E)) (y.value : E)
    rw [inner_conj_symm]
    calc
      inner ℂ (x.value : E) (r.theta (y.value : E)) =
          inner ℂ (r.theta (r.theta (x.value : E))) (r.theta (y.value : E)) := by
            rw [r.theta_square]
      _ = inner ℂ (r.theta (x.value : E)) (y.value : E) := r.theta.inner_map_map _ _
  re_inner_nonneg x := r.positive x.value
  add_left x y z := by
    change inner ℂ (r.theta ((x.value : E) + (y.value : E))) (z.value : E) = _
    rw [map_add, inner_add_left]
  smul_left x y c := by
    change inner ℂ (r.theta (c • (x.value : E))) (y.value : E) = _
    rw [map_smul, inner_smul_left]

/-- The seminorm is built solely from the reflected core, PDF p. 5. -/
instance osPreSeminormedAddCommGroup (r : ReflectionData E) :
    SeminormedAddCommGroup (OSPreSpace r) :=
  letI : PreInnerProductSpace.Core ℂ (OSPreSpace r) := osCore r
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ) (F := OSPreSpace r)

/-- Compatibility of scalar multiplication with the reflected seminorm (p. 5). -/
instance osPreNormedSpace (r : ReflectionData E) : NormedSpace ℂ (OSPreSpace r) :=
  letI : PreInnerProductSpace.Core ℂ (OSPreSpace r) := osCore r
  InnerProductSpace.Core.toNormedSpace (𝕜 := ℂ) (F := OSPreSpace r)

/-- The pre-inner product uses the very same seminorm instance, PDF p. 5. -/
instance osPreInnerProductSpace (r : ReflectionData E) :
    InnerProductSpace ℂ (OSPreSpace r) :=
  InnerProductSpace.ofCore (osCore r)

/-- The separated Hilbert completion of the reflected seminormed space.
Uniform completion identifies points at distance zero, giving the quotient by
the theta-form radical followed by completion (Definition 1.1, PDF p. 5). -/
def OS (r : ReflectionData E) := UniformSpace.Completion (OSPreSpace r)

/-- The completed reflected norm, PDF p. 5. -/
instance osNormedAddCommGroup (r : ReflectionData E) : NormedAddCommGroup (OS r) :=
  inferInstanceAs (NormedAddCommGroup (UniformSpace.Completion (OSPreSpace r)))

/-- The scalar structure on the completed reflected space, PDF p. 5. -/
instance osNormedSpace (r : ReflectionData E) : NormedSpace ℂ (OS r) :=
  inferInstanceAs (NormedSpace ℂ (UniformSpace.Completion (OSPreSpace r)))

/-- The completed reflected inner product, PDF p. 5. -/
instance osInnerProductSpace (r : ReflectionData E) : InnerProductSpace ℂ (OS r) :=
  inferInstanceAs (InnerProductSpace ℂ (UniformSpace.Completion (OSPreSpace r)))

/-- Completeness of the canonical completion, PDF p. 5. -/
instance osCompleteSpace (r : ReflectionData E) : CompleteSpace (OS r) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (OSPreSpace r)))

/-- The identity between algebraic copies, with no ambient norm transport (p. 5). -/
def toOSPre (r : ReflectionData E) : r.plus →ₗ[ℂ] OSPreSpace r :=
  ((osPreEquiv r).linearEquiv ℂ).symm.toLinearMap

/-- Sanity check: the reflected seminorm is used even when it is degenerate. -/
example (r : ReflectionData E) (v : r.plus) :
    ‖toOSPre r v‖ = Real.sqrt (inner ℂ (r.theta (v : E)) (v : E)).re := rfl

/-- The canonical OS quotient map of Definition 1.1, PDF p. 5. -/
def osQ (r : ReflectionData E) : r.plus →ₗ[ℂ] OS r :=
  (UniformSpace.Completion.toComplₗᵢ : OSPreSpace r →ₗᵢ[ℂ] OS r).toLinearMap.comp
    (toOSPre r)

/-- The computed null subspace in the ambient Hilbert space, PDF p. 5. -/
def osNull (r : ReflectionData E) : Submodule ℂ E :=
  (osQ r).ker.map r.plus.subtype

/-- The computed time-zero subspace E0, PDF p. 5. -/
def timeZero (r : ReflectionData E) : Submodule ℂ E :=
  r.plus ⊓ LinearMap.ker (r.theta.toLinearMap - LinearMap.id)

/-- A sanity check: the canonical quotient takes zero to zero. -/
example (r : ReflectionData E) : osQ r 0 = 0 := map_zero _

/-- A sanity check: time zero always contains the zero vector. -/
example (r : ReflectionData E) : (0 : E) ∈ timeZero r := Submodule.zero_mem _

/-- The unique continuous quotient extension when it exists, and zero otherwise.
The defining property specifies its value on the dense canonical quotient image;
it asserts no existence, norm estimate, symmetry, or descent theorem. See
Definition 2.1 and Lemma 2.2, PDF pp. 8--9. -/
def osExtension (r : ReflectionData E) (T : r.plus →ₗ[ℂ] r.plus) : OS r →L[ℂ] OS r :=
  if h : ∃ A : OS r →L[ℂ] OS r, ∀ x, A (osQ r x) = osQ r (T x) then
    Classical.choose h
  else 0

/-- An algebraic unitary one-parameter group. Strong continuity is deliberately
separate, since Lemma 3.5 (PDF p. 11) does not assume it. -/
structure RealUnitaryAction where
  op : ℝ → E ≃ₗᵢ[ℂ] E
  zero : ∀ x, op 0 x = x
  add : ∀ s t x, op (s + t) x = op s (op t x)

/-- Strong continuity of a unitary group. -/
def RealUnitaryAction.StronglyContinuous (U : RealUnitaryAction (E := E)) : Prop :=
  ∀ x, Continuous (fun t => U.op t x)

/-- The orbit span defining linear cyclicity, PDF p. 11. -/
def orbitSpan (U : RealUnitaryAction (E := E)) (F : Submodule ℂ E)
    (times : Set ℝ) : Submodule ℂ E :=
  Submodule.span ℂ {x | ∃ t ∈ times, ∃ v ∈ F, U.op t v = x}

/-- A subspace is cyclic if its full real-time orbit has dense linear span. -/
def IsCyclic (U : RealUnitaryAction (E := E)) (F : Submodule ℂ E) : Prop :=
  (orbitSpan U F Set.univ).topologicalClosure = ⊤

/-- The fixed subspace is computed from all times, PDF p. 11. -/
def unitaryFixedSubspace (U : RealUnitaryAction (E := E)) : Submodule ℂ E :=
  ⨅ t : ℝ, LinearMap.ker ((U.op t).toLinearMap - LinearMap.id)

/-- A sanity check for the time-zero law of a unitary group. -/
example (U : RealUnitaryAction (E := E)) (x : E) : U.op 0 x = x := U.zero x

/-- Definition 3.1, PDF p. 10. Cyclicity is not part of the definition. -/
structure ReflectionGroup (r : ReflectionData E) where
  group : RealUnitaryAction (E := E)
  continuous : group.StronglyContinuous
  positive_invariant : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ r.plus, group.op t x ∈ r.plus
  reflected : ∀ t x, r.theta (group.op t (r.theta x)) = group.op (-t) x

/-- Restrict a positive-time operator to Eplus, with its actual inherited action. -/
def positiveRestriction (r : ReflectionData E) (U : ReflectionGroup r)
    (t : ℝ≥0) : r.plus →ₗ[ℂ] r.plus where
  toFun x := ⟨U.group.op t x, U.positive_invariant t t.property x x.property⟩
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c x := by apply Subtype.ext; exact map_smul _ _ _

/-- The quotient extension of the actual positive-time action, not an independent
operator parameter. Its descent and semigroup properties are Proposition 3.2. -/
def quantized (r : ReflectionData E) (U : ReflectionGroup r) (t : ℝ≥0) :
    OS r →L[ℂ] OS r := osExtension r (positiveRestriction r U t)

/-- Fixed vectors of the computed quantized semigroup, all positive times (p. 11). -/
def quantizedFixed (r : ReflectionData E) (U : ReflectionGroup r) : Submodule ℂ (OS r) :=
  ⨅ t : {t : ℝ≥0 // 0 < t},
    LinearMap.ker ((quantized r U t.val).toLinearMap - LinearMap.id)

/-- The image q(D), expressed without choosing representatives of D (p. 11). -/
def quotientImage (r : ReflectionData E) (D : Submodule ℂ E) : Set (OS r) :=
  osQ r '' {v : r.plus | (v : E) ∈ D}

/-- Canonical quotient of a vector in an explicitly stated operator domain. -/
def domainQ (r : ReflectionData E) (D : Submodule ℂ r.plus) (v : D) :
    D.map (osQ r) :=
  ⟨osQ r v, Submodule.mem_map.mpr ⟨v, v.property, rfl⟩⟩

/-- Orthogonal projection onto a closed subspace; the zero fallback is unused
for the closed spaces in Proposition 3.17. This uses Mathlib's actual projection,
not a free map satisfying assumed projection identities. -/
def projectionTo (F : Submodule ℂ E) : E →L[ℂ] F :=
  if h : IsClosed (F : Set E) then
    letI : CompleteSpace F := h.completeSpace_coe
    F.orthogonalProjectionOnto
  else 0

/-- The ambient endomorphism corresponding to the actual orthogonal projection. -/
def projectionOn (F : Submodule ℂ E) : E →L[ℂ] E :=
  F.subtypeL.comp (projectionTo F)

/-- Gamma is exactly q restricted to the computed time-zero space, PDF p. 16. -/
def timeZeroQuotient (r : ReflectionData E) : timeZero r →ₗ[ℂ] OS r :=
  (osQ r).comp (Submodule.inclusion (show timeZero r ≤ r.plus from inf_le_left))

/-- The computed compression phi(t)=P U(t) P*, PDF pp. 15--16. -/
def timeZeroCompression (r : ReflectionData E) (U : ReflectionGroup r) (t : ℝ) :
    timeZero r →ₗ[ℂ] timeZero r :=
  (projectionTo (timeZero r)).toLinearMap.comp
    ((U.group.op t).toLinearMap.comp (timeZero r).subtype)

/-- The multiplicativity condition in Proposition 3.17 concerns positive times. -/
def CompressionMultiplicative (r : ReflectionData E) (U : ReflectionGroup r) : Prop :=
  ∀ s t : ℝ, 0 < s → 0 < t →
    timeZeroCompression r U (s + t) = (timeZeroCompression r U s).comp (timeZeroCompression r U t)

/-- The Markov identity uses the three actual orthogonal projections, PDF p. 16. -/
def MarkovCondition (r : ReflectionData E) : Prop :=
  (projectionOn r.plus).comp
      ((projectionOn (timeZero r)).comp
        (projectionOn (r.plus.map r.theta.toLinearMap))) =
    (projectionOn r.plus).comp (projectionOn (r.plus.map r.theta.toLinearMap))

/-- A sanity check: Gamma takes zero to zero. -/
example (r : ReflectionData E) : timeZeroQuotient r 0 = 0 := map_zero _

/-- First-linear hermitian forms, for either real or complex scalars, PDF p. 52.
No topology, nondegeneracy, or positivity is required on the vector space. -/
def IsHermitianForm (K : Type*) [RCLike K] {V : Type v} [AddCommGroup V] [Module K V]
    (beta : V → V → K) : Prop :=
  (∀ x y z, beta (x + y) z = beta x z + beta y z) ∧
  (∀ a x y, beta (a • x) y = a * beta x y) ∧
  (∀ x y z, beta x (y + z) = beta x y + beta x z) ∧
  (∀ a x y, beta x (a • y) = star a * beta x y) ∧
  (∀ x y, star (beta x y) = beta y x)

/-- Scalar positive-definite kernels mean nonnegative finite Gram sums, with
nonnegative including zero, Definition C.1, PDF p. 51. -/
def IsPositiveKernel (K : Type*) [RCLike K] {X : Type v} (k : X → X → K) : Prop :=
  ∀ n : ℕ, ∀ x : Fin n → X, ∀ c : Fin n → K,
    ∃ a : ℝ, 0 ≤ a ∧ (∑ i, ∑ j, star (c i) * k (x i) (x j) * c j) = (a : K)

/-- A sanity check: the zero form satisfies the full hermitian-form predicate. -/
example (K : Type*) [RCLike K] (V : Type v) [AddCommGroup V] [Module K V] :
    IsHermitianForm K (fun _ _ : V => (0 : K)) := by
  simp [IsHermitianForm]

/-- A tame Borel measure on the closed half-line, Definition A.2, PDF p. 43.
All kernels are integrated nonnegatively with values in ENNReal. -/
def IsTame (rho : Measure ℝ≥0) : Prop :=
  (∫⁻ y, (1 + (y : ℝ≥0∞) ^ 2)⁻¹ ∂rho) < ⊤

/-- Tempered positive measures on Euclidean space mean a finite polynomially
weighted nonnegative integral, Appendix A, PDF pp. 42--44. -/
def IsTemperedMeasure {X : Type*} [MeasurableSpace X] [Norm X]
    (mu : Measure X) : Prop :=
  ∃ N : ℕ, (∫⁻ x, (1 + ENNReal.ofReal (‖x‖ ^ 2))⁻¹ ^ N ∂mu) < ⊤

/-- The Stieltjes density, including the extended reciprocal at the origin. -/
def stieltjesDensity (d : ℕ) (rho : Measure ℝ≥0) (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ∫⁻ y, ((y : ℝ≥0∞) ^ 2 + ENNReal.ofReal (‖x‖ ^ 2))⁻¹ ∂rho

/-- The measure is computed from rho, not independently supplied. -/
def stieltjesMeasure (d : ℕ) (rho : Measure ℝ≥0) :
    Measure (EuclideanSpace ℝ (Fin d)) := volume.withDensity (stieltjesDensity d rho)

/-- Extended logarithmic singularity at zero; only its [0,1] restriction is used. -/
def logReciprocal (y : ℝ≥0) : ℝ≥0∞ :=
  if y = 0 then ⊤ else ENNReal.ofReal (Real.log ((y : ℝ)⁻¹))

/-- A sanity check: zero is an infinite logarithmic singularity, not log(0)=0. -/
example : logReciprocal 0 = ⊤ := by simp [logReciprocal]

/-- A sanity check: the zero spectral measure is tame. -/
example : IsTame (0 : Measure ℝ≥0) := by simp [IsTame]

/-- Evaluation of a complex polynomial at real Euclidean coordinates. -/
def polynomialValue {d : ℕ} (p : MvPolynomial (Fin d) ℂ)
    (x : EuclideanSpace ℝ (Fin d)) : ℂ :=
  MvPolynomial.eval (fun i => (x i : ℂ)) p

/-- A sanity check: evaluation preserves the zero polynomial. -/
example {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    polynomialValue (0 : MvPolynomial (Fin d) ℂ) x = 0 := by
  simp [polynomialValue]

end QAlgorithms.Papers.Independent.Intakethird100.P92


