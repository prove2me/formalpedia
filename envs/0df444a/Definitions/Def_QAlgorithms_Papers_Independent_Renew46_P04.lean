-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P04
-- name    : QAlgorithms_Papers_Independent_Renew46_P04
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T03:45:22.974988+00:00
-- url     : https://prove2.me/theorems/f7984b15-d835-4484-bc3f-1d1f6d2d35e1
-- title:
--   Definitions for Norm-attaining tensors and nuclear operators
-- statement:
--   The objects the formalized statements of *Norm-attaining tensors and nuclear operators* (arXiv:2006.09871) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Factors`: PDF p.3: the two Banach factors, indexed by false and true. ULift places different carrier universes in one family without changing any norm.
--   - `Algebraic`: PDF p.3: algebraic tensor product with the finite-decomposition projective seminorm.
--   - `NormedAlgebraic`: PDF p.3: the actual normed algebraic space, obtained by Hausdorff separation of the finite-decomposition seminorm. The separation conclusion in projective_series identifies it faithfully with the raw algebraic tensor product.
--   - `Projective`: PDF p.3: Hausdorff completion in the projective seminorm.
--   - `pair`: PDF p.3: an ordered pair of vectors in the dependent two-factor family.
--   - `algebraicInclusion`: PDF p.3: the canonical algebraic inclusion.
--   - `pure`: PDF p.3: the canonical pure tensor.
--   - `Bilinear`: PDF p.3: bounded bilinear maps, using exactly two multilinear coordinates.
--   - `extendBilinear`: PDF pp.3–4: canonical extension through the dense algebraic inclusion.
--   - `restrictBilinear`: PDF p.3: canonical restriction to pure tensors, retaining the two coordinates.
--   - `TensorRep`: PDF p.5, Definition 2.1: bounded sequences and actual absolutely convergent representation.
--   - `finiteCosts`: PDF p.3: finite-decomposition costs on the algebraic tensor product, including an empty decomposition for zero. The scalar coefficients in Mathlib's lift norm are absorbed in the first factor.
--   - `tensorCosts`: PDF p.3: all countable representation costs, without attainment imposed.
--   - `normalizedCosts`: PDF p.3: normalized cost formula, used only when both factors are nonzero.
--   - `TensorAttains`: PDF p.5: attainment of the projective norm by some admissible representation.
--   - `rankOneBilinear`: PDF p.4: the rank-one bilinear map, before completion.
--   - `projectiveRealization`: PDF p.4: the actual canonical map J, constructed by continuous extension.
--   - `NuclearRep`: PDF p.4: full series representation, with separate boundedness and norm-product summability.
--   - `NuclearRange`: PDF p.4: nuclear operators, as the actual range of J.
--   - `Nuclear`: PDF p.4: the nuclear space with its computed quotient norm.
--   - `nuclearOperator`: PDF p.4: quotient-descended canonical realization; no optimal lift is selected.
--   - `nuclearQuotient`: PDF p.4: quotient map from the completed projective product.
--   - `nuclearCosts`: PDF p.4: series costs for an operator; used only on the nuclear range.
--   - `NuclearAttains`: PDF p.5, Definition 2.1: nuclear attainment uses the quotient nuclear norm.
--   - `Annihilator`: PDF p.4: annihilator of the actual kernel inside the continuous tensor dual.
--   - `pullNuclearDual`: PDF p.4: pullback of a nuclear dual functional along the actual quotient map.
--   - `ApproximationProperty`: PDF p.4: approximation property in the source's compact-set formulation.
--   - `OperatorAttains`: PDF p.5: classical operator-norm attainment on the unit sphere.
--   - `BilinearAttains`: PDF p.5: classical bilinear attainment requires both unit vectors.
--   - `TensorDense`: PDF p.6: projective-norm density.
--   - `NuclearDense`: PDF p.6: density in the nuclear quotient norm.
--   - `LocalBilinear`: PDF p.12, Definition 4.1(b): the radius depends on epsilon and the fixed form.
--   - `MetricPi`: PDF p.14, Definition 4.7: contractive finite-dimensional projections. Norm at most one allows the zero projection, including the zero Banach space.
--   - `InWOTClosure`: PDF p.21: weak operator closure, expressed by its finite-test neighborhoods.
--   - `dualBilinear`: PDF pp.4,20: curry an operator into a dual to an actual scalar bilinear form.
--   - `tensorFunctional`: PDF pp.20,22: weak-star topology for the precise projective predual.
--   - `InTensorWeakStarClosure`: PDF p.20: weak-star closure uses all completed tensor tests, not only pure tensors.
--   - `TensorNorming`: PDF p.22: norming on the unit sphere, vacuously true when the tensor space is zero.
--   - `CZero`: PDF pp.8–9: c0(I), nuclearOperatord by scalar functions vanishing at infinity on a discrete index.
--   - `LOne`: PDF pp.8–9: the usual absolutely summable scalar family.
--   - `IntervalL1`: PDF p.10: L1 of the unit interval with Lebesgue measure.
--   - `CircleL1`: PDF pp.10–11: L1 of the circle with Haar measure, using the additive circle R/Z.
--   - `Plane`: PDF p.10: the Euclidean plane over the same scalar field.
--   - `StrictlyConvex`: PDF p.8: strict convexity in its scalar-independent norm characterization.
--   - `BanachData`: PDF p.3: an existential Banach-space witness, with its genuine standard structures.
--   - `ContractiveFDD`: PDF pp.16–17: partial-sum projections of a constant-one FDD, with ordered convergence. Commutation and increasing ranges are encoded by P_i P_j = P_min(i,j).
--   - `HasSchauderBasis`: PDF p.16: a Schauder basis is a unique ordered partial-sum expansion, not an unconditional sum.
--   - `CZeroSum`: PDF pp.16–18: c0 sum is the closed subspace generated by one-coordinate vectors inside the sup-norm product; it is not l-infinity or Mathlib's finite-support l-zero space.
--   - `injectiveEmbedding`: PDF p.5: algebraic tensor evaluation on the dual balls, represented by a bounded bilinear form on the duals. Its bilinear norm is the supremum of absolute values, so no complex or signed supremum is used.
--   - `InjectiveProduct`: PDF p.5: completion for the injective norm, as the norm-closed algebraic image in bounded bilinear forms on the duals. This norm is the binary injective norm, not Mathlib's deprecated injectiveSeminorm on PiTensorProduct.
--   - `RadonNikodym`: PDF p.10, Example 3.12(b): the Banach-space Radon--Nikodym property. For every finite measure, every absolutely continuous vector measure of bounded variation has an integrable Bochner density. The integrability guard is essential. This is not the scalar Radon--Nikodym derivative theorem. Definition also verified against arXiv:1701.04837v2, Introduction, PDF p.1.
-- source:
--   Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4, https://arxiv.org/abs/2006.09871v4

import Mathlib

/-!
Norm-attaining tensors and nuclear operators, arXiv:2006.09871v4.
The binary algebraic product is the two-factor PiTensorProduct, with its
finite-decomposition projective seminorm, followed by Hausdorff completion.
No attaining decomposition or approximation property is built into that space.
Nuclear operators are represented by the actual quotient by the canonical map's
kernel; their norm is the quotient norm, rather than the operator norm.
-/

noncomputable section

-- Nested completed tensor and quotient dual operator spaces exceed the default search-size bound.
-- The previous bound of 512 still rejected their standard Mathlib norm instances.
set_option synthInstance.maxSize 8192

namespace QAlgorithms.Papers.Independent.Renew46.P04

open Filter Set
open scoped Topology TensorProduct ENNReal

universe u v

variable {K : Type*} [RCLike K]

/-- PDF p.3: the standard operator norm, specialized to one scalar field to keep
nested dual and quotient instance search from introducing intermediate fields. -/
@[reducible]
local instance linearOperatorNorm {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] [NormedSpace K E] [NormedSpace K F] :
    Norm (E →L[K] F) :=
  ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id K)

/-- PDF p.3: Mathlib's standard operator seminormed group, with the scalar fixed. -/
@[reducible]
local instance linearOperatorSeminormedGroup {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] [NormedSpace K E] [NormedSpace K F] :
    SeminormedAddCommGroup (E →L[K] F) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (σ₁₂ := RingHom.id K)

/-- PDF p.3: Mathlib's standard operator normed group, with the scalar fixed. -/
@[reducible]
local instance linearOperatorNormedGroup {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace K E] [NormedSpace K F] :
    NormedAddCommGroup (E →L[K] F) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id K)

/-- PDF p.3: Mathlib's standard normed scalar action on bounded linear operators. -/
@[reducible]
local instance linearOperatorNormedSpace {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] [NormedSpace K E] [NormedSpace K F] :
    NormedSpace K (E →L[K] F) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id K) (𝕜' := K)

/-- PDF p.3: cache the standard normed dual structure before forming iterated duals. -/
@[reducible]
local instance dualNormedGroup {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] :
    NormedAddCommGroup (E →L[K] K) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id K)

/-- PDF p.3: cache the standard scalar action on the continuous dual. -/
@[reducible]
local instance dualNormedSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] :
    NormedSpace K (E →L[K] K) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id K) (𝕜' := K)

example {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace K E] [NormedSpace K F] (T : E →L[K] F) :
    ‖T‖ = ContinuousLinearMap.opNorm T := rfl

/-- PDF p.3: the two Banach factors, indexed by false and true.
ULift places different carrier universes in one family without changing any norm. -/
def Factors (X : Type u) (Y : Type v) : Bool → Type (max u v)
  | false => ULift.{v} X
  | true => ULift.{u} Y

/-- PDF p.3: the normed additive structure is transported from each factor. -/
@[reducible]
instance factorsNormedAddCommGroup {X Y : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup Y] (b : Bool) :
    NormedAddCommGroup (Factors X Y b) := by cases b <;> dsimp [Factors] <;> infer_instance

/-- PDF p.3: scalar multiplication is transported from each factor. -/
instance factorsNormedSpace {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
    [NormedSpace K X] [NormedSpace K Y] (b : Bool) : NormedSpace K (Factors X Y b) := by
  cases b with
  | false =>
      exact { ULift.module' with
        norm_smul_le := fun c x => (norm_smul_le c x.down :) }
  | true =>
      exact { ULift.module' with
        norm_smul_le := fun c y => (norm_smul_le c y.down :) }

/-- PDF p.3: algebraic tensor product with the finite-decomposition projective seminorm. -/
abbrev Algebraic (K X Y : Type*) [RCLike K]
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace K X] [NormedSpace K Y] :=
  PiTensorProduct K (Factors X Y)

/-- PDF p.3: the actual normed algebraic space, obtained by Hausdorff separation
of the finite-decomposition seminorm. The separation conclusion in projective_series
identifies it faithfully with the raw algebraic tensor product. -/
abbrev NormedAlgebraic (K X Y : Type*) [RCLike K]
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace K X] [NormedSpace K Y] :=
  SeparationQuotient (Algebraic K X Y)

/-- PDF p.3: Hausdorff completion in the projective seminorm. -/
abbrev Projective (K X Y : Type*) [RCLike K]
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedSpace K X] [NormedSpace K Y] :=
  UniformSpace.Completion (NormedAlgebraic K X Y)

/-- PDF p.3: reuse the completion's standard normed group without repeatedly
searching through the binary family and separation quotient. -/
@[reducible]
instance projectiveNormedGroup {X Y : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup Y] [NormedSpace K X] [NormedSpace K Y] :
    NormedAddCommGroup (Projective K X Y) :=
  inferInstanceAs (NormedAddCommGroup
    (UniformSpace.Completion (NormedAlgebraic K X Y)))

/-- PDF p.3: reuse the completion's standard normed scalar action. -/
@[reducible]
instance projectiveNormedSpace {X Y : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup Y] [NormedSpace K X] [NormedSpace K Y] :
    NormedSpace K (Projective K X Y) :=
  inferInstanceAs (NormedSpace K
    (UniformSpace.Completion (NormedAlgebraic K X Y)))

section Banach

variable {X Y Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]
variable [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]

/-- PDF p.3: an ordered pair of vectors in the dependent two-factor family. -/
def pair (x : X) (y : Y) : (b : Bool) → Factors X Y b
  | false => ULift.up x
  | true => ULift.up y

/-- PDF p.3: the canonical algebraic inclusion. -/
def algebraicInclusion : Algebraic K X Y →L[K] Projective K X Y :=
  UniformSpace.Completion.toComplL.comp (SeparationQuotient.mkCLM K (Algebraic K X Y))

/-- PDF p.3: the canonical pure tensor. -/
def pure (x : X) (y : Y) : Projective K X Y :=
  algebraicInclusion (PiTensorProduct.tprod K (pair x y))

/-- PDF p.3: bounded bilinear maps, using exactly two multilinear coordinates. -/
abbrev Bilinear (K X Y Z : Type*) [RCLike K]
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    [NormedSpace K X] [NormedSpace K Y] [NormedSpace K Z] :=
  ContinuousMultilinearMap K (Factors X Y) Z

/-- PDF pp.3–4: canonical extension through the dense algebraic inclusion. -/
def extendBilinear (B : Bilinear K X Y Z) : Projective K X Y →L[K] Z :=
  (PiTensorProduct.liftIsometry K (Factors X Y) Z B).extend algebraicInclusion

/-- PDF p.3: canonical restriction to pure tensors, retaining the two coordinates. -/
def restrictBilinear (L : Projective K X Y →L[K] Z) : Bilinear K X Y Z :=
  (L.comp algebraicInclusion).compContinuousMultilinearMap (PiTensorProduct.tprodL K)

/-- PDF p.5, Definition 2.1: bounded sequences and actual absolutely convergent representation. -/
def TensorRep (z : Projective K X Y) (x : ℕ → X) (y : ℕ → Y) : Prop :=
  (∃ C : ℝ, ∀ n, ‖x n‖ ≤ C ∧ ‖y n‖ ≤ C) ∧
  Summable (fun n => ‖x n‖ * ‖y n‖) ∧ HasSum (fun n => pure (x n) (y n)) z

/-- PDF p.3: finite-decomposition costs on the algebraic tensor product, including
an empty decomposition for zero. The scalar coefficients in Mathlib's lift norm
are absorbed in the first factor. -/
def finiteCosts (u : Algebraic K X Y) : Set ℝ :=
  {r | ∃ (n : ℕ) (x : Fin n → X) (y : Fin n → Y),
    u = ∑ i, PiTensorProduct.tprod K (pair (x i) (y i)) ∧
    r = ∑ i, ‖x i‖ * ‖y i‖}

/-- PDF p.3: all countable representation costs, without attainment imposed. -/
def tensorCosts (z : Projective K X Y) : Set ℝ :=
  {r | ∃ x y, TensorRep z x y ∧ r = ∑' n, ‖x n‖ * ‖y n‖}

/-- PDF p.3: normalized cost formula, used only when both factors are nonzero. -/
def normalizedCosts (z : Projective K X Y) : Set ℝ :=
  {r | ∃ (a : ℕ → K) (x : ℕ → X) (y : ℕ → Y),
    Summable (fun n => ‖a n‖) ∧ (∀ n, ‖x n‖ = 1 ∧ ‖y n‖ = 1) ∧
    HasSum (fun n => a n • pure (x n) (y n)) z ∧ r = ∑' n, ‖a n‖}

/-- PDF p.5: attainment of the projective norm by some admissible representation. -/
def TensorAttains (z : Projective K X Y) : Prop := ‖z‖ ∈ tensorCosts z

example (x : X) (y : Y) :
    ‖pair x y false‖ * ‖pair x y true‖ = ‖x‖ * ‖y‖ := by
  rfl

example : pure (K := K) (0 : X) (0 : Y) = 0 := by
  unfold pure
  rw [(PiTensorProduct.tprod K).map_coord_zero false (by rfl)]
  exact map_zero _

/-- PDF p.4: the rank-one bilinear map, before completion. -/
def rankOneBilinear : Bilinear K (X →L[K] K) Y (X →L[K] Y) :=
  MultilinearMap.mkContinuous
    { toFun := fun m => ((m false).down).smulRight ((m true).down)
      map_update_add' := by
        intro _ m i a b
        cases i
        · simp only [Function.update_self,
            Function.update_of_ne (Ne.symm Bool.false_ne_true)]
          ext x
          change (a.down x + b.down x) • (m true).down =
            a.down x • (m true).down + b.down x • (m true).down
          exact add_smul _ _ _
        · simp only [Function.update_self, Function.update_of_ne Bool.false_ne_true]
          ext x
          change (m false).down x • (a.down + b.down) =
            (m false).down x • a.down + (m false).down x • b.down
          exact smul_add _ _ _
      map_update_smul' := by
        intro _ m i c a
        cases i
        · simp only [Function.update_self,
            Function.update_of_ne (Ne.symm Bool.false_ne_true)]
          ext x
          change (c * a.down x) • (m true).down =
            c • (a.down x • (m true).down)
          exact mul_smul _ _ _
        · simp only [Function.update_self, Function.update_of_ne Bool.false_ne_true]
          ext x
          change (m false).down x • (c • a.down) =
            c • ((m false).down x • a.down)
          simp only [smul_smul, mul_comm] }
    1 (by
      intro m
      change ‖((m false).down).smulRight ((m true).down)‖ ≤
        1 * ∏ i : Bool, ‖m i‖
      rw [ContinuousLinearMap.norm_smulRight_apply]
      simp only [Fintype.prod_bool, one_mul]
      change ‖(m false).down‖ * ‖(m true).down‖ ≤
        ‖(m true).down‖ * ‖(m false).down‖
      exact le_of_eq (mul_comm _ _))

/-- PDF p.4: the actual canonical map J, constructed by continuous extension. -/
def projectiveRealization : Projective K (X →L[K] K) Y →L[K] (X →L[K] Y) :=
  extendBilinear rankOneBilinear

/-- PDF p.4: full series representation, with separate boundedness and norm-product summability. -/
def NuclearRep (T : X →L[K] Y) (f : ℕ → (X →L[K] K)) (y : ℕ → Y) : Prop :=
  (∃ C : ℝ, ∀ n, ‖f n‖ ≤ C ∧ ‖y n‖ ≤ C) ∧
  Summable (fun n => ‖f n‖ * ‖y n‖) ∧
  ∀ x, HasSum (fun n => (f n x) • y n) (T x)

/-- PDF p.4: nuclear operators, as the actual range of J. -/
def NuclearRange : Submodule K (X →L[K] Y) := projectiveRealization.toLinearMap.range

/-- PDF p.4: the nuclear space with its computed quotient norm. -/
abbrev Nuclear (K X Y : Type*) [RCLike K] [NormedAddCommGroup X] [NormedSpace K X]
    [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y] :=
  Projective K (X →L[K] K) Y ⧸ (projectiveRealization (K := K) (X := X) (Y := Y)).ker

/-- PDF p.4: continuity of the constructed realization gives a closed kernel. -/
instance realizationKernelClosed : IsClosed ((projectiveRealization (K := K) (X := X) (Y := Y)).ker :
    Set (Projective K (X →L[K] K) Y)) := projectiveRealization.isClosed_ker

/-- PDF p.4: cache the standard normed quotient by the actual closed kernel. -/
@[reducible]
instance nuclearNormedGroup : NormedAddCommGroup (Nuclear K X Y) :=
  Submodule.Quotient.normedAddCommGroup
    (S := (projectiveRealization (K := K) (X := X) (Y := Y)).ker)

/-- PDF p.4: cache the standard quotient scalar action for the nuclear dual. -/
@[reducible]
instance nuclearNormedSpace : NormedSpace K (Nuclear K X Y) :=
  Submodule.Quotient.normedSpace
    (S := (projectiveRealization (K := K) (X := X) (Y := Y)).ker) K

/-- PDF p.4: quotient-descended canonical realization; no optimal lift is selected. -/
def nuclearOperator : Nuclear K X Y →L[K] (X →L[K] Y) :=
  projectiveRealization.ker.liftQL projectiveRealization le_rfl

/-- PDF p.4: quotient map from the completed projective product. -/
def nuclearQuotient : Projective K (X →L[K] K) Y →L[K] Nuclear K X Y :=
  projectiveRealization.ker.mkQL

/-- PDF p.4: series costs for an operator; used only on the nuclear range. -/
def nuclearCosts (T : X →L[K] Y) : Set ℝ :=
  {r | ∃ f y, NuclearRep T f y ∧ r = ∑' n, ‖f n‖ * ‖y n‖}

/-- PDF p.5, Definition 2.1: nuclear attainment uses the quotient nuclear norm. -/
def NuclearAttains (T : Nuclear K X Y) : Prop := ‖T‖ ∈ nuclearCosts (nuclearOperator T)

example : nuclearOperator (0 : Nuclear K X Y) = 0 := map_zero _

/-- PDF p.4: annihilator of the actual kernel inside the continuous tensor dual. -/
def Annihilator : Submodule K (Projective K (X →L[K] K) Y →L[K] K) where
  carrier := {G | ∀ z, projectiveRealization z = 0 → G z = 0}
  zero_mem' := by simp
  add_mem' := by intro G H hG hH z hz; simp [hG z hz, hH z hz]
  smul_mem' := by intro a G hG z hz; simp [hG z hz]

/-- PDF p.4: pullback of a nuclear dual functional along the actual quotient map. -/
def pullNuclearDual (H : Nuclear K X Y →L[K] K) :
    Projective K (X →L[K] K) Y →L[K] K := H.comp nuclearQuotient

/-- PDF p.4: approximation property in the source's compact-set formulation. -/
def ApproximationProperty (K X : Type*) [RCLike K] [NormedAddCommGroup X]
    [NormedSpace K X] : Prop :=
  ∀ C : Set X, IsCompact C → ∀ eps : ℝ, 0 < eps →
    ∃ T : X →L[K] X, FiniteDimensional K T.range ∧ ∀ x ∈ C, ‖T x - x‖ ≤ eps

/-- PDF p.5: classical operator-norm attainment on the unit sphere. -/
def OperatorAttains (T : X →L[K] Y) : Prop := ∃ x, ‖x‖ = 1 ∧ ‖T x‖ = ‖T‖

/-- PDF p.5: classical bilinear attainment requires both unit vectors. -/
def BilinearAttains (B : Bilinear K X Y K) : Prop :=
  ∃ x y, ‖x‖ = 1 ∧ ‖y‖ = 1 ∧ ‖B (pair x y)‖ = ‖B‖

/-- PDF p.6: projective-norm density. -/
def TensorDense (K X Y : Type*) [RCLike K] [NormedAddCommGroup X] [NormedSpace K X]
    [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y] : Prop :=
  Dense {z : Projective K X Y | TensorAttains z}

/-- PDF p.6: density in the nuclear quotient norm. -/
def NuclearDense (K X Y : Type*) [RCLike K] [NormedAddCommGroup X] [NormedSpace K X]
    [CompleteSpace X] [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y] : Prop :=
  Dense {T : Nuclear K X Y | NuclearAttains T}

/-- PDF p.12, Definition 4.1(b): the radius depends on epsilon and the fixed form. -/
def LocalBilinear (K X Y : Type*) [RCLike K] [NormedAddCommGroup X] [NormedSpace K X]
    [NormedAddCommGroup Y] [NormedSpace K Y] : Prop :=
  ∀ eps : ℝ, 0 < eps → ∀ B : Bilinear K X Y K, ‖B‖ = 1 →
    ∃ eta : ℝ, 0 < eta ∧ ∀ (x : X) (y : Y), ‖x‖ = 1 → ‖y‖ = 1 →
      1 - eta < ‖B (pair x y)‖ → ∃ (a : X) (b : Y),
        ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ ‖B (pair a b)‖ = 1 ∧ ‖x - a‖ < eps ∧ ‖y - b‖ < eps

/-- PDF p.14, Definition 4.7: contractive finite-dimensional projections.
Norm at most one allows the zero projection, including the zero Banach space. -/
def MetricPi (K X : Type*) [RCLike K] [NormedAddCommGroup X] [NormedSpace K X] : Prop :=
  ∀ eps : ℝ, 0 < eps → ∀ s : Finset X, (∀ x ∈ s, ‖x‖ = 1) →
    ∃ P : X →L[K] X, P.comp P = P ∧ ‖P‖ ≤ 1 ∧ FiniteDimensional K P.range ∧
      ∀ x ∈ s, ∃ y ∈ P.range, ‖x - y‖ < eps

example : NuclearRep (0 : X →L[K] Y) (fun _ => 0) (fun _ => 0) := by
  refine ⟨⟨0, by simp⟩, ?_, ?_⟩
  · simp
  · intro x
    simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : Y)) 0)

/-- PDF p.21: weak operator closure, expressed by its finite-test neighborhoods. -/
def InWOTClosure (s : Set (X →L[K] Y)) (T : X →L[K] Y) : Prop :=
  ∀ (a : Finset X) (b : Finset (Y →L[K] K)) (eps : ℝ), 0 < eps →
    ∃ S ∈ s, ∀ x ∈ a, ∀ f ∈ b, ‖f (T x - S x)‖ < eps

/-- PDF pp.4,20: curry an operator into a dual to an actual scalar bilinear form. -/
def dualBilinear (T : X →L[K] (Y →L[K] K)) : Bilinear K X Y K :=
  MultilinearMap.mkContinuous
    { toFun := fun m => T ((m false).down) ((m true).down)
      map_update_add' := by
        intro _ m i a b
        cases i
        · simp only [Function.update_self,
            Function.update_of_ne (Ne.symm Bool.false_ne_true)]
          change T (a.down + b.down) (m true).down =
            T a.down (m true).down + T b.down (m true).down
          simp only [map_add, ContinuousLinearMap.add_apply]
        · simp only [Function.update_self, Function.update_of_ne Bool.false_ne_true]
          change T (m false).down (a.down + b.down) =
            T (m false).down a.down + T (m false).down b.down
          exact map_add _ _ _
      map_update_smul' := by
        intro _ m i c a
        cases i
        · simp only [Function.update_self,
            Function.update_of_ne (Ne.symm Bool.false_ne_true)]
          change T (c • a.down) (m true).down = c • T a.down (m true).down
          simp only [map_smul, ContinuousLinearMap.smul_apply]
        · simp only [Function.update_self, Function.update_of_ne Bool.false_ne_true]
          change T (m false).down (c • a.down) = c • T (m false).down a.down
          exact map_smul _ _ _ }
    ‖T‖ (by
      intro m
      have h := ((T ((m false).down)).le_opNorm ((m true).down)).trans
        (mul_le_mul_of_nonneg_right (T.le_opNorm ((m false).down)) (norm_nonneg ((m true).down)))
      simp only [Fintype.prod_bool]
      change ‖T (m false).down (m true).down‖ ≤
        ‖T‖ * (‖(m true).down‖ * ‖(m false).down‖)
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h)

/-- PDF pp.20,22: weak-star topology for the precise projective predual. -/
def tensorFunctional (T : X →L[K] (Y →L[K] K)) : Projective K X Y →L[K] K :=
  extendBilinear (dualBilinear T)

/-- PDF p.20: weak-star closure uses all completed tensor tests, not only pure tensors. -/
def InTensorWeakStarClosure (s : Set (X →L[K] (Y →L[K] K)))
    (T : X →L[K] (Y →L[K] K)) : Prop :=
  ∀ (a : Finset (Projective K X Y)) (eps : ℝ), 0 < eps →
    ∃ S ∈ s, ∀ z ∈ a, ‖tensorFunctional (T - S) z‖ < eps

/-- PDF p.22: norming on the unit sphere, vacuously true when the tensor space is zero. -/
def TensorNorming (s : Set (X →L[K] (Y →L[K] K))) : Prop :=
  ∀ z : Projective K X Y, ‖z‖ = 1 → ∀ eps : ℝ, 0 < eps →
    ∃ T ∈ s, 1 - eps < ‖tensorFunctional T z‖

example (T : X →L[K] Y) (s : Set (X →L[K] Y)) (h : T ∈ s) : InWOTClosure s T := by
  intro a b eps heps
  exact ⟨T, h, by simpa using (fun x (_ : x ∈ a) f (_ : f ∈ b) => heps)⟩

end Banach

/-- PDF pp.8–9: c0(I), nuclearOperatord by scalar functions vanishing at infinity on a discrete index. -/
abbrev CZero (K I : Type*) [RCLike K] :=
  ZeroAtInftyContinuousMap (WithDiscreteTopology I) K

/-- PDF pp.8–9: the usual absolutely summable scalar family. -/
abbrev LOne (K I : Type*) [RCLike K] := lp (fun _ : I => K) 1

/-- PDF p.10: L1 of the unit interval with Lebesgue measure. -/
abbrev IntervalL1 (K : Type*) [RCLike K] :=
  MeasureTheory.Lp K 1 (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1))

/-- PDF pp.10–11: L1 of the circle with Haar measure, using the additive circle R/Z. -/
abbrev CircleL1 (K : Type*) [RCLike K] := MeasureTheory.Lp K 1
  (MeasureTheory.volume : MeasureTheory.Measure (AddCircle (1 : ℝ)))

/-- PDF p.10: the Euclidean plane over the same scalar field. -/
abbrev Plane (K : Type*) [RCLike K] := EuclideanSpace K (Fin 2)

/-- PDF p.8: strict convexity in its scalar-independent norm characterization. -/
def StrictlyConvex (Y : Type*) [NormedAddCommGroup Y] : Prop :=
  ∀ x y : Y, ‖x‖ = 1 → ‖y‖ = 1 → x ≠ y → ‖x + y‖ < 2

section SequenceResults

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

end SequenceResults

/-- PDF p.3: an existential Banach-space witness, with its genuine standard structures. -/
structure BanachData (K : Type*) [RCLike K] where
  Carrier : Type
  [group : NormedAddCommGroup Carrier]
  [space : NormedSpace K Carrier]
  [complete : CompleteSpace Carrier]

attribute [instance] BanachData.group BanachData.space BanachData.complete

/-- PDF pp.16–17: partial-sum projections of a constant-one FDD, with ordered convergence.
Commutation and increasing ranges are encoded by P_i P_j = P_min(i,j). -/
def ContractiveFDD {X : Type*} [NormedAddCommGroup X] [NormedSpace K X] : Prop :=
  ∃ P : ℕ → (X →L[K] X),
    (∀ i, FiniteDimensional K (P i).range ∧ ‖P i‖ ≤ 1) ∧
    (∀ i j, (P i).comp (P j) = P (min i j)) ∧
    ∀ x, Tendsto (fun n => P n x) atTop (𝓝 x)

/-- PDF p.16: a Schauder basis is a unique ordered partial-sum expansion, not an unconditional sum. -/
def HasSchauderBasis {X : Type*} [NormedAddCommGroup X] [NormedSpace K X] : Prop :=
  ∃ e : ℕ → X, ∀ x : X, ∃! a : ℕ → K,
    Tendsto (fun n => ∑ i ∈ Finset.range n, a i • e i) atTop (𝓝 x)

/-- PDF pp.16–18: c0 sum is the closed subspace generated by one-coordinate vectors
inside the sup-norm product; it is not l-infinity or Mathlib's finite-support l-zero space. -/
def CZeroSum {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)] [∀ n, NormedSpace K (E n)] :
    Submodule K (lp E ⊤) :=
  (Submodule.span K {v | ∃ (n : ℕ) (x : E n), v = lp.single ⊤ n x}).topologicalClosure

section InjectiveProduct

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace K X] [CompleteSpace X]
variable [NormedAddCommGroup Y] [NormedSpace K Y] [CompleteSpace Y]

/-- PDF p.5: algebraic tensor evaluation on the dual balls, represented by a bounded
bilinear form on the duals. Its bilinear norm is the supremum of absolute values,
so no complex or signed supremum is used. -/
def injectiveEmbedding : Algebraic K X Y →ₗ[K] Bilinear K (X →L[K] K) (Y →L[K] K) K :=
  PiTensorProduct.lift
    { toFun := fun m => dualBilinear
        (((NormedSpace.inclusionInDoubleDual K X) ((m false).down)).smulRight
          ((NormedSpace.inclusionInDoubleDual K Y) ((m true).down)))
      map_update_add' := by
        intro _ m i a b
        cases i
        · ext f
          simp only [ContinuousMultilinearMap.add_apply, dualBilinear,
            MultilinearMap.coe_mkContinuous, Function.update_self,
            Function.update_of_ne (Ne.symm Bool.false_ne_true)]
          change (f false).down (a.down + b.down) * (f true).down (m true).down =
            (f false).down a.down * (f true).down (m true).down +
              (f false).down b.down * (f true).down (m true).down
          simp only [map_add, add_mul]
        · ext f
          simp only [ContinuousMultilinearMap.add_apply, dualBilinear,
            MultilinearMap.coe_mkContinuous, Function.update_self,
            Function.update_of_ne Bool.false_ne_true]
          change (f false).down (m false).down * (f true).down (a.down + b.down) =
            (f false).down (m false).down * (f true).down a.down +
              (f false).down (m false).down * (f true).down b.down
          simp only [map_add, mul_add]
      map_update_smul' := by
        intro _ m i c a
        cases i
        · ext f
          simp only [ContinuousMultilinearMap.smul_apply, dualBilinear,
            MultilinearMap.coe_mkContinuous, Function.update_self,
            Function.update_of_ne (Ne.symm Bool.false_ne_true)]
          change (f false).down (c • a.down) * (f true).down (m true).down =
            c * ((f false).down a.down * (f true).down (m true).down)
          simp only [map_smul, smul_eq_mul, mul_assoc]
        · ext f
          simp only [ContinuousMultilinearMap.smul_apply, dualBilinear,
            MultilinearMap.coe_mkContinuous, Function.update_self,
            Function.update_of_ne Bool.false_ne_true]
          change (f false).down (m false).down * (f true).down (c • a.down) =
            c * ((f false).down (m false).down * (f true).down a.down)
          simp only [map_smul, smul_eq_mul, mul_assoc, mul_left_comm] }

/-- PDF p.5: completion for the injective norm, as the norm-closed algebraic image
in bounded bilinear forms on the duals. This norm is the binary injective norm,
not Mathlib's deprecated injectiveSeminorm on PiTensorProduct. -/
def InjectiveProduct : Submodule K (Bilinear K (X →L[K] K) (Y →L[K] K) K) :=
  (injectiveEmbedding (K := K) (X := X) (Y := Y)).range.topologicalClosure

/-- PDF p.5: the injective completion inherits the ambient standard scalar action. -/
@[reducible]
instance injectiveProductNormedSpace :
    NormedSpace K (InjectiveProduct (K := K) (X := X) (Y := Y)) :=
  Submodule.normedSpace
    ((injectiveEmbedding (K := K) (X := X) (Y := Y)).range.topologicalClosure)

example (x : X) (y : Y) (f : X →L[K] K) (g : Y →L[K] K) :
    injectiveEmbedding (PiTensorProduct.tprod K (pair x y)) (pair f g) = f x * g y := by
  simp [injectiveEmbedding, dualBilinear, pair, NormedSpace.dual_def]

end InjectiveProduct

/-- PDF p.10, Example 3.12(b): the Banach-space Radon--Nikodym property.
For every finite measure, every absolutely continuous vector measure of bounded
variation has an integrable Bochner density. The integrability guard is essential.
This is not the scalar Radon--Nikodym derivative theorem.
Definition also verified against arXiv:1701.04837v2, Introduction, PDF p.1. -/
def RadonNikodym (K : Type*) [RCLike K] (E : Type u) [NormedAddCommGroup E]
    [NormedSpace K E] : Prop :=
  letI := NormedSpace.restrictScalars ℝ K E
  ∀ (A : Type u) [MeasurableSpace A] (mu : MeasureTheory.Measure A),
    MeasureTheory.IsFiniteMeasure mu → ∀ nu : MeasureTheory.VectorMeasure A E,
      nu.variation Set.univ < ⊤ →
      (∀ s : Set A, mu s = 0 → nu s = 0) →
      ∃ f : A → E, MeasureTheory.Integrable f mu ∧
        ∀ s : Set A, MeasurableSet s → nu s = ∫ x in s, f x ∂mu

example (A : Type*) [MeasurableSpace A] (mu : MeasureTheory.Measure A) :
    MeasureTheory.Integrable (fun _ : A => (0 : ℝ)) mu := by simp

end QAlgorithms.Papers.Independent.Renew46.P04


