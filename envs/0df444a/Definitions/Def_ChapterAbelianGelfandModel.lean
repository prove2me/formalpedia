-- Prove2me | Definitions.Def_ChapterAbelianGelfandModel
-- name    : ChapterAbelianGelfandModel
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-09T10:09:50.86398+00:00
-- url     : https://prove2.me/theorems/fe56d5a8-0526-4913-9c3c-04097095bd9e
-- title:
--   The Lean 4 theorem `star_sqrtC_mul` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterAbelianGelfandModel.lean`): generated def bundle for ChapterAbelianGelfandModel. See BookProof/ChapterAbelianGelfandModel.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterAbelianGelfandModel.lean

import Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_coeFn

import Definitions.Def_ChapterLinftyMultiplication
import Mathlib


/-!
# The measure model of a commutative C*-algebra (plan GAP-2, the Gelfand step)

`ChapterAbelianAtomicCondensation` closes the *atomic* half of the abelian
classification and `ChapterLinftyMaximalAbelian` the *diffuse* half, both for
algebras that are already given as operators on a concrete `L²`.  The step that
the plan records as the remaining obstruction of GAP-2 is the passage in the
other direction: from an **abstract** abelian algebra to a **measure model**.

This module supplies that passage at the C*-level, which is exactly the classical
Gelfand–Naimark plus Riesz–Markov–Kakutani route:

1. Gelfand duality (Mathlib's `gelfandStarTransform`) identifies a commutative
   unital C*-algebra `A` with `C(X, ℂ)` for the compact Hausdorff character space
   `X = characterSpace ℂ A`.
2. Riesz–Markov–Kakutani turns a **state** of `C(X, ℂ)` into a Borel *probability
   measure* on `X` (`exists_probabilityMeasure_of_state`).
3. `L²(μ)` then carries the **multiplication representation** of `C(X, ℂ)`
   (`mulRepHom`, a unital `*`-homomorphism into the bounded operators), which is
   *injective* whenever the measure charges every nonempty open set, and for which
   the constant function `1` is a unit vector implementing the original state
   (`inner_oneVec_mulRep`).

Putting the three together, the headline `state_is_vector_state_of_multiplication`
says: **every state of a commutative unital C*-algebra is the vector state of a
representation of that algebra by multiplication operators on an `L²` space of a
probability measure.**  This is the concrete (abelian) Gelfand–Naimark–Segal
model, i.e. precisely the "abstract algebra ⇒ measure model" direction.

## Deliverables

* `rieszStateMeasure`, `integral_rieszStateMeasure`,
  `isProbabilityMeasure_rieszStateMeasure` — a positive unital real-linear
  functional on `C(X, ℝ)` (`X` compact Hausdorff) is integration against a Borel
  probability measure;
* `exists_probabilityMeasure_of_state` — the complex form: a state of the
  C*-algebra `C(X, ℂ)` is integration against a Borel probability measure;
* `contMemLpTop`, `mulRep`, `mulRepHom`, `mulRepHom_injective` — the
  multiplication representation of `C(X, ℂ)` on `L²(μ)` as a unital
  `*`-homomorphism, faithful when `μ` charges the nonempty open sets;
* `oneVec`, `inner_oneVec_mulRep` — the cyclic unit vector and the vector state
  it implements;
* `gelfandModel`, `gelfandModel_isometry` — the Gelfand identification
  `A ≃⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ)`;
* `multiplicationRep` and HEADLINE `state_is_vector_state_of_multiplication` — the
  abelian GNS measure model of an abstract commutative unital C*-algebra.

## What is still not claimed

The remaining GAP-2 obstruction is now sharper: this gives the **C*-level** model
(a *state*, a Borel probability measure, and a `*`-representation by
multiplication).  The *von Neumann*-level statement — that a **weakly closed**
abelian algebra on a separable `L²` is unitarily equivalent to *all* of `L∞(μ)`
acting on `L²(μ)` — additionally needs the bicommutant theorem and the σ-weak
continuity of the model, neither of which is available in Mathlib.  Nothing here
is `sorry`-ed.
-/

open MeasureTheory Complex WeakDual CompactlySupported CompactlySupportedContinuousMap
open scoped ComplexOrder

namespace BookProof.ChapterAbelianGelfandModel

open BookProof.ChapterLinftyMultiplication

/-! ## 1. Riesz–Markov–Kakutani: a positive unital functional is a probability measure -/

section Riesz
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- A positive real-linear functional on `C(X, ℝ)`, `X` compact, read as a positive
linear map on the compactly supported continuous functions (the two spaces agree
on a compact space). -/
noncomputable def positiveCcMap (L : C(X, ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ L f) : C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toFun f := L (f : C(X, ℝ))
  map_add' f g := by
    have h : ((f + g : C_c(X, ℝ)) : C(X, ℝ)) = (f : C(X, ℝ)) + g := rfl
    rw [h, map_add]
  map_smul' c f := by
    have h : ((c • f : C_c(X, ℝ)) : C(X, ℝ)) = c • (f : C(X, ℝ)) := rfl
    rw [h, map_smul]
    rfl
  monotone' := by
    intro f g hfg
    have h : 0 ≤ L ((g : C(X, ℝ)) - f) := by
      apply hL
      intro x
      simpa using hfg x
    simp only [map_sub] at h
    linarith

/-- **The Riesz measure of a positive functional.** -/
noncomputable def rieszStateMeasure (L : C(X, ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ L f) : Measure X :=
  RealRMK.rieszMeasure (positiveCcMap L hL)

instance instIsFiniteMeasureRieszStateMeasure (L : C(X, ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ L f) : IsFiniteMeasure (rieszStateMeasure L hL) := by
  unfold rieszStateMeasure
  infer_instance

/-- **Riesz–Markov–Kakutani.**  The functional is integration against its Riesz measure. -/
theorem integral_rieszStateMeasure (L : C(X, ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ L f) (f : C(X, ℝ)) :
    ∫ x, f x ∂(rieszStateMeasure L hL) = L f := by
  have h := RealRMK.integral_rieszMeasure (positiveCcMap L hL)
    (CompactlySupportedContinuousMap.continuousMapEquiv f)
  have hΛ : positiveCcMap L hL (CompactlySupportedContinuousMap.continuousMapEquiv f) = L f :=
    rfl
  rw [rieszStateMeasure]
  exact hΛ ▸ h

/-- A *unital* positive functional gives a **probability** measure. -/
theorem isProbabilityMeasure_rieszStateMeasure (L : C(X, ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ L f) (hone : L 1 = 1) :
    IsProbabilityMeasure (rieszStateMeasure L hL) := by
  constructor
  have h : ∫ _x : X, (1 : ℝ) ∂(rieszStateMeasure L hL) = 1 := by
    have h1 := integral_rieszStateMeasure L hL 1
    simpa [hone] using h1
  have h' : ((rieszStateMeasure L hL) Set.univ).toReal = 1 := by
    have h2 : (rieszStateMeasure L hL).real Set.univ = 1 := by
      rw [← h, integral_const]
      simp
    simpa [Measure.real] using h2
  exact (ENNReal.toReal_eq_one_iff _).mp h'

end Riesz

/-! ## 2. States of `C(X, ℂ)` are probability measures -/

section ComplexState

variable {X : Type*} [TopologicalSpace X]

/-- A real-valued continuous function read as a complex-valued one. -/
def toC (f : C(X, ℝ)) : C(X, ℂ) :=
  ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

@[simp] theorem toC_apply (f : C(X, ℝ)) (x : X) : toC f x = (f x : ℂ) := rfl

/-- The real-linear functional attached to a complex functional: the real part of its
values on real functions. -/
noncomputable def realPartFunctional (psi : C(X, ℂ) →ₗ[ℂ] ℂ) :
    C(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := (psi (toC f)).re
  map_add' f g := by
    have h : toC (f + g) = toC f + toC g := by ext x; simp
    rw [h, map_add]
    simp
  map_smul' c f := by
    have h : toC (c • f) = (c : ℂ) • toC f := by ext x; simp
    rw [h, map_smul]
    simp

/-- The pointwise square root of a nonnegative continuous function, read complex. -/
noncomputable def sqrtC (f : C(X, ℝ)) : C(X, ℂ) :=
  toC ⟨fun x => Real.sqrt (f x), Real.continuous_sqrt.comp f.continuous⟩

theorem star_sqrtC_mul (f : C(X, ℝ)) (hf : 0 ≤ f) :
    star (sqrtC f) * sqrtC f = toC f := by
  ext x
  have hx : (0 : ℝ) ≤ f x := by simpa using hf x
  have hs : Real.sqrt (f x) * Real.sqrt (f x) = f x := Real.mul_self_sqrt hx
  simp only [sqrtC, ContinuousMap.mul_apply, ContinuousMap.star_apply, toC_apply,
    RCLike.star_def, Complex.conj_ofReal, ContinuousMap.coe_mk]
  rw [← Complex.ofReal_mul, hs]

/-- On a nonnegative real function a positive functional takes a nonnegative real
value: `f = |√f|²`. -/
theorem psi_nonneg_of_nonneg (psi : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hpos : ∀ g : C(X, ℂ), 0 ≤ psi (star g * g)) (f : C(X, ℝ)) (hf : 0 ≤ f) :
    0 ≤ (psi (toC f)).re ∧ (psi (toC f)).im = 0 := by
  have h := hpos (sqrtC f)
  rw [star_sqrtC_mul f hf] at h
  exact ⟨(Complex.le_def.mp h).1, ((Complex.le_def.mp h).2).symm⟩

theorem realPartFunctional_nonneg (psi : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hpos : ∀ g : C(X, ℂ), 0 ≤ psi (star g * g)) (f : C(X, ℝ)) (hf : 0 ≤ f) :
    0 ≤ realPartFunctional psi f :=
  (psi_nonneg_of_nonneg psi hpos f hf).1

/-- A positive functional takes **real** values on real functions (`f = f⁺ - f⁻`). -/
theorem realPartFunctional_ofReal (psi : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hpos : ∀ g : C(X, ℂ), 0 ≤ psi (star g * g)) (f : C(X, ℝ)) :
    psi (toC f) = (realPartFunctional psi f : ℂ) := by
  have hp : (0 : C(X, ℝ)) ≤ f ⊔ 0 := le_sup_right
  have hm : (0 : C(X, ℝ)) ≤ (-f) ⊔ 0 := le_sup_right
  have hsub : toC f = toC (f ⊔ 0) - toC ((-f) ⊔ 0) := by
    ext x
    simp only [toC_apply, ContinuousMap.sub_apply, ContinuousMap.sup_apply,
      ContinuousMap.zero_apply, ContinuousMap.neg_apply]
    rw [← Complex.ofReal_sub]
    congr 1
    rcases le_total (f x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_right (by linarith)]
      ring
  have him : (psi (toC f)).im = 0 := by
    rw [hsub, map_sub]
    simp [(psi_nonneg_of_nonneg psi hpos _ hp).2, (psi_nonneg_of_nonneg psi hpos _ hm).2]
  exact Complex.ext (by simp [realPartFunctional]) (by simp [him])

end ComplexState

/-! ### The measure of a state -/

section StateMeasure

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  (psi : C(X, ℂ) →ₗ[ℂ] ℂ) (hpos : ∀ g : C(X, ℂ), 0 ≤ psi (star g * g))

/-- **The measure of a state** of `C(X, ℂ)`: the Riesz measure of its real part. -/
noncomputable def stateMeasure : Measure X :=
  rieszStateMeasure (realPartFunctional psi) (realPartFunctional_nonneg psi hpos)

instance instIsFiniteMeasureStateMeasure : IsFiniteMeasure (stateMeasure psi hpos) := by
  unfold stateMeasure
  infer_instance

instance instRegularStateMeasure : (stateMeasure psi hpos).Regular := by
  unfold stateMeasure rieszStateMeasure
  infer_instance









end StateMeasure

/-! ## 3. The cyclic vector `1` of `L²(μ)` -/

section OneVec

variable {X : Type*} [MeasurableSpace X] (mu : Measure X)

/-- The constant function `1`, as a vector of `L²(μ)` for a finite measure. -/
noncomputable def oneVec [IsFiniteMeasure mu] : Lp ℂ 2 mu := (memLp_const (1 : ℂ)).toLp _





end OneVec

/-! ## 4. The multiplication representation of `C(X, ℂ)` on `L²(μ)` -/

section MultRep

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (mu : Measure X)

/-- A continuous function on a compact space is essentially bounded. -/
theorem contMemLpTop (f : C(X, ℂ)) : MemLp (fun x => f x) ⊤ mu := by
  have hm : AEStronglyMeasurable (fun x => f x) mu := (map_continuous f).aestronglyMeasurable
  obtain ⟨C, hC⟩ := (isCompact_range (map_continuous f)).isBounded.subset_closedBall 0
  refine memLp_top_of_bound hm C (.of_forall fun x => ?_)
  simpa using hC (Set.mem_range_self x)

/-- **The multiplication representation**: a continuous symbol acting on `L²(μ)`. -/
noncomputable def mulRep (f : C(X, ℂ)) : Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu :=
  multOp (fun x => f x) (contMemLpTop mu f)

theorem mulRep_coeFn (f : C(X, ℂ)) (u : Lp ℂ 2 mu) :
    (mulRep mu f u : X → ℂ) =ᵐ[mu] fun x => f x * (u : X → ℂ) x :=
  multOp_coeFn _ _ u

theorem mulRep_one : mulRep mu 1 = 1 := by
  refine ContinuousLinearMap.ext fun u => Lp.ext ?_
  filter_upwards [mulRep_coeFn mu 1 u] with x hx
  simpa using hx

theorem mulRep_mul (f g : C(X, ℂ)) : mulRep mu (f * g) = (mulRep mu f) * (mulRep mu g) := by
  refine ContinuousLinearMap.ext fun u => Lp.ext ?_
  filter_upwards [mulRep_coeFn mu (f * g) u, mulRep_coeFn mu g u,
    mulRep_coeFn mu f (mulRep mu g u)] with x h1 h2 h3
  simp only [ContinuousLinearMap.mul_apply, h1, h3, h2, ContinuousMap.mul_apply]
  ring

theorem mulRep_add (f g : C(X, ℂ)) : mulRep mu (f + g) = mulRep mu f + mulRep mu g := by
  refine ContinuousLinearMap.ext fun u => Lp.ext ?_
  filter_upwards [mulRep_coeFn mu (f + g) u, mulRep_coeFn mu f u, mulRep_coeFn mu g u,
    Lp.coeFn_add (mulRep mu f u) (mulRep mu g u)] with x h1 h2 h3 h4
  simp only [ContinuousLinearMap.add_apply, h4, Pi.add_apply, h1, h2, h3,
    ContinuousMap.add_apply]
  ring

theorem mulRep_smul (c : ℂ) (f : C(X, ℂ)) : mulRep mu (c • f) = c • mulRep mu f := by
  refine ContinuousLinearMap.ext fun u => Lp.ext ?_
  filter_upwards [mulRep_coeFn mu (c • f) u, mulRep_coeFn mu f u,
    Lp.coeFn_smul c (mulRep mu f u)] with x h1 h2 h3
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, h3, h1, h2,
    ContinuousMap.smul_apply, smul_eq_mul]
  ring

theorem mulRep_zero : mulRep mu 0 = 0 := by
  have h := mulRep_smul mu 0 1
  simpa using h

/-- **Star-preservation**: the adjoint of a multiplication operator multiplies by the
conjugate symbol. -/
theorem mulRep_star (f : C(X, ℂ)) : mulRep mu (star f) = star (mulRep mu f) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).mpr fun u v => ?_
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [mulRep_coeFn mu (star f) u, mulRep_coeFn mu f v] with x h1 h2
  simp only [h1, h2, RCLike.inner_apply, ContinuousMap.star_apply, RCLike.star_def, map_mul,
    Complex.conj_conj]
  ring

/-- The multiplication representation as a unital `*`-homomorphism into the bounded
operators of `L²(μ)`. -/
noncomputable def mulRepHom : C(X, ℂ) →⋆ₐ[ℂ] (Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) where
  toFun f := mulRep mu f
  map_one' := mulRep_one mu
  map_mul' := mulRep_mul mu
  map_zero' := mulRep_zero mu
  map_add' := mulRep_add mu
  map_star' f := mulRep_star mu f
  commutes' r := by
    have h : (algebraMap ℂ C(X, ℂ)) r = r • (1 : C(X, ℂ)) := by
      ext x
      simp [Algebra.algebraMap_eq_smul_one]
    rw [h, mulRep_smul, mulRep_one]
    rfl

@[simp] theorem mulRepHom_apply (f : C(X, ℂ)) : mulRepHom mu f = mulRep mu f := rfl





end MultRep

/-! ## 5. The Gelfand model of an abstract commutative unital C*-algebra -/

section Gelfand

variable (A : Type*) [CommCStarAlgebra A]

/-- The character space of `A` carries its Borel σ-algebra. -/
noncomputable scoped instance instMeasurableSpaceCharacterSpace :
    MeasurableSpace (characterSpace ℂ A) :=
  borel _

scoped instance instBorelSpaceCharacterSpace : BorelSpace (characterSpace ℂ A) := ⟨rfl⟩

/-- **Gelfand duality** (Mathlib's `gelfandStarTransform`): a commutative unital
C*-algebra is `*`-isomorphic to the continuous functions on its character space. -/
noncomputable def gelfandModel : A ≃⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ) :=
  gelfandStarTransform A



variable {A}

/-- The representation of `A` by multiplication operators on `L²(μ)`, obtained by
composing the Gelfand transform with the multiplication representation. -/
noncomputable def multiplicationRep (mu : Measure (characterSpace ℂ A)) :
    A →⋆ₐ[ℂ] (Lp ℂ 2 mu →L[ℂ] Lp ℂ 2 mu) :=
  (mulRepHom mu).comp (gelfandModel A : A →⋆ₐ[ℂ] C(characterSpace ℂ A, ℂ))



end Gelfand

end BookProof.ChapterAbelianGelfandModel


