-- Prove2me | Definitions.Def_UniformGamma
-- name    : UniformGamma
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:27.491651+00:00
-- url     : https://prove2.me/theorems/28ddf24e-9834-49f1-9c62-272bd6e2ec9f
-- statement:
--   A tracial state on a unital C*-algebra D is a positive linear functional τ:D→ℂ with τ(1)=1 and τ(ab)=τ(ba); a closed star ideal is a norm-closed two-sided ideal closed under adjoint, and its quotient is given the induced quotient norm. The file packages the analytic facts needed to make the quotient, ultrapower and completion constructions into C*-algebras as hypotheses (classes NormConstruction, NullConstruction, CauchyConstruction, LimitConstruction, TraceConstruction) rather than proving them: quotients by closed star ideals are normed rings with ‖xy‖≤‖x‖‖y‖, ‖x*‖=‖x‖ and ‖x‖²≤‖x*x‖; families of traces are closed under the stated null, Cauchy and ultralimit operations; and ultralimit traces vanish on null sequences. Given a family τ=(τᵢ) of tracial states, the trace 2-norm of a is √Re τ(a*a), and the family norm is its supremum over i. A bounded sequence is τ-null along a filter if its family norm tends to 0, and the null sequences form a closed star ideal of the bounded sequences ℓ^∞(X,D); the ultrapower along an ultrafilter U is the quotient by it. Sequences that are Cauchy in the family norm form a C*-subalgebra of ℓ^∞(ℕ,D); quotienting by its null sequences gives the uniform tracial completion, which is nontrivial because each completion trace takes value 1 at 1. The file also defines ultralimit traces, traces on the ultrapower from sequences of traces, pullbacks of traces along star-homomorphisms, the diagonal embedding of D into the ultrapower, and descent of a trace vanishing on an ideal to the quotient. A C*-algebra is topologically simple if its only closed two-sided ideals are 0 and everything, nuclear if every tensor product with any C*-algebra admits at most one C*-norm, stably finite if every n×n matrix over it with v*v=1 also satisfies vv*=1, and of real rank zero if every self-adjoint element is approximable within any ε>0 by a self-adjoint element with finite spectrum. For a separable nontrivial A, UniformPropertyGammaAt(A,U) asks for a projection p in the ultrapower of the uniform tracial completion (built from the family of all tracial states of A) that commutes with the image of every x in the completion and satisfies τ_s(p·x)=½τ_s(x) for every x and every sequence s of tracial states of A, where τ_s is the limit trace along U. Statement is the defined proposition that for every separable, nontrivial, infinite-dimensional, topologically simple, nuclear, stably finite C*-algebra A with a nonempty tracial state space, and every ultrafilter U on ℕ that refines the cofinite filter and whose ultrapower of the completion has real rank zero, this property holds. MainClaim is the defined proposition asserting that the five construction classes can be satisfied and that Statement then holds; it is not asserted here to be a proved theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/UniformGamma.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/UniformGamma.lean; bytes 16..25315
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

/-!
The final claim constructs the tracial quotients and states the original gamma assertion.
`Analysis.TracialSplitting.Challenge.main_iff_original` verifies statement preservation.
-/

universe uA uD uE uI uR uX u v

namespace Pureness

open scoped ComplexOrder

structure CStarAlgebraNorm (R : Type uR) [Ring R] [StarRing R] [Algebra ℂ R]
    extends AlgebraNorm ℂ R where
  cstar : ∀ x, toAlgebraNorm (star x * x) = toAlgebraNorm x * toAlgebraNorm x

structure TracialState (A : Type uA) [CStarAlgebra A] [PartialOrder A] where
  functional : A →ₚ[ℂ] ℂ
  normalized : functional 1 = 1
  tracial : ∀ a b : A, functional (a * b) = functional (b * a)

structure ClosedStarIdeal (D : Type uD) [CStarAlgebra D] where
  ideal : TwoSidedIdeal D
  star_mem : ∀ {u : D}, u ∈ ideal → star u ∈ ideal
  isClosed : IsClosed (ideal : Set D)

end Pureness

universe uNuclear

namespace ComparatorModel

namespace Pureness

open scoped TensorProduct ComplexOrder

abbrev CStarAlgebraNorm := @_root_.OAI.Pureness.CStarAlgebraNorm

def IsNuclear (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (B : Type v) [CStarAlgebra B], Subsingleton (CStarAlgebraNorm (A ⊗[ℂ] B))

abbrev TracialState := @_root_.OAI.Pureness.TracialState

end Pureness

namespace CurrentMain

open _root_.OAI.ComparatorModel.Pureness

open scoped ComplexOrder

def RealRankZero (D : Type) [CStarAlgebra D] : Prop :=
  ∀ a : D, IsSelfAdjoint a → ∀ ε : ℝ, 0 < ε →
    ∃ b : D, IsSelfAdjoint b ∧ (spectrum ℂ b).Finite ∧ ‖a - b‖ < ε

def traceTwoNorm {D : Type} [CStarAlgebra D] [PartialOrder D]
    (τ : TracialState D) (a : D) : ℝ :=
  Real.sqrt (τ.functional (star a * a)).re

end CurrentMain

section

open Filter

open scoped Topology NNReal ENNReal

abbrev Pureness.ClosedStarIdeal := @_root_.OAI.Pureness.ClosedStarIdeal

namespace Pureness.ClosedStarIdeal

section

variable {D : Type} [CStarAlgebra D] (J : ClosedStarIdeal D)

abbrev Quotient := J.ideal.ringCon.Quotient

def quotientMap : D →ₐ[ℂ] J.Quotient := J.ideal.ringCon.mkₐ ℂ

instance quotientStar : Star (J.Quotient) where
  star := Quotient.map' star (by
    intro u v h
    change J.ideal.ringCon u v at h
    change J.ideal.ringCon (star u) (star v)
    rw [TwoSidedIdeal.rel_iff] at h ⊢
    simpa only [star_sub] using J.star_mem h)

instance quotientStarRing : StarRing (J.Quotient) where
  star_involutive x := Quotient.inductionOn' x (fun u => congrArg J.quotientMap (star_star u))
  star_mul x y := Quotient.inductionOn₂' x y (fun u v => congrArg J.quotientMap (star_mul u v))
  star_add x y := Quotient.inductionOn₂' x y (fun u v => congrArg J.quotientMap (star_add u v))

instance quotientStarModule : StarModule ℂ (J.Quotient) where
  star_smul c x := Quotient.inductionOn' x (fun u => congrArg J.quotientMap (star_smul c u))

abbrev idealSubmodule : Submodule ℂ (D) :=
  (J.quotientMap).toLinearMap.ker

instance idealSubmodule_closed : IsClosed (J.idealSubmodule : Set D) := by
  have he : (J.idealSubmodule : Set D) = (J.ideal : Set D) := by
    ext u
    change J.ideal.ringCon.mk' u = J.ideal.ringCon.mk' 0 ↔ u ∈ J.ideal
    exact Quotient.eq
  rw [he]
  exact J.isClosed

def quotientLinearEquiv :
    (D ⧸ J.idealSubmodule) ≃ₗ[ℂ] J.Quotient :=
  (J.quotientMap).toLinearMap.quotKerEquivOfSurjective ((J.ideal.ringCon.mkₐ_surjective (α := ℂ)))

instance quotientNormedAddCommGroup : NormedAddCommGroup (J.Quotient) :=
  NormedAddCommGroup.induced _ _ (J.quotientLinearEquiv).symm
    (J.quotientLinearEquiv).symm.injective

instance quotientNormedSpace : NormedSpace ℂ (J.Quotient) :=
  NormedSpace.induced ℂ _ _ (J.quotientLinearEquiv).symm

def quotientNormEquiv : J.Quotient ≃ₗᵢ[ℂ]
    (D ⧸ J.idealSubmodule) where
  __ := (J.quotientLinearEquiv).symm
  norm_map' _ := rfl

instance quotientCompleteSpace : CompleteSpace (J.Quotient) :=
  (J.quotientNormEquiv).toIsometryEquiv.completeSpace_iff.mpr inferInstance

class NormConstruction : Prop where
  mul_le : ∀ {D : Type} [CStarAlgebra D] (J : ClosedStarIdeal D) (x y : J.Quotient),
    ‖x*y‖ ≤ ‖x‖*‖y‖
  star_eq : ∀ {D : Type} [CStarAlgebra D] (J : ClosedStarIdeal D) (x : J.Quotient),
    ‖star x‖ = ‖x‖
  square_le : ∀ {D : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (J : ClosedStarIdeal D) (x : J.Quotient), ‖x‖ * ‖x‖ ≤ ‖star x * x‖

variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction]

instance quotientNormedRing : NormedRing (J.Quotient) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le := NormConstruction.mul_le J

instance quotientNormedAlgebra : NormedAlgebra ℂ (J.Quotient) where
  norm_smul_le := norm_smul_le

instance quotientNormedStarGroup : NormedStarGroup (J.Quotient) where
  norm_star_le x := (NormConstruction.star_eq J x).le

end

open Filter

open scoped Topology NNReal ENNReal

variable {D : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (J : ClosedStarIdeal D)

variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction]

instance quotientCStarAlgebra : CStarAlgebra (J.Quotient) where
  norm_mul_self_le := NormConstruction.square_le J

end Pureness.ClosedStarIdeal

end

section

open _root_.OAI.ComparatorModel.Pureness

section UniformTraceNorm

variable {D : Type} {I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (τ : I → TracialState D) [Nonempty I]

variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction]

def CurrentMain.familyTwoNorm (a : D) : ℝ := ⨆ i, traceTwoNorm (τ i) a

end UniformTraceNorm

open _root_.OAI.ComparatorModel.Pureness Filter

open scoped Topology NNReal ENNReal

variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction]

instance CurrentMain.boundedFamilyProductCStar {X : Type} {D : Type} [CStarAlgebra D] [Nontrivial D] :
    CStarAlgebra (lp (fun _ : X => D) ∞) where

section UniformNull

variable {D : Type} {I : Type} {X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (τ : I → TracialState D) [Nonempty I]

def CurrentMain.IsFamilyNull (F : Filter X) (u : X → D) : Prop :=
  Tendsto (fun n => familyTwoNorm τ (u n)) F (𝓝 0)

class CurrentMain.NullConstruction : Prop where
  zero : ∀ {D I X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] (τ : I → Pureness.TracialState D) [Nonempty I]
    (F : Filter X), IsFamilyNull τ F (fun _ => 0)
  add : ∀ {D I X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] (τ : I → Pureness.TracialState D) [Nonempty I]
    {F : Filter X} {u v : X → D}, IsFamilyNull τ F u → IsFamilyNull τ F v →
    IsFamilyNull τ F (fun n => u n + v n)
  neg : ∀ {D I X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] (τ : I → Pureness.TracialState D) [Nonempty I]
    {F : Filter X} {u : X → D}, IsFamilyNull τ F u → IsFamilyNull τ F (fun n => -u n)
  star : ∀ {D I X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] (τ : I → Pureness.TracialState D) [Nonempty I]
    {F : Filter X} {u : X → D}, IsFamilyNull τ F u → IsFamilyNull τ F (fun n => star (u n))
  mul_left : ∀ {D I X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] (τ : I → Pureness.TracialState D) [Nonempty I]
    {F : Filter X} {u v : X → D}, IsFamilyNull τ F v → ∀ {M : ℝ},
    (∀ n, ‖u n‖ ≤ M) → IsFamilyNull τ F (fun n => u n * v n)
  mul_right : ∀ {D I X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] (τ : I → Pureness.TracialState D) [Nonempty I]
    {F : Filter X} {u v : X → D}, IsFamilyNull τ F u → ∀ {M : ℝ},
    (∀ n, ‖v n‖ ≤ M) → IsFamilyNull τ F (fun n => u n * v n)
  closed : ∀ {D I X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] (τ : I → Pureness.TracialState D) [Nonempty I] (F : Filter X),
    IsClosed {u : lp (fun _ : X => D) ∞ | IsFamilyNull τ F (fun n => u n)}

variable [Nontrivial D]

variable [ComparatorModel.CurrentMain.NullConstruction]

def CurrentMain.familyNullTwoSided (F : Filter X) : TwoSidedIdeal (lp (fun _ : X => D) ∞) :=
  TwoSidedIdeal.mk' {u | IsFamilyNull τ F (fun n => u n)}
    (NullConstruction.zero τ F)
    (fun hu hv => NullConstruction.add τ hu hv)
    (fun hu => NullConstruction.neg τ hu)
    (fun {u _} hv => NullConstruction.mul_left τ hv
      (lp.norm_apply_le_norm ENNReal.top_ne_zero u))
    (fun {_ v} hu => NullConstruction.mul_right τ hu
      (lp.norm_apply_le_norm ENNReal.top_ne_zero v))

def CurrentMain.familyNullIdeal (F : Filter X) : ClosedStarIdeal (lp (fun _ : X => D) ∞) where
  ideal := familyNullTwoSided τ F
  star_mem := by
    intro u hu
    apply (TwoSidedIdeal.mem_mk' _ _ _ _ _ _ (star u)).mpr
    exact NullConstruction.star τ ((TwoSidedIdeal.mem_mk' _ _ _ _ _ _ u).mp hu)
  isClosed := by
    have he : (familyNullTwoSided τ F : Set (lp (fun _ : X => D) ∞)) =
        {u | IsFamilyNull τ F (fun n => u n)} := by
      ext u
      exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ u
    rw [he]
    exact NullConstruction.closed τ F

end UniformNull

variable {D : Type} {I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (τ : I → TracialState D) [Nonempty I]

variable [ComparatorModel.CurrentMain.NullConstruction]

def CurrentMain.IsFamilyCauchy (u : ℕ → D) : Prop :=
  IsFamilyNull τ (atTop : Filter (ℕ × ℕ)) (fun p => u p.1 - u p.2)

class CurrentMain.CauchyConstruction : Prop where
  const : ∀ {D I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (τ : I → Pureness.TracialState D) [Nonempty I] (a : D), IsFamilyCauchy τ (fun _ => a)
  add : ∀ {D I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (τ : I → Pureness.TracialState D) [Nonempty I] {u v : ℕ → D},
    IsFamilyCauchy τ u → IsFamilyCauchy τ v → IsFamilyCauchy τ (fun n => u n+v n)
  star : ∀ {D I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (τ : I → Pureness.TracialState D) [Nonempty I] {u : ℕ → D},
    IsFamilyCauchy τ u → IsFamilyCauchy τ (fun n => star (u n))
  mul : ∀ {D I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (τ : I → Pureness.TracialState D) [Nonempty I] {u v : ℕ → D},
    IsFamilyCauchy τ u → IsFamilyCauchy τ v → ∀ {M N : ℝ},
    (∀ n, ‖u n‖ ≤ M) → (∀ n, ‖v n‖ ≤ N) → IsFamilyCauchy τ (fun n => u n*v n)
  closed : ∀ {D I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (τ : I → Pureness.TracialState D) [Nonempty I] [Nontrivial D],
    IsClosed {u : lp (fun _ : ℕ => D) ∞ | IsFamilyCauchy τ (fun n => u n)}

variable [Nontrivial D]

variable [ComparatorModel.CurrentMain.CauchyConstruction]

def CurrentMain.familyCauchyAlgebra : StarSubalgebra ℂ (lp (fun _ : ℕ => D) ∞) where
  carrier := {u | IsFamilyCauchy τ (fun n => u n)}
  zero_mem' := CauchyConstruction.const τ 0
  one_mem' := CauchyConstruction.const τ 1
  add_mem' hu hv := CauchyConstruction.add τ hu hv
  mul_mem' {u v} hu hv := CauchyConstruction.mul τ hu hv
    (lp.norm_apply_le_norm ENNReal.top_ne_zero u)
    (lp.norm_apply_le_norm ENNReal.top_ne_zero v)
  algebraMap_mem' z := CauchyConstruction.const τ (algebraMap ℂ D z)
  star_mem' hu := CauchyConstruction.star τ hu

instance CurrentMain.familyCauchy_complete : CompleteSpace (familyCauchyAlgebra τ) :=
  (CauchyConstruction.closed τ).completeSpace_coe

instance CurrentMain.familyCauchy_cstar : CStarAlgebra (familyCauchyAlgebra τ) where

def CurrentMain.familyCauchyNullIdeal : ClosedStarIdeal (familyCauchyAlgebra τ) where
  ideal := TwoSidedIdeal.comap (familyCauchyAlgebra τ).val.toRingHom
    (familyNullIdeal τ atTop).ideal
  star_mem := by
    intro u hu
    apply (familyNullIdeal τ atTop).star_mem hu
  isClosed := by
    exact (familyNullIdeal τ atTop).isClosed.preimage
      (continuous_subtype_val : Continuous (fun u : familyCauchyAlgebra τ => u.1))

abbrev CurrentMain.UniformTracialCompletion := (familyCauchyNullIdeal τ).Quotient

end

section

open scoped ComplexOrder

variable {D : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction]

instance Pureness.ClosedStarIdeal.quotientOrder (J : ClosedStarIdeal D) : PartialOrder J.Quotient :=
  CStarAlgebra.spectralOrder _

instance Pureness.ClosedStarIdeal.quotientStarOrdered (J : ClosedStarIdeal D) : StarOrderedRing J.Quotient :=
  CStarAlgebra.spectralOrderedRing _

variable (J : Pureness.ClosedStarIdeal D)

variable (τ : Pureness.TracialState D) (hτ : ∀ a ∈ J.ideal, τ.functional a = 0)

def Pureness.ClosedStarIdeal.descendedValue : J.Quotient → ℂ := Quotient.lift τ.functional (by
  intro u v huv
  change J.ideal.ringCon u v at huv
  rw [TwoSidedIdeal.rel_iff] at huv
  have h := hτ (u-v) huv
  rw [map_sub, sub_eq_zero] at h
  exact h)

def Pureness.ClosedStarIdeal.descendedLinear : J.Quotient →ₗ[ℂ] ℂ where
  toFun := J.descendedValue τ hτ
  map_add' x y := Quotient.inductionOn₂' x y (fun u v => τ.functional.map_add u v)
  map_smul' c x := Quotient.inductionOn' x (fun u => τ.functional.map_smul c u)

def Pureness.ClosedStarIdeal.descendedTrace : TracialState J.Quotient where
  functional := { J.descendedLinear τ hτ with
    monotone' := by
      intro x y hxy
      apply sub_nonneg.mp
      change 0 ≤ J.descendedLinear τ hτ y - J.descendedLinear τ hτ x
      rw [← map_sub]
      obtain ⟨z,hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hxy)
      rw [hz]
      induction z using Quotient.inductionOn' with
      | h u => exact τ.functional.map_nonneg (star_mul_self_nonneg u) }
  normalized := τ.normalized
  tracial x y := Quotient.inductionOn₂' x y (fun u v => τ.tracial u v)

end

section

open _root_.OAI.ComparatorModel.Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

section UltraTrace

variable {D : Type} {X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]

variable (θ : X → TracialState D) (U : Ultrafilter X)

variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction]

instance CurrentMain.boundedFamilyProductOrder : PartialOrder (lp (fun _ : X => D) ∞) :=
  CStarAlgebra.spectralOrder _

instance CurrentMain.boundedFamilyProductStarOrdered : StarOrderedRing (lp (fun _ : X => D) ∞) :=
  CStarAlgebra.spectralOrderedRing _

def CurrentMain.ultraTraceValue (u : lp (fun _ : X => D) ∞) : ℂ :=
  limUnder (U : Filter X) (fun n => (θ n).functional (u n))

class CurrentMain.LimitConstruction : Prop where
  tendsto : ∀ {D X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]
    (θ : X → Pureness.TracialState D) (U : Ultrafilter X) (u : lp (fun _ : X => D) ∞),
    Tendsto (fun n => (θ n).functional (u n)) (U : Filter X) (𝓝 (ultraTraceValue θ U u))

variable [ComparatorModel.CurrentMain.LimitConstruction]

def CurrentMain.ultraTraceLinear : lp (fun _ : X => D) ∞ →ₗ[ℂ] ℂ where
  toFun := ultraTraceValue θ U
  map_add' u v := by
    apply tendsto_nhds_unique (LimitConstruction.tendsto θ U (u+v))
    simpa only [lp.coeFn_add, Pi.add_apply, map_add] using
      (LimitConstruction.tendsto θ U u).add (LimitConstruction.tendsto θ U v)
  map_smul' z u := by
    apply tendsto_nhds_unique (LimitConstruction.tendsto θ U (z • u))
    simpa only [lp.coeFn_smul, Pi.smul_apply, map_smul, RingHom.id_apply, smul_eq_mul] using
      (LimitConstruction.tendsto θ U u).const_mul z

def CurrentMain.boundedFamilyEval (n : X) : lp (fun _ : X => D) ∞ →⋆ₐ[ℂ] D where
  toFun u := u n
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

def CurrentMain.ultraTrace : TracialState (lp (fun _ : X => D) ∞) where
  functional := { ultraTraceLinear θ U with
    monotone' := by
      intro u v huv
      exact le_of_tendsto_of_tendsto (LimitConstruction.tendsto θ U u)
        (LimitConstruction.tendsto θ U v) (Eventually.of_forall (fun n =>
          (θ n).functional.monotone (map_rel (boundedFamilyEval n) huv))) }
  normalized := by
    apply tendsto_nhds_unique (LimitConstruction.tendsto θ U 1)
    have he (n : X) : (θ n).functional ((1 : lp (fun _ : X => D) ∞) n) = 1 :=
      (θ n).normalized
    simp only [he]
    exact tendsto_const_nhds
  tracial u v := by
    change ultraTraceValue θ U (u*v) = ultraTraceValue θ U (v*u)
    apply tendsto_nhds_unique (LimitConstruction.tendsto θ U (u*v))
    have he (n : X) : (θ n).functional ((u*v) n) = (θ n).functional ((v*u) n) :=
      (θ n).tracial (u n) (v n)
    simpa only [he] using LimitConstruction.tendsto θ U (v*u)

end UltraTrace

section UniformQuotient

variable {D : Type} {I : Type} {X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]

variable (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)

variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction] [ComparatorModel.CurrentMain.LimitConstruction]

abbrev CurrentMain.FamilyUltrapower := (familyNullIdeal τ (U : Filter X)).Quotient

class CurrentMain.TraceConstruction : Prop where
  null : ∀ {D I X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D] (τ : I → Pureness.TracialState D) [Nonempty I]
    (U : Ultrafilter X) (s : X → I) (u : lp (fun _ : X => D) ∞),
    IsFamilyNull τ (U : Filter X) (fun n => u n) →
      (ultraTrace (fun n => τ (s n)) U).functional u = 0

variable [ComparatorModel.CurrentMain.TraceConstruction]

def CurrentMain.familyLimitTrace (s : X → I) : TracialState (FamilyUltrapower τ U) :=
  (familyNullIdeal τ (U : Filter X)).descendedTrace
    (ultraTrace (fun n => τ (s n)) U) (fun u hu => by
      apply TraceConstruction.null τ U s u
      have he : u ∈ familyNullTwoSided τ (U : Filter X) ↔
          IsFamilyNull τ (U : Filter X) (fun n => u n) := by
        unfold familyNullTwoSided
        exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ u
      exact he.mp hu)

end UniformQuotient

section PullbackTrace

variable {D : Type} {E : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]

variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction] [ComparatorModel.CurrentMain.LimitConstruction] [ComparatorModel.CurrentMain.TraceConstruction]

def CurrentMain.pullbackTrace (τ : TracialState E) (ι : D →⋆ₐ[ℂ] E) : TracialState D where
  functional := { τ.functional.toLinearMap.comp ι.toLinearMap with
    monotone' := fun _ _ h => τ.functional.monotone (map_rel ι h) }
  normalized := by change τ.functional (ι 1) = 1; rw [map_one, τ.normalized]
  tracial x y := by
    change τ.functional (ι (x*y)) = τ.functional (ι (y*x))
    rw [map_mul ι x y, map_mul ι y x]
    exact τ.tracial _ _

end PullbackTrace

section CompletionTraces

variable {D : Type} {I : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I]

variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction] [ComparatorModel.CurrentMain.LimitConstruction] [ComparatorModel.CurrentMain.TraceConstruction]

instance CurrentMain.familyCauchyOrder : PartialOrder (familyCauchyAlgebra τ) :=
  CStarAlgebra.spectralOrder _

instance CurrentMain.familyCauchyStarOrdered : StarOrderedRing (familyCauchyAlgebra τ) :=
  CStarAlgebra.spectralOrderedRing _

def CurrentMain.cauchyTrace (i : I) : TracialState (familyCauchyAlgebra τ) :=
  pullbackTrace (ultraTrace (fun _ : ℕ => τ i) (Ultrafilter.of atTop))
    (familyCauchyAlgebra τ).subtype

def CurrentMain.completionTrace (i : I) : TracialState (UniformTracialCompletion τ) :=
  (familyCauchyNullIdeal τ).descendedTrace (cauchyTrace τ i) (fun u hu => by
    apply TraceConstruction.null τ (Ultrafilter.of atTop) (fun _ => i) u.1
    have he : u.1 ∈ familyNullTwoSided τ atTop ↔
        IsFamilyNull τ atTop (fun n => u.1 n) := by
      unfold familyNullTwoSided
      exact TwoSidedIdeal.mem_mk' _ _ _ _ _ _ u.1
    have hn : IsFamilyNull τ atTop (fun n => u.1 n) := he.mp hu
    exact hn.mono_left (Ultrafilter.of_le atTop))

def CurrentMain.boundedFamilyConstant {X : Type} (a : D) : lp (fun _ : X => D) ∞ :=
  ⟨fun _ => a, memℓp_infty_iff.mpr ⟨‖a‖,by rintro _ ⟨n,rfl⟩; exact le_rfl⟩⟩

instance CurrentMain.completionNontrivial : Nontrivial (UniformTracialCompletion τ) := by
  obtain ⟨i⟩ := ‹Nonempty I›
  refine ⟨⟨1,0,?_⟩⟩
  intro h
  have he := congrArg (completionTrace τ i).functional h
  rw [(completionTrace τ i).normalized, map_zero] at he
  exact one_ne_zero he

end CompletionTraces

variable {D : Type} {I : Type} {X : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)

variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction] [ComparatorModel.CurrentMain.LimitConstruction] [ComparatorModel.CurrentMain.TraceConstruction]

def CurrentMain.familyUltrapowerMap : D →⋆ₐ[ℂ] FamilyUltrapower τ U where
  toFun a := (familyNullIdeal τ (U : Filter X)).quotientMap (boundedFamilyConstant a)
  map_zero' := (familyNullIdeal τ (U : Filter X)).quotientMap.map_zero
  map_one' := (familyNullIdeal τ (U : Filter X)).quotientMap.map_one
  map_add' a b := (familyNullIdeal τ (U : Filter X)).quotientMap.map_add
    (boundedFamilyConstant a) (boundedFamilyConstant b)
  map_mul' a b := (familyNullIdeal τ (U : Filter X)).quotientMap.map_mul
    (boundedFamilyConstant a) (boundedFamilyConstant b)
  commutes' z := (familyNullIdeal τ (U : Filter X)).quotientMap.commutes z
  map_star' _a := rfl

end

section

open Filter Topology

variable {A : Type uA} [NormedRing A]

variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction] [ComparatorModel.CurrentMain.LimitConstruction] [ComparatorModel.CurrentMain.TraceConstruction]

def Pureness.TopologicallySimple (A : Type uA) [NormedRing A] : Prop :=
  ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤

end

section

open _root_.OAI.ComparatorModel.Pureness Filter

variable [ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction] [ComparatorModel.CurrentMain.NullConstruction] [ComparatorModel.CurrentMain.CauchyConstruction] [ComparatorModel.CurrentMain.LimitConstruction] [ComparatorModel.CurrentMain.TraceConstruction]

def CurrentMain.StablyFinite (A : Type uA) [CStarAlgebra A] : Prop :=
  ∀ n : ℕ, ∀ v : CStarMatrix (Fin n) (Fin n) A,
    star v*v = 1 → v*star v = 1

def CurrentMain.UniformPropertyGammaAt (A : Type) [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
    [Nonempty (TracialState A)] (U : Ultrafilter ℕ) : Prop :=
  ∃ p : FamilyUltrapower (completionTrace (fun τ : TracialState A => τ)) U,
    IsStarProjection p ∧ ∀ x : UniformTracialCompletion (fun τ : TracialState A => τ),
      p * familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x =
        familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x * p ∧
      ∀ s : ℕ → TracialState A,
        (familyLimitTrace (completionTrace (fun τ : TracialState A => τ)) U s).functional
          (p * familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x) =
        (1/2 : ℂ) *
        (familyLimitTrace (completionTrace (fun τ : TracialState A => τ)) U s).functional
          (familyUltrapowerMap (completionTrace (fun τ : TracialState A => τ)) U x)

open _root_.OAI.ComparatorModel.Pureness Filter

def CurrentMain.Statement : Prop := ∀
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (_hsimple : TopologicallySimple A) (_hinf : ¬FiniteDimensional ℂ A)
    (_hA : IsNuclear.{0, uNuclear} A) (_hfinite : StablyFinite A)
    [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
    (_hfree : (U : Filter ℕ) ≤ atTop)
    (_hRR : RealRankZero (FamilyUltrapower (completionTrace (fun τ : TracialState A => τ)) U)),
    UniformPropertyGammaAt A U

end

def CurrentMain.MainClaim : Prop :=
  ∃ h0 : ComparatorModel.Pureness.ClosedStarIdeal.NormConstruction, letI := h0;
  ∃ h1 : ComparatorModel.CurrentMain.NullConstruction, letI := h1;
  ∃ h2 : ComparatorModel.CurrentMain.CauchyConstruction, letI := h2;
  ∃ h3 : ComparatorModel.CurrentMain.LimitConstruction, letI := h3;
  ∃ h4 : ComparatorModel.CurrentMain.TraceConstruction, letI := h4;
  Statement.{uNuclear}



end ComparatorModel
end
end OAI


