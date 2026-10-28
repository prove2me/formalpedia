-- Prove2me | Definitions.Def_OAIQ039C035
-- name    : OAIQ039C035
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T06:21:51.917791+00:00
-- url     : https://prove2.me/theorems/3a1c60fe-0b4e-416c-b9ca-69ed8efdf704
-- title:
--   Definitions bundle OAIQ039C035 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 40 declarations of OpenAI's Lean: 15 definitions and 25 theorems. The definitions and types are `OAI.Kadison.Decomposable.scalarVectorMultiplier`, `OAI.Kadison.FaithfulNormalFunctional.gnsEmbedding`, `OAI.Kadison.FinitePatching.ConjugatedWords.encode`, `OAI.Kadison.FinitePatching.PartialUnitary.add`, `OAI.Kadison.FinitePatching.PartialUnitary.complement`, `OAI.Kadison.FinitePatching.PartialUnitary.completed`, `OAI.Kadison.FinitePatching.PartialUnitary.completion`, `OAI.Kadison.FinitePatching.PartialUnitary.map`, `OAI.Kadison.FinitePatching.PartialUnitary.ofUnitary`, `OAI.Kadison.FinitePatching.PartialUnitary.zero`, `OAI.Kadison.FinitePatching.Words.MomentBound`, `OAI.Kadison.FinitePatching.Words.letter`, `OAI.Kadison.FinitePatching.Words.slotPower`, `OAI.Kadison.FinitePatching.Words.word`, `OAI.Kadison.PartialIsometryOrder.Link.extend`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_ConjugatedWordAlgebra`, `Commutator_FactorComparison`, `Commutator_FactorCorner`, `Commutator_FaithfulVectorGNS`, `Commutator_FiniteFactorComparison`, `Commutator_L2InfiniteSumCoordinates`, `Commutator_PartialUnitaryAlgebra`, `Commutator_PartialUnitaryCompletion`, `Commutator_PartialUnitaryHom`, `Commutator_PartialUnitaryOrder`, `Commutator_PartialUnitaryWords`, `Commutator_PartialWordPerturbation`, `Commutator_PolarExtension`, `Commutator_PolarSupport`.
--
--   **Imports.** It imports the bundles `OAIQ039C022`, `OAIQ039C023`, `OAIQ039C024` and `OAIQ039C025` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ039C045`, `OAIQ039C046`, `OAIQ039C048`, `OAIQ039C051`, `OAIQ039C052` and `OAIQ039C053`; the statements `OAI.Kadison.CyclicSpectral.stableUnitary_intertwines`, `OAI.Kadison.Decomposable.vector_indicator_of_scalar`, `OAI.Kadison.FaithfulNormalFunctional.gnsEmbedding_intertwines`, `OAI.Kadison.FinitePatching.ConjugatedWords.free_of_centered_unitary_words`, `OAI.Kadison.FinitePatching.Words.momentBound_add`, `OAI.Kadison.FinitePatching.Words.moment_limit_of_contractions`, `OAI.Kadison.FinitePatching.Words.moment_limit_of_dense_coefficients`, `OAI.Kadison.FinitePatching.Words.word_perturbation_bound`, `OAI.Kadison.FinitePatching.exists_all_unitary_tests`, `OAI.Kadison.FinitePatching.exists_almost_full_finite_tests`, `OAI.Kadison.FinitePatching.exists_countable_unitary_tests`, `OAI.Kadison.FinitePatching.exists_finite_word_patch`, `OAI.Kadison.FinitePatching.exists_full_unitary_finite_tests` and `OAI.Kadison.TracialSequence.pullUnitary_moment_limits`; the proofs of `OAI.Kadison.CyclicSpectral.stableUnitary_intertwines`, `OAI.Kadison.Decomposable.vector_indicator_of_scalar`, `OAI.Kadison.FaithfulNormalFunctional.gnsEmbedding_intertwines`, `OAI.Kadison.FinitePatching.ConjugatedWords.free_of_centered_unitary_words`, `OAI.Kadison.FinitePatching.Words.momentBound_add`, `OAI.Kadison.FinitePatching.Words.moment_limit_of_contractions`, `OAI.Kadison.PositiveWOT.positive_strong_null`, `OAI.Kadison.PositiveWOT.threshold_exhaustion`, `OAI.Kadison.RelativeCornerQuantization.exists_polar_cut` and `OAI.Kadison.TracialSequence.pullUnitary_moment_limits`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C022
import Definitions.Def_OAIQ039C023
import Definitions.Def_OAIQ039C024
import Definitions.Def_OAIQ039C025

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

variable (A : Type*) [CStarAlgebra A]

namespace PartialUnitary

variable {A}

@[simp] lemma power_negSucc (v : PartialUnitary A) (n : ℕ) :
    v.power (.negSucc n)=(star v.val)^(n+1) := rfl

lemma power_support (v : PartialUnitary A) (k : ℤ) : v.power k*v.support=v.power k := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => exact v.projection.isIdempotentElem.eq
    | succ n =>
      simp only [power,pow_succ,mul_assoc,v.mul_support]
  | negSucc n => simp only [power,pow_succ,mul_assoc,v.star_mul_support]

lemma support_power (v : PartialUnitary A) (k : ℤ) : v.support*v.power k=v.power k := by
  cases k with
  | ofNat n =>
    cases n with
    | zero => exact v.projection.isIdempotentElem.eq
    | succ n => simp only [power,pow_succ',←mul_assoc,v.support_mul]
  | negSucc n => simp only [power,pow_succ',←mul_assoc,v.support_mul_star]

lemma orthogonal_support_symm {v w : PartialUnitary A}
    (h : v.support*w.support=0) : w.support*v.support=0 := by
  simpa only [StarMul.star_mul,v.projection.isSelfAdjoint.star_eq,w.projection.isSelfAdjoint.star_eq,
    star_zero] using congrArg star h

lemma power_mul_power_zero {v w : PartialUnitary A} (h : v.support*w.support=0)
    (k l : ℤ) : v.power k*w.power l=0 := by
  calc
    _=(v.power k*v.support)*(w.support*w.power l) := by rw [power_support,support_power]
    _=0 := by rw [mul_assoc,←mul_assoc v.support,h,zero_mul,mul_zero]

lemma star_val_mul_zero {v w : PartialUnitary A} (h : v.support*w.support=0) :
    star v.val*w.val=0 := by simpa [power] using power_mul_power_zero h (Int.negSucc 0) 1

lemma val_mul_star_zero {v w : PartialUnitary A} (h : v.support*w.support=0) :
    v.val*star w.val=0 := by simpa [power] using power_mul_power_zero h 1 (Int.negSucc 0)

def add (v w : PartialUnitary A) (h : v.support*w.support=0) : PartialUnitary A where
  val := v.val+w.val
  support := v.support+w.support
  projection := by
    constructor
    · dsimp [IsIdempotentElem]
      rw [add_mul,mul_add,mul_add,v.projection.isIdempotentElem.eq,
        w.projection.isIdempotentElem.eq,h,orthogonal_support_symm h]
      simp
    · exact v.projection.isSelfAdjoint.add w.projection.isSelfAdjoint
  star_mul := by
    rw [star_add,add_mul,mul_add,mul_add,v.star_mul,w.star_mul,
      star_val_mul_zero h,star_val_mul_zero (orthogonal_support_symm h)]
    simp
  mul_star := by
    rw [star_add,add_mul,mul_add,mul_add,v.mul_star,w.mul_star,
      val_mul_star_zero h,val_mul_star_zero (orthogonal_support_symm h)]
    simp
  mul_support := by
    have h1 := power_mul_power_zero h 1 0
    have h2 := power_mul_power_zero (orthogonal_support_symm h) 1 0
    simp [power] at h1 h2
    rw [add_mul,mul_add,mul_add,v.mul_support,w.mul_support,h1,h2]
    simp
  support_mul := by
    have h1 := power_mul_power_zero h 0 1
    have h2 := power_mul_power_zero (orthogonal_support_symm h) 0 1
    simp [power] at h1 h2
    rw [add_mul,mul_add,mul_add,v.support_mul,w.support_mul,h1,h2]
    simp

def zero : PartialUnitary A where
  val := 0
  support := 0
  projection := IsStarProjection.zero A
  star_mul := by simp
  mul_star := by simp
  mul_support := by simp
  support_mul := by simp

@[simp] lemma zero_power (k : ℤ) : (zero : PartialUnitary A).power k=0 := by
  cases k with
  | ofNat n => cases n <;> simp [power,zero]
  | negSucc n => simp [power,zero]

end PartialUnitary

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryOrder
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.PartialUnitary

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
@[ext] lemma ext {v w : PartialUnitary A} (h : v.val=w.val) : v=w := by
  have hp : v.support=w.support := by rw [←v.star_mul,←w.star_mul,h]
  cases v
  cases w
  cases h
  cases hp
  rfl

end Kadison.FinitePatching.PartialUnitary

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryCompletion
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.PartialUnitary

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def ofUnitary (u : unitary A) : PartialUnitary A where
  val := u
  support := 1
  projection := IsStarProjection.one A
  star_mul := u.property.1
  mul_star := u.property.2
  mul_support := mul_one _
  support_mul := one_mul _

def complement (v : PartialUnitary A) : PartialUnitary A where
  val := 1-v.support
  support := 1-v.support
  projection := v.projection.one_sub
  star_mul := by rw [v.projection.one_sub.isSelfAdjoint.star_eq]; exact v.projection.one_sub.isIdempotentElem.eq
  mul_star := by rw [v.projection.one_sub.isSelfAdjoint.star_eq]; exact v.projection.one_sub.isIdempotentElem.eq
  mul_support := v.projection.one_sub.isIdempotentElem.eq
  support_mul := v.projection.one_sub.isIdempotentElem.eq

omit [PartialOrder A] [StarOrderedRing A] in
lemma support_complement_zero (v : PartialUnitary A) : v.support*v.complement.support=0 := by
  change v.support*(1-v.support)=0
  rw [mul_sub,mul_one,v.projection.isIdempotentElem.eq,sub_self]

def completed (v : PartialUnitary A) : PartialUnitary A := v.add v.complement v.support_complement_zero

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma completed_val (v : PartialUnitary A) : v.completed.val=v.val+(1-v.support) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma completed_support (v : PartialUnitary A) : v.completed.support=1 := by
  change v.support+(1-v.support)=1
  abel

def completion (v : PartialUnitary A) : unitary A :=
  ⟨v.completed.val,by constructor <;> simp only [v.completed.star_mul,v.completed.mul_star,completed_support]⟩

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma completion_val (v : PartialUnitary A) : (v.completion:A)=v.val+(1-v.support) := rfl

end Kadison.FinitePatching.PartialUnitary

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryWords
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.FinitePatching

namespace Words

variable {A J K : Type*} [CStarAlgebra A]

variable (x : J → A) (k : K → ℤ)

def slotPower (v : PartialUnitary A) : Slot K → A
  | none => 1
  | some none => v.support
  | some (some i) => v.power (k i)

def letter (v : PartialUnitary A) (i : Letter J K) : A := x i.1*slotPower k v i.2

def word (v : PartialUnitary A) (l : List (Letter J K)) : A := wordProduct (letter x k v) l

@[simp] lemma word_nil (v : PartialUnitary A) : word x k v []=1 := rfl

@[simp] lemma word_cons (v : PartialUnitary A) (i : Letter J K) (l : List (Letter J K)) :
    word x k v (i::l)=letter x k v i*word x k v l := rfl

end Words

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialUnitaryHom
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

variable {A B J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

namespace PartialUnitary

def map (φ : A →⋆ₐ[ℂ] B) (v : PartialUnitary A) : PartialUnitary B where
  val := φ v.val
  support := φ v.support
  projection := v.projection.map φ
  star_mul := by rw [←map_star,←map_mul,v.star_mul]
  mul_star := by rw [←map_star,←map_mul,v.mul_star]
  mul_support := by rw [←map_mul,v.mul_support]
  support_mul := by rw [←map_mul,v.support_mul]

end PartialUnitary

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PartialWordPerturbation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

namespace Words

variable {A J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

variable (x : J → A) (k : K → ℤ)

def MomentBound (v : PartialUnitary A) (N : ℕ) (B : ℝ) : Prop :=
  (∀ i,‖τ (v.power (k i))‖ ≤ B) ∧
    ∀ l : List (Letter J K), l≠[] → l.length ≤ N → Valid l → ‖τ (word x k v l)‖ ≤ B

end Words

end Kadison.FinitePatching

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ConjugatedWordAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.ConjugatedWords

open Words

variable {B J : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

def encode (color : J → Bool) (σ : Bool) : List J → List (Letter J Bool)
  | [] => []
  | a::l => (a,transition (color a) (front color σ l))::encode color σ l

@[simp] lemma encode_length (color : J → Bool) (σ : Bool) (l : List J) :
    (encode color σ l).length=l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [encode,ih]

end Kadison.FinitePatching.ConjugatedWords

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PolarSupport
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma initial_mul_abs (T : H →L[ℂ] H) : rightSupport T*CFC.abs T=CFC.abs T := by
  ext x
  apply Submodule.starProjection_eq_self_iff.mpr
  exact (absToInitial T x).property

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FactorCorner
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.FactorCorner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_nonzero_corner (M : VonNeumannAlgebra H) (hf : IsFactor M)
    {e f : H →L[ℂ] H} (he : e∈M) (hee : e≠0) (hff : f≠0) :
    ∃ a∈M, f*a*e≠0 := by
  by_contra! h
  have hz : ∀ x∈supportSpace M e, f x=0 := by
    intro x hx
    apply closure_minimal (t := {x | f x=0}) ?_
      (isClosed_eq f.continuous continuous_const) hx
    have hspan : Submodule.span ℂ {x | ∃ a∈M, ∃ ξ : H, a (e ξ)=x} ≤ LinearMap.ker f.toLinearMap := by
      apply Submodule.span_le.mpr
      rintro y ⟨a,ha,ξ,rfl⟩
      exact congrArg (fun T : H →L[ℂ] H => T ξ) (h a ha)
    exact hspan
  apply hff
  ext x
  have hm := (supportSpace M e).starProjection_apply_mem x
  rw [centralSupport_eq_one M hf he hee] at hm
  exact hz x hm

end Kadison.FactorCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PolarExtension
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma partialIsometry_extends {W V : H →L[ℂ] H} (hW : ‖W‖≤1)
    (hV : V*star V*V=V) (hext : W*(star V*V)=V) :
    partialIsometry W*(star V*V)=V ∧ star V*V ≤ rightSupport W := by
  let P := star V*V
  have hP : IsStarProjection P := by
    constructor
    · change (star V*V)*(star V*V)=star V*V
      calc
        _=star V*(V*star V*V) := by noncomm_ring
        _=star V*V := by rw [hV]
    · exact IsSelfAdjoint.star_mul_self V
  have hwpos : 0≤1-star W*W := by
    apply sub_nonneg.mpr
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg W)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg W]
  have hcomp : P*(1-star W*W)*P=0 := by
    have hextstar : P*star W=star V := by
      simpa only [star_mul,star_star] using congrArg star hext
    calc
      _=P*P-(P*star W)*(W*P) := by noncomm_ring
      _=0 := by rw [hP.isIdempotentElem.eq,hextstar,hext]; exact sub_self P
  have hz := positive_kills_of_compression hwpos hP.isSelfAdjoint hcomp
  have hsq : (star W*W)*P=P := by
    rw [sub_mul,one_mul,sub_eq_zero] at hz
    exact hz.symm
  have hAP : CFC.abs W*P=P := abs_fixes_of_square_fixes hsq
  constructor
  · change partialIsometry W*P=V
    calc
      _=partialIsometry W*(CFC.abs W*P) := by rw [hAP]
      _=V := by rw [←mul_assoc,factorization,hext]
  · apply (hP.le_iff_mul_eq_right (isProjection_rightSupport W)).mpr
    change rightSupport W*P=P
    calc
      _=rightSupport W*(CFC.abs W*P) := by rw [hAP]
      _=P := by rw [←mul_assoc,initial_mul_abs,hAP]

end Kadison.Polar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FactorComparison
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Link

variable {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}

lemma residual_cross (v : Link M e f) (he : IsStarProjection e) (hf : IsStarProjection f)
    (w : Link M (e-v.initial) (f-v.final)) :
    star v.val*w.val=0 ∧ v.val*star w.val=0 := by
  constructor
  · have hstar := congrArg star v.final_mul
    simp only [star_mul,v.final_projection.isSelfAdjoint.star_eq] at hstar
    calc
      _=(star v.val*v.final)*w.val := by rw [hstar]
      _=0 := by rw [mul_assoc,v.final_mul_residual hf w,mul_zero]
  · have hstar := congrArg star (v.residual_mul_initial he w)
    simp only [star_mul,v.initial_projection.isSelfAdjoint.star_eq,star_zero] at hstar
    calc
      _=(v.val*v.initial)*star w.val := by rw [v.mul_initial]
      _=0 := by rw [mul_assoc,hstar,mul_zero]

def extend (v : Link M e f) (he : IsStarProjection e) (hf : IsStarProjection f)
    (w : Link M (e-v.initial) (f-v.final)) : Link M e f := by
  have hvw := (v.residual_cross he hf w).1
  have hvw' := (v.residual_cross he hf w).2
  have hwv : star w.val*v.val=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hvw
  have hwv' : w.val*star v.val=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hvw'
  have hinit : star (v.val+w.val)*(v.val+w.val)=v.initial+w.initial := by
    simp only [star_add,add_mul,mul_add,hvw,hwv,add_zero,zero_add,initial]
  have hfinal : (v.val+w.val)*star (v.val+w.val)=v.final+w.final := by
    simp only [star_add,add_mul,mul_add,hvw',hwv',add_zero,zero_add,final]
  refine ⟨v.val+w.val,M.add_mem v.mem w.mem,?_,?_,?_⟩
  · rw [star_add]
    simp only [add_mul,mul_add,hvw',hwv',zero_add,add_zero]
    rw [v.triple,w.triple]
    have h1 : v.val*star v.val*w.val=0 := by rw [mul_assoc,hvw,mul_zero]
    have h2 : w.val*star w.val*v.val=0 := by rw [mul_assoc,hwv,mul_zero]
    rw [h1,h2,add_zero,zero_add]
  · rw [hinit]
    calc
      _ ≤ v.initial+(e-v.initial) := add_le_add_right w.source_le _
      _=e := by abel
  · rw [hfinal]
    calc
      _ ≤ v.final+(f-v.final) := add_le_add_right w.target_le _
      _=f := by abel

@[simp] lemma extend_val (v : Link M e f) (he : IsStarProjection e) (hf : IsStarProjection f)
    (w : Link M (e-v.initial) (f-v.final)) : (v.extend he hf w).val=v.val+w.val := rfl

lemma le_extend (v : Link M e f) (he : IsStarProjection e) (hf : IsStarProjection f)
    (w : Link M (e-v.initial) (f-v.final)) : v≤v.extend he hf w := by
  obtain ⟨hvw,_⟩ := v.residual_cross he hf w
  have hwv : star w.val*v.val=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hvw
  apply (le_def _ _).mpr
  constructor
  · change v.initial ≤ star (v.val+w.val)*(v.val+w.val)
    simp only [star_add,add_mul,mul_add,hvw,hwv,add_zero,zero_add]
    exact le_add_of_nonneg_right w.initial_projection.nonneg
  · change (v.val+w.val)*v.initial=v.val
    rw [add_mul,v.mul_initial,v.residual_mul_initial he w,add_zero]

end Link

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FaithfulVectorGNS
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology ENNReal

namespace Kadison.FaithfulNormalFunctional

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (x : ℕ → H)

variable (M : VonNeumannAlgebra H)

def gnsEmbedding : (restricted x M).GNS →ₗᵢ[ℂ] InfiniteAmplification.Space ℕ H :=
  VectorGNS.embedding (restricted x M)
    ((InfiniteAmplification.diagonal (H:=H) (ι:=ℕ)).comp M.subtype) (vector x) (fun a => (vector_inner x a.val).symm)

end Kadison.FaithfulNormalFunctional

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteFactorComparison
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.PartialIsometryOrder.instCompleteSpaceSubtypeMemSubmoduleComplexFamilySpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Link

variable {M : VonNeumannAlgebra H} {e f : H →L[ℂ] H}

lemma initial_mem (v : Link M e f) : v.initial∈M := M.mul_mem (M.star_mem' v.mem) v.mem

lemma final_mem (v : Link M e f) : v.final∈M := M.mul_mem v.mem (M.star_mem' v.mem)

lemma trace_initial_final (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))
    (v : Link M e f) : τ ⟨v.initial,v.initial_mem⟩=τ ⟨v.final,v.final_mem⟩ :=
  hτ (star (⟨v.val,v.mem⟩ : M)) ⟨v.val,v.mem⟩

end Link

end Kadison.PartialIsometryOrder

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_L2InfiniteSumCoordinates
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped InnerProductSpace Topology ENNReal

namespace Kadison.Decomposable

open InfiniteAmplification

local instance l2InfiniteSumCoordinatesDecidableEq_rb61230_1 {α : Sort*} : DecidableEq α := Classical.decEq α
variable {Ω H ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [TopologicalSpace Ω] [CompactSpace Ω] [BorelSpace Ω]

def scalarVectorMultiplier (f : C(Ω,ℂ)) : Lp H 2 μ →L[ℂ] Lp H 2 μ :=
  operator μ (fun x => f x • (1 : H →L[ℂ] H))
    (fun z => f.continuous.aestronglyMeasurable.smul aestronglyMeasurable_const)
    (Eventually.of_forall (fun x => by
      calc
        ‖f x • (1 : H →L[ℂ] H)‖=‖f x‖*‖(1 : H →L[ℂ] H)‖ := norm_smul _ _
        _≤‖f x‖*1 := mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
        _≤‖f‖ := by simpa using f.norm_coe_le_norm x))

end Kadison.Decomposable

end

end
end

end OAI
end


