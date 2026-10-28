-- Prove2me | Definitions.Def_OAIQ039C072
-- name    : OAIQ039C072
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:22:32.092981+00:00
-- url     : https://prove2.me/theorems/6825dfb7-e211-4e25-b20f-35853a56276c
-- title:
--   Definitions bundle OAIQ039C072 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 7 declarations of OpenAI's Lean: 3 definitions and 4 theorems. The definitions and types are `OAI.Kadison.TracialSequence.generatedFreeAlgebra`, `OAI.Kadison.TracialSequence.relativeUltrapower`, `OAI.Kadison.TracialSequence.subalgebraState`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_RelativeSequenceRange`, `Commutator_TracialGeneratedAlgebra`, `Commutator_TracialSequenceTrace`, `Commutator_TracialVectorSubalgebra`.
--
--   **Imports.** It imports the bundles `OAIQ039C067` and `OAIQ039C069` of this split.
--
--   **Imported by** (directly, in this split): the statements `OAI.Kadison.TracialSequence.double_compression_preserves`, `OAI.Kadison.TracialSequence.double_embedding`, `OAI.Kadison.TracialSequence.free_position_small_corners_bound`, `OAI.Kadison.TracialSequence.generatedFreeAlgebra_constants` and `OAI.Kadison.TracialSequence.generatedFreeAlgebra_natural_of_range`; the proofs of `OAI.Kadison.TracialSequence.double_compression_preserves`, `OAI.Kadison.TracialSequence.double_embedding`, `OAI.Kadison.TracialSequence.freeCornerPosition_of_unitary_abstract`, `OAI.Kadison.TracialSequence.free_position_small_corners_bound`, `OAI.Kadison.TracialSequence.generatedFreeAlgebra_constants`, `OAI.Kadison.TracialSequence.generatedFreeAlgebra_natural_of_range` and `OAI.Kadison.TracialSequence.generated_free_small_corners_bound`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C067
import Definitions.Def_OAIQ039C069

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequenceTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison

namespace TracialSequence

open TracialGNS HilbertSequence

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

include hτ in
lemma trace_faithful {T : boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω}
    (hT : T∈Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))
    (hz : sequenceTrace τ ω (star T*T)=0) : T=0 := by
  have hv : T (sequenceVacuum τ ω)=0 := by
    rw [sequenceTrace,VectorFunctional.functional_star_mul] at hz
    exact inner_self_eq_zero.mp hz
  apply bicommutant_eq_of_vacuum τ ω hτ T 0 hT
  · intro b _; simp
  · simpa only [zero_apply] using hv

end TracialSequence

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RelativeSequenceRange
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

open HilbertSequence

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ) (j : B →⋆ₐ[ℂ] A)

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma relative_range_bicommutant (hω : (ω : Filter ℕ)≤atTop) :
    Set.centralizer (Set.centralizer (Set.range ((leftRestricted τ ω).comp (mapSequence j))))=
      Set.range ((leftRestricted τ ω).comp (mapSequence j)) := by
  exact BicommutantRange.operatorHom_range
    ((leftRestricted τ ω).comp (mapSequence j)) fun T hT hsT hnT =>
      let h := relative_bicommutant_contraction τ ω j hτ hω hT hsT hnT
      ⟨h.choose, h.choose_spec.2⟩

def relativeUltrapower (hω : (ω : Filter ℕ)≤atTop) : VonNeumannAlgebra (boundedSubspace τ ω) :=
  BicommutantRange.ofStarHom ((leftRestricted τ ω).comp (mapSequence j))
    (relative_range_bicommutant τ ω j hτ hω)

end Kadison.TracialSequence

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialVectorSubalgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexHeadSpace _root_.OAI.Kadison.FreeCreation.instIsClosedGNSFunctionalCoeSubmoduleComplexTailSpace _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder

namespace Kadison.TracialSequence

open TracialGNS FreeWordTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (hω : (ω : Filter ℕ)≤Filter.atTop)

variable (M : VonNeumannAlgebra (boundedSubspace τ ω))
  (hM : ∀ a : M,(a:boundedSubspace τ ω →L[ℂ] boundedSubspace τ ω) ∈
    Set.centralizer (Set.centralizer (Set.range (leftRestricted τ ω))))

include hτ hM in
lemma subalgebra_faithful (a : M)
    (ha : VectorGNS.subalgebraTrace M (sequenceVacuum τ ω) (star a*a)=0) : a=0 := by
  apply Subtype.ext
  exact trace_faithful τ ω hτ (hM a) ha

lemma subalgebra_normalized (hone : τ 1=1) :
    VectorGNS.subalgebraTrace M (sequenceVacuum τ ω) 1=1 :=
  (trace_one τ ω).trans hone

abbrev subalgebraState (hone : τ 1=1) : FaithfulState M where
  functional := VectorGNS.subalgebraTrace M (sequenceVacuum τ ω)
  normalized := subalgebra_normalized τ ω M hone
  faithful := subalgebra_faithful τ ω hτ M hM

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialGeneratedAlgebra
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TracialSequence

abbrev generatedFreeAlgebra {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)
    (D : VonNeumannAlgebra (boundedSubspace τ ω)) :
    VonNeumannAlgebra (boundedSubspace τ ω) :=
  GeneratedFreePair.algebra (H := boundedSubspace τ ω) (A := A) D (constantAction τ ω)

end Kadison.TracialSequence

end

end
end

end OAI
end


