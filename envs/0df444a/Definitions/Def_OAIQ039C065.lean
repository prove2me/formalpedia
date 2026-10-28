-- Prove2me | Definitions.Def_OAIQ039C065
-- name    : OAIQ039C065
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:14:08.012926+00:00
-- url     : https://prove2.me/theorems/9d68c7f2-8df2-429d-a299-61187319b2c9
-- title:
--   Definitions bundle OAIQ039C065 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 5 definitions. The definitions and types are `OAI.Kadison.FreeBlocks.sourceConjugation`, `OAI.Kadison.TracialSequence.relativeVectorCLM`, `OAI.Kadison.VectorGNS.CornerCommutatorBound`, `OAI.Kadison.VectorGNS.RepresentedCornerBound`, `OAI.Kadison.VectorGNS.vectorState`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_FreeActualCovariance`, `Commutator_GNSCornerTransport`, `Commutator_RelativeSequenceRange`, `Commutator_RepresentedCornerBound`, `Commutator_TracialGNSCorners`.
--
--   **Imports.** It imports the bundles `OAIQ039C052`, `OAIQ039C054`, `OAIQ039C055` and `OAIQ039C056` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ039C069`; the statements `OAI.Kadison.FreeBlocks.sumConjugation_levelWord`, `OAI.Kadison.TracialSequence.represented_corner_bound`, `OAI.Kadison.VectorGNS.ambient_range`, `OAI.Kadison.VectorGNS.corner_bound`, `OAI.Kadison.VectorGNS.factorTrace_generated`, `OAI.Kadison.VectorGNS.factorTrace_inclusion_normal`, `OAI.Kadison.VectorGNS.free_original_bound`, `OAI.Kadison.VectorGNS.free_original_bound_represented` and `OAI.Kadison.VectorGNS.gns_generation`; the proofs of `OAI.Kadison.FreeBlocks.sumConjugation_levelWord`, `OAI.Kadison.VectorGNS.ambient_range`, `OAI.Kadison.VectorGNS.corner_bound`, `OAI.Kadison.VectorGNS.factorTrace_generated`, `OAI.Kadison.VectorGNS.factorTrace_inclusion_normal`, `OAI.Kadison.VectorGNS.free_original_bound`, `OAI.Kadison.VectorGNS.free_original_bound_represented` and `OAI.Kadison.VectorGNS.gns_generation`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ039C052
import Definitions.Def_OAIQ039C054
import Definitions.Def_OAIQ039C055
import Definitions.Def_OAIQ039C056

section
-- module Solutions.OAIQ039_CM.Commutator_FreeActualCovariance
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct

open UniformSpace

namespace Kadison.FreeBlocks

open FreeWordTensor FreeMoments FreeWordAction

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : Free S t.functional.toLinearMap)
  (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
    Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))

abbrev sourceConjugation (u : unitary D) (n : ℕ) :
    sourceLevel t f hf S j n →L[ℂ] sourceLevel t f hf S j n :=
  HilbertTensor.map
    (PreHilbert.wordMap (factorFull t f hf) (factorZero t f hf)
      (TracialGNS.conjugation (factorTrace t f hf) (factorTrace_tracial t f hf ht) u)
      (centeredIsometry (TracialGNS.vacuum (factorTrace t f hf))
        (TracialGNS.conjugation (factorTrace t f hf) (factorTrace_tracial t f hf ht) u)
        (TracialGNS.conjugation_vacuum (factorTrace t f hf)
          (factorTrace_tracial t f hf ht) u)) n).toContinuousLinearMap
    (1 : multiplicityLevel t S j n →L[ℂ] multiplicityLevel t S j n)

end Kadison.FreeBlocks

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_GNSCornerTransport
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
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

open ContinuousLinearMap

namespace Kadison.VectorGNS

open FreeWordTensor FreeMoments FreeWordAction FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (ξ : H)

variable (htr : ∀ a b : M,subalgebraTrace M ξ (a*b)=subalgebraTrace M ξ (b*a))
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

abbrev vectorState : FaithfulState M where
  functional := subalgebraTrace M ξ
  normalized := hone
  faithful := hfaith

end Kadison.VectorGNS

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

def relativeVectorCLM : B →L[ℂ] τ.GNS :=
  (vectorCLM τ).comp (j.toLinearMap.mkContinuous 1 (fun b => by
    change ‖j b‖≤1*‖b‖
    simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le j b))

end Kadison.TracialSequence

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialGNSCorners
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction

open Filter ContinuousLinearMap

namespace Kadison.VectorGNS

def CornerCommutatorBound
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ξ : H)
    (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
    (hone : subalgebraTrace M ξ 1=1)
    {D : Type} [CStarAlgebra D] (f : D →⋆ₐ[ℂ] M)
    (R : Bool → StarSubalgebra ℂ M) (T : H →L[ℂ] H) (c : ℝ) (β : ℂ) : Prop :=
  ∀ X,CornerSymmetrization.CornerElement
    (FreeBlocks.factorOperators (vectorState M ξ hfaith hone) f)
    (FreeBlocks.ambientOperators (vectorState M ξ hfaith hone) R)
    (TracialGNS.vacuum (subalgebraTrace M ξ)) β X →
    ‖subalgebraCompression M ξ T*X-X*subalgebraCompression M ξ T‖ ≤ c*‖X‖

end Kadison.VectorGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RepresentedCornerBound
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

open scoped InnerProductSpace ComplexOrder

namespace Kadison.VectorGNS

open FreeWordTensor FreeMoments FreeWordAction FreeBlocks

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (ξ : H)
  (htr : ∀ a b : M,subalgebraTrace M ξ (a*b)=subalgebraTrace M ξ (b*a))
  (hfaith : ∀ a : M,subalgebraTrace M ξ (star a*a)=0 → a=0)
  (hone : subalgebraTrace M ξ 1=1)

variable (D : VonNeumannAlgebra H) (hDM : D.toStarSubalgebra≤M.toStarSubalgebra)
  (R : Bool → StarSubalgebra ℂ M)

def RepresentedCornerBound (U : H →L[ℂ] H) (c : ℝ) (β : ℂ) : Prop :=
  ∀ q : D,IsStarProjection (q:H →L[ℂ] H) →
    subalgebraTrace D ξ q=β → ∀ a : M,
    (q:H →L[ℂ] H)*a*q=a →
    ‖U*(a:H →L[ℂ] H)-(a:H →L[ℂ] H)*U‖ ≤ c*‖a‖

end Kadison.VectorGNS

end

end
end

end OAI
end


