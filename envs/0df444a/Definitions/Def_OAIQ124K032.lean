-- Prove2me | Definitions.Def_OAIQ124K032
-- name    : OAIQ124K032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:12:58.934105+00:00
-- url     : https://prove2.me/theorems/b70fd843-ca67-4e1a-8ee2-99e23cdbbfed
-- title:
--   Definitions bundle OAIQ124K032 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean).
--
--   **Imports.** It imports the bundles `OAIQ124K025`, `OAIQ124K020` and `OAIQ124K031` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ124K033`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ124K025
import Definitions.Def_OAIQ124K020
import Definitions.Def_OAIQ124K031

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_IntegralPairings
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert recurrences, projective section ranges, integral lattices and graded perfect adjoints.
-/


section

namespace KLInvariance.TitsSpace
open Module CoordinateProjection ReflectionPairTranslation ProjectiveRange
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 abbrev bottInterKernelFirst (i : I) (l : List I) (U : Set W) :=
    onKernel (bottInterRestriction cs i (i::l) U) (bottSetFirst cs i l U)
      (bottInterRestriction cs i l U) (bottInter_first_zero cs i l U)

 theorem bottInterKernelFirst_surjective (i : I) (l : List I) (U : Set W) :
    Function.Surjective (bottInterKernelFirst cs i l U) := by
  intro z
  let n : BottSamelsonModule cs l := (bottSetProjection_surjective cs l U z.val).choose
  have hn : bottSetProjection cs l U n=z.val := (bottSetProjection_surjective cs l U z.val).choose_spec
  have hnJ : bottSetProjection cs l (simpleInter cs i U) n=0 :=
    (congrArg (bottInterRestriction cs i l U) hn).trans z.property
  let w : LinearMap.ker (bottInterRestriction cs i (i::l) U) :=
    ⟨bottSetProjection cs (i::l) U (bottSeed cs i l n),
      bottSeed_zero_stable cs i l (simpleInter cs i U) (simpleInter_stable cs i U) n hnJ⟩
  exact ⟨w,Subtype.ext ((bottSetFirst_seed cs i l U n).trans hn)⟩

end
end KLInvariance.TitsSpace

end


end OAI
end


