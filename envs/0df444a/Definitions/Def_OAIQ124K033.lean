-- Prove2me | Definitions.Def_OAIQ124K033
-- name    : OAIQ124K033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:54:15.387307+00:00
-- url     : https://prove2.me/theorems/b5b068af-4e8e-4197-810f-e5216ad51b00
-- title:
--   Definitions bundle OAIQ124K033 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 theorem.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_IntegralPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/IntegralPairings.lean).
--
--   **Imports.** It imports the bundles `OAIQ124K030` and `OAIQ124K032` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ124K024`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ124K030
import Definitions.Def_OAIQ124K032

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

 theorem bottProjectiveUpper_cons (i : I) (l : List I) (HP : BottProjectiveUpper cs l)
    (HF : BottFlabby cs l) : BottProjectiveUpper cs (i::l) := by
  intro U hU
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l U) := HP U hU
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs l (simpleInter cs i U)) :=
    HP (simpleInter cs i U) (hU.simpleInter cs U i)
  let : Module.Projective (SymmetricCoefficient (M := M)) (bottSetImage cs (i::l) (simpleInter cs i U)) :=
    bottStableUpper_projective cs i l (simpleInter cs i U) (simpleInter_stable cs i U)
  let : Module.Projective (SymmetricCoefficient (M := M)) (LinearMap.ker (bottInterRestriction cs i l U)) :=
    kernel_projective (bottInterRestriction cs i l U) (bottSetRestrict_surjective cs l (fun _ h => h.1))
  let : Module.Projective (SymmetricCoefficient (M := M))
      ↥(LinearMap.ker (bottInterRestriction cs i (i::l) U) ⊓ LinearMap.ker (bottSetFirst cs i l U)) :=
    bottCommon_projective cs i l HP HF U hU
  exact projective_of_two_stage (bottInterRestriction cs i (i::l) U) (bottSetFirst cs i l U)
    (bottInterRestriction cs i l U) (bottInter_first_zero cs i l U)
    (bottSetRestrict_surjective cs (i::l) (fun _ h => h.1)) (bottInterKernelFirst_surjective cs i l U)

end
end KLInvariance.TitsSpace

end


end OAI
end


