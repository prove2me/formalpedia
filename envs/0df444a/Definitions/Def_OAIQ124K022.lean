-- Prove2me | Definitions.Def_OAIQ124K022
-- name    : OAIQ124K022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:13:21.405986+00:00
-- url     : https://prove2.me/theorems/bb4cce23-8db3-43ff-be14-8c8e31f72fe9
-- title:
--   Definitions bundle OAIQ124K022 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 2 declarations of OpenAI's Lean: 2 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: [`KazhdanLusztig_BalancedPairings`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/BalancedPairings.lean).
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`; the bundle `OAIQ124K020` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ124K024`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K020

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BalancedPairings
attribute [-instance] _root_.OAI.KLInvariance.BruhatGraph.edgeRing_ufm _root_.OAI.KLInvariance.TitsSpace.planePrime_isPrime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded stalk duality, integral perfect balanced all-sections pairings, recognition and top grading.
-/


section


namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
noncomputable section

 theorem bottAdjointSheaf_primitive
    (p : GradedSheaf.Hom
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l))
      (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
    (hp : p.PrimitiveProjector) :
    (bottAdjointSheaf cs basis l hl p).PrimitiveProjector :=
  GradedSheaf.Hom.primitive_of_antiInvolution _
    (bottAdjointSheaf_involutive cs basis l hl)
    (bottAdjointSheaf_comp cs basis l hl)
    (bottAdjointSheaf_zero cs basis l hl) p hp

end
end KLInvariance.TitsSpace

end


section

/-! For a supplied normalized boundary sheaf and an ACTUAL word splitting,
the adjoint image is primitively indecomposable. The splitting's existence
and the BMP axioms on that image still require word recognition. -/
namespace KLInvariance.TitsSpace
open Module _root_.OAI.KLInvariance.Graded MomentGraph BruhatGraph
universe u us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  (l : List I) (hl : cs.IsReduced l)
  (α : Edge cs 1 (cs.wordProd l) → SymmetricCoefficient (M := M))
  (B : BoundarySheaf (symmetricGrading_negative basis)
    (graph cs 1 (cs.wordProd l)) α
    ⟨cs.wordProd l,one_bruhat cs _,bruhat_refl cs _⟩)
  (s : GradedSheaf.SplitIn B.sheaf (bottGradedProjectionSheaf cs basis l 1 (cs.wordProd l)))
noncomputable section

 theorem bottBoundarySplitAdjoint_primitive :
    (GradedSheaf.Hom.id (bottSplitAdjointSheaf cs basis l hl B.sheaf s)).PrimitiveProjector := by
  let := symmetricCoefficientNoetherian basis
  let := interval_finite cs 1 (cs.wordProd l)
  exact GradedSheaf.Hom.primitive_image _ (bottAdjointSheaf_primitive cs basis l hl
    s.projector (B.split_projector_primitive s))

end
end KLInvariance.TitsSpace

end


end OAI
end


