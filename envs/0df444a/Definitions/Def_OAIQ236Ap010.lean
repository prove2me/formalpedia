-- Prove2me | Definitions.Def_OAIQ236Ap010
-- name    : OAIQ236Ap010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-10T19:54:53.658411+00:00
-- url     : https://prove2.me/theorems/be7acff5-c926-4bbc-aeab-f41e5f202838
-- title:
--   Definitions bundle OAIQ236Ap010 of the split of OpenAI, Parabolic intersections in Artin groups
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1 declaration of OpenAI's Lean: 1 definition. The definitions and types are `OAI.HarmonicArtin.ParabolicIntersections.blockProjector`.
--
--   **Sources.** They come from these modules of lean/OAI/Topology, in whole or in part: [`ArtinGroups_ParabolicIntersections_ConnectedSupport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/ConnectedSupport.lean).
--
--   **Imports.** It imports the bundles `OAIQ236Ap005` and `OAIQ236Ap007` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI_HarmonicArtin_ParabolicIntersections_exists_minimal_parabolic`, `OAI.HarmonicArtin.ParabolicIntersections.exists_minimal_parabolic_s236`, `OAI_HarmonicArtin_ParabolicIntersections_relative_descending_lower_connected`, `OAI.HarmonicArtin.ParabolicIntersections.relative_descending_lower_connected_s236`, `OAI_HarmonicArtin_ParabolicIntersections_spherical_reduction`, `OAI.HarmonicArtin.ParabolicIntersections.spherical_reduction_s236`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Topology at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ236Ap005
import Definitions.Def_OAIQ236Ap007

section
-- module Solutions.OAIQ236_AP.ArtinGroups_ParabolicIntersections_ConnectedSupport
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.amplitudeCoreFintype _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreDecidable _root_.OAI.HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex.negativeAmplitudeCoreFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Connected support of transported indecomposable projectives

This proves the support-cut form of the connectedness assertion in
Proposition 2.7 of paper 082-03. The input is the dimension of the actual
endomorphism cohomology, rather than an assumed connectedness property.
-/

namespace HarmonicArtin.ParabolicIntersections

open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable

variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def blockProjector (E : BasedComplex Q (K := K) I) (T : Set I)
    (hT : BlockClosed Q E T) : Map Q E E :=
  (blockProjectionMap Q E T hT).comp Q (blockInclusionMap Q E T hT)

end HarmonicArtin.ParabolicIntersections

end OAI
end


