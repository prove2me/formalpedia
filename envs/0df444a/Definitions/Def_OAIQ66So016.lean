-- Prove2me | Definitions.Def_OAIQ66So016
-- name    : OAIQ66So016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T02:12:50.642553+00:00
-- url     : https://prove2.me/theorems/e09ac523-f114-4df7-bf74-c49f13d91fb7
-- title:
--   Definitions bundle OAIQ66So016 of the split of OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SimpleFInftyOvergroups.main`, carved from OpenAI's openai/math development (OpenAI, *Simple F-infinity overgroups of groups with decidable word problem (OpenAI result)*, OpenAI Math Release, September 23, 2026, result family 250, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 3 declarations of OpenAI's Lean: 3 instances.
--
--   **Sources.** They come from these modules of lean/OAI/GroupTheory, in whole or in part: [`FiniteType_ProductGroupHomology`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/FiniteType/ProductGroupHomology.lean).
--
--   **Imports.** It imports the bundle `OAIQ66So008` of this split.
--
--   **Imported by** (directly, in this split): the proofs of `OAI.StageGeometry.simple_geometric_overgroup_of_binary_ring_data`, `OAI.TwistedBrin.Basis.CutBasis.localGroup_finitelyPresented`, `OAI.TwistedBrin.Basis.CutBasis.localGroup_geometric_of_certificates` and `OAI.TwistedBrin.Basis.CutBasis.sublevel_cocycle_trivial`.
-- source:
--   OpenAI, Simple F-infinity overgroups of groups with decidable word problem (OpenAI result), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/SimpleOvergroups.lean; Apache License 2.0); definitions carved from lean/OAI/GroupTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ66So008

section
-- module Solutions.OAIQ066_SO.FiniteType_ProductGroupHomology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory CategoryTheory.Limits _root_.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
namespace ProductGroupHomology
open _root_.CategoryTheory CategoryTheory.Limits
attribute [-instance] AddCommGroup.toIntModule
end ProductGroupHomology

open Set Function
open scoped Pointwise

universe u v
namespace TwistedBrin
instance instTopologicalSpaceCantor : TopologicalSpace Cantor := inferInstanceAs (TopologicalSpace (ℕ → Bool))
instance instCompactSpaceCantor : CompactSpace Cantor := inferInstanceAs (CompactSpace (ℕ → Bool))
instance instT2SpaceCantor : T2Space Cantor := inferInstanceAs (T2Space (ℕ → Bool))

end TwistedBrin

end

end OAI
end


