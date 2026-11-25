-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_LevelFamily
-- name    : Development_AutomorphicArithmetic_PrimitiveCosets_LevelFamily
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:35:49.884256+00:00
-- url     : https://prove2.me/theorems/7144363d-3203-4c25-b1b0-039a9f3d53e5
-- title:
--   Level Family
-- statement:
--   Definitions and structural lemmas for Level Family, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/LevelFamily.lean

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_GChiEq
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_GzEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost
open Classical in
noncomputable def UpperTheory.Comparison₂.level_family_wt (Λ : Level) (ψ : PChar) : ℝ :=
  if ψ = PChar.one then 1 else Λ.wt ψ


