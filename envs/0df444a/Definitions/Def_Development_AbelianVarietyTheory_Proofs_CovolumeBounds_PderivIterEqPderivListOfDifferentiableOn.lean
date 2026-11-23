-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_PderivIterEqPderivListOfDifferentiableOn
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_PderivIterEqPderivListOfDifferentiableOn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:02.737001+00:00
-- url     : https://prove2.me/theorems/18d38546-a6a5-4762-912b-6dcb3b0c29c8
-- title:
--   Pderiv Iter Eq Pderiv List Of Differentiable On
-- statement:
--   Definitions and structural lemmas for Pderiv Iter Eq Pderiv List Of Differentiable On, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/PderivIterEqPderivListOfDifferentiableOn.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormPderivIterLeOfAnalyticAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace GlobalTheory
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
section Holomorphic
variable {F G : (ι → ℂ) → V} {U : Set (ι → ℂ)} {a : ι → ℂ}
end Holomorphic
end GlobalTheory


