-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_VVAlgebraMapNonneg
-- name    : Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_VVAlgebraMapNonneg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:38.378721+00:00
-- url     : https://prove2.me/theorems/8ec9853a-dcec-4914-ac73-2b2513bdef1b
-- title:
--   VVAlgebra Map Nonneg
-- statement:
--   Definitions and structural lemmas for VVAlgebra Map Nonneg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/LevelGroupExamples/VVAlgebraMapNonneg.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IntegralFrameCheck
open Formalism.L2.Pj NumberField IsDedekindDomain
open scoped WithZero
section Dvr
variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']
variable {V' K'' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K''] [Algebra V' K'']
  [IsFractionRing V' K'']
end Dvr
end GlobalTheory.IntegralFrameCheck


