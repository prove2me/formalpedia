-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExpandByConductor
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExpandByConductor
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:07.360395+00:00
-- url     : https://prove2.me/theorems/184a4ef2-a384-44ed-b215-8269886e462f
-- title:
--   Expand By Conductor
-- statement:
--   Definitions and structural lemmas for Expand By Conductor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExpandByConductor.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.CharCond
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
noncomputable def rep (ϖ : 𝒪[F]) (j : ℕ) (x : 𝒪[F] ⧸ Ideal.span {ϖ ^ j}) : 𝒪[F] :=
  (Ideal.Quotient.mk_surjective x).choose
end GlobalTheory.HL.CharCond


