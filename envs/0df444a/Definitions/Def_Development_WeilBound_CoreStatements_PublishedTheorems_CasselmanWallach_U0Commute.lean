-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_U0Commute
-- name    : Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_U0Commute
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:56.380985+00:00
-- url     : https://prove2.me/theorems/2e8dc766-4f6f-442f-8ddf-f721225745e5
-- title:
--   U0 Commute
-- statement:
--   Definitions and structural lemmas for U0 Commute, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/U0Commute.lean

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UnitaryGroupStatement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ParabolicUnipotentGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
namespace PositivityTheory.CWB
open PositivityTheory.CW
namespace WordFiltrationCommute
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V)
abbrev wd (l : List (Fin n × Fin n)) : Module.End ℂ V := (l.map fun p => E p.1 p.2).prod
end WordFiltrationCommute
end PositivityTheory.CWB
end


