-- Prove2me | Definitions.Def_Freiman_lowerEarlyTerminalGoalsEarly3
-- name    : Freiman_lowerEarlyTerminalGoalsEarly3
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:29:04.655819+00:00
-- url     : https://prove2.me/theorems/8caf668c-c69f-4041-9c40-764aeceecf10
-- title:
--   Freiman.lowerEarlyTerminalGoalsEarly3
-- statement:
--   Typed, losslessly transcribed GoalsEarly3 data: exact source goal specifications, conflicting bound pairs or source residual records, with range-checked references. Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/residual_geometry_certificate.json:487 records.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/residual_geometry_certificate.json:487 records. Lean module: Definitions.Def_Freiman_lowerEarlyTerminalGoalsEarly3.

import Definitions.Def_Freiman_lowerEarlyTerminalBounds
set_option maxRecDepth 65536
namespace Freiman
def lowerEarlyTerminalGoalsEarly3 : List LowerEarlyTerminalGoal := [
⟨[1,2,3,4], .compare ([2,2],[3,1,1]) true ([2,2],[3,1,1]) false false⟩,
⟨[1,2,3,4,5], .compare ([2,2,1],[3,1,1]) true ([2,2,2],[3,1,1]) false true⟩,
⟨[1,2,3,4,5], .compare ([2,2,2],[3,1,1]) true ([2,2,1],[3,1,1]) false true⟩,
⟨[1,2,27,3,4], .compare ([2,2],[3,1,1,1]) true ([2,2],[3,1,1,2]) false true⟩,
⟨[1,2,27,3,4], .compare ([2,2],[3,1,1,2]) true ([2,2],[3,1,1,1]) false true⟩,
⟨[1,2,3,4], .compare ([2,2],[3,2]) true ([2,2],[3,2]) false false⟩,
⟨[1,2,3,4,49], .compare ([2,2,1],[3,2]) true ([2,2,2],[3,2]) false true⟩,
⟨[1,2,3,4,49], .compare ([2,2,2],[3,2]) true ([2,2,1],[3,2]) false true⟩,
⟨[1,2,75,3,4], .compare ([2,2],[3,2,1]) true ([2,2],[3,2,2]) false true⟩,
⟨[1,2,75,3,4], .compare ([2,2],[3,2,2]) true ([2,2],[3,2,1]) false true⟩,
⟨[1,2,3,4], .compare ([3],[2]) true ([2,2],[3,1,1]) false false⟩,
⟨[1,2,3,4], .compare ([2,2],[3,1,1]) true ([3],[2]) false false⟩,
⟨[1,2,3,4], .compare ([2,2],[3,1,1]) true ([2,2],[3,2]) false false⟩,
⟨[1,2,3,4], .compare ([2,2],[3,2]) true ([2,2],[3,1,1]) false false⟩,
⟨[1,2,3,4], .compare ([2,2],[3,2]) true ([2],[2]) false false⟩,
⟨[1,2,3,4], .compare ([2],[2]) true ([2,2],[3,2]) false false⟩,
⟨[1,159,3,4,160], .compare ([2,1,1],[3,1,1]) true ([2,1,1],[3,1,1]) false false⟩,
⟨[1,159,3,4,161,160], .compare ([2,1,1,1],[3,1,1]) true ([2,1,1,2],[3,1,1]) false true⟩,
⟨[1,159,3,4,161,160], .compare ([2,1,1,2],[3,1,1]) true ([2,1,1,1],[3,1,1]) false true⟩,
⟨[1,159,187,3,4,160], .compare ([2,1,1],[3,1,1,1]) true ([2,1,1],[3,1,1,2]) false true⟩,
⟨[1,159,187,3,4,160], .compare ([2,1,1],[3,1,1,2]) true ([2,1,1],[3,1,1,1]) false true⟩,
⟨[1,159,3,4,160], .compare ([2,1,1],[3,2]) true ([2,1,1],[3,2]) false false⟩,
⟨[1,159,3,4,213,160], .compare ([2,1,1,1],[3,2]) true ([2,1,1,2],[3,2]) false true⟩,
⟨[1,159,3,4,213,160], .compare ([2,1,1,2],[3,2]) true ([2,1,1,1],[3,2]) false true⟩,
⟨[1,159,235,3,4,160], .compare ([2,1,1],[3,2,1]) true ([2,1,1],[3,2,2]) false true⟩,
⟨[1,159,235,3,4,160], .compare ([2,1,1],[3,2,2]) true ([2,1,1],[3,2,1]) false true⟩,
⟨[1,159,3,4,160], .compare ([2,1,1,2],[3,3]) true ([2,1,1,2],[3,3]) false false⟩,
⟨[1,159,257,3,4,160], .compare ([2,1,1,2,1],[3,3]) true ([2,1,1,2,2],[3,3]) false true⟩,
⟨[1,159,257,3,4,160], .compare ([2,1,1,2,2],[3,3]) true ([2,1,1,2,1],[3,3]) false true⟩,
⟨[1,159,271,3,4,160], .compare ([2,1,1,2],[3,3,1]) true ([2,1,1,2],[3,3,2]) false true⟩,
⟨[1,159,271,3,4,160], .compare ([2,1,1,2],[3,3,2]) true ([2,1,1,2],[3,3,1]) false true⟩,
⟨[1,159,3,4,160], .compare ([2,1,1,3],[3,3]) true ([2,1,1,3],[3,3]) false false⟩,
⟨[1,159,297,3,4,160], .compare ([2,1,1,3,1],[3,3]) true ([2,1,1,3,2],[3,3]) false true⟩,
⟨[1,159,297,3,4,160], .compare ([2,1,1,3,2],[3,3]) true ([2,1,1,3,1],[3,3]) false true⟩,
⟨[1,159,311,3,4,160], .compare ([2,1,1,3],[3,3,1]) true ([2,1,1,3],[3,3,2]) false true⟩,
⟨[1,159,311,3,4,160], .compare ([2,1,1,3],[3,3,2]) true ([2,1,1,3],[3,3,1]) false true⟩,
⟨[1,159,3,4,160], .compare ([2,2],[3,1,1]) true ([2,2],[3,1,1]) false false⟩,
⟨[1,159,3,4,5,160], .compare ([2,2,1],[3,1,1]) true ([2,2,2],[3,1,1]) false true⟩,
⟨[1,159,3,4,5,160], .compare ([2,2,2],[3,1,1]) true ([2,2,1],[3,1,1]) false true⟩,
⟨[1,159,27,3,4,160], .compare ([2,2],[3,1,1,1]) true ([2,2],[3,1,1,2]) false true⟩,
⟨[1,159,27,3,4,160], .compare ([2,2],[3,1,1,2]) true ([2,2],[3,1,1,1]) false true⟩,
⟨[1,159,3,4,160], .compare ([2,2],[3,2]) true ([2,2],[3,2]) false false⟩,
⟨[1,159,3,4,49,160], .compare ([2,2,1],[3,2]) true ([2,2,2],[3,2]) false true⟩,
⟨[1,159,3,4,49,160], .compare ([2,2,2],[3,2]) true ([2,2,1],[3,2]) false true⟩,
⟨[1,159,75,3,4,160], .compare ([2,2],[3,2,1]) true ([2,2],[3,2,2]) false true⟩,
⟨[1,159,75,3,4,160], .compare ([2,2],[3,2,2]) true ([2,2],[3,2,1]) false true⟩,
⟨[1,159,3,4,160], .compare ([3],[2]) true ([2,1,1],[3,1,1]) false false⟩,
⟨[1,159,3,4,160], .compare ([2,1,1],[3,1,1]) true ([3],[2]) false false⟩,
⟨[1,159,3,4,160], .compare ([2,1,1],[3,1,1]) true ([2,1,1],[3,2]) false false⟩,
⟨[1,159,3,4,160], .compare ([2,1,1],[3,2]) true ([2,1,1],[3,1,1]) false false⟩,
⟨[1,159,3,4,160], .compare ([2,1,1],[3,2]) true ([2,1,1,2],[3,3]) false false⟩,
⟨[1,159,3,4,160], .compare ([2,1,1,2],[3,3]) true ([2,1,1],[3,2]) false false⟩,
⟨[1,159,3,4,160], .compare ([2,1,1,2],[3,3]) true ([2,1,1,3],[3,3]) false false⟩,
⟨[1,159,3,4,160], .compare ([2,1,1,3],[3,3]) true ([2,1,1,2],[3,3]) false false⟩,
⟨[1,159,3,4,160], .compare ([2,1,1,3],[3,3]) true ([2,2],[3,1,1]) false false⟩,
⟨[1,159,3,4,160], .compare ([2,2],[3,1,1]) true ([2,1,1,3],[3,3]) false false⟩,
⟨[1,159,3,4,160], .compare ([2,2],[3,1,1]) true ([2,2],[3,2]) false false⟩,
⟨[1,159,3,4,160], .compare ([2,2],[3,2]) true ([2,2],[3,1,1]) false false⟩,
⟨[1,159,3,4,160], .compare ([2,2],[3,2]) true ([2],[2]) false false⟩,
⟨[1,159,3,4,160], .compare ([2],[2]) true ([2,2],[3,2]) false false⟩]
end Freiman


