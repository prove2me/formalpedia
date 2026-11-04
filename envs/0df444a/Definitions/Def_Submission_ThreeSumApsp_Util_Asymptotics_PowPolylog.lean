-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
-- name    : Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:57:32.367476+00:00
-- url     : https://prove2.me/theorems/728b682d-1e76-43d3-8b52-bf0a94fe5bbe
-- title:
--   Pow Polylog
-- statement:
--   Supporting definitions from the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowPolylog.lean

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Dominated
import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_Powers
import Definitions.Def_Submission_ThreeSumApsp_Util_Log
set_option autoImplicit false
section
@[expose] section
open Filter Asymptotics
namespace ThreeSumApsp
variable {f g : ℕ → ℝ} {a b : ℝ}
namespace IsBigOPow
end IsBigOPow
namespace IsPowPolylog
end IsPowPolylog
end ThreeSumApsp


