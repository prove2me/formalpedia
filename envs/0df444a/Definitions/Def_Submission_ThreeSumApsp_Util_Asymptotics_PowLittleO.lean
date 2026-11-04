-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
-- name    : Submission_ThreeSumApsp_Util_Asymptotics_PowLittleO
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:01:18.795187+00:00
-- url     : https://prove2.me/theorems/fe5f0b5d-56e4-481b-abc5-7f1226e3f7ce
-- title:
--   Pow Little O
-- statement:
--   Definitions and structural lemmas for Pow Little O, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Util/Asymptotics/PowLittleO.lean

import Definitions.Def_Submission_ThreeSumApsp_Util_Asymptotics_PowPolylog
set_option autoImplicit false
section
@[expose] section
open Filter Asymptotics
namespace ThreeSumApsp
variable {f g T : ℕ → ℝ} {size : ℕ → ℕ} {a b c d η : ℝ}
end ThreeSumApsp


