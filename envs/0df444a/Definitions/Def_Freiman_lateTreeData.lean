-- Prove2me | Definitions.Def_Freiman_lateTreeData
-- name    : Freiman_lateTreeData
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:25:18.477117+00:00
-- url     : https://prove2.me/theorems/fdd8b811-d4da-4e73-a7d3-94aa9c676132
-- title:
--   Freiman late: lateTreeData
-- statement:
--   Exact source late decision catalogue, shared-kernel finite validator or actual-cover interface; no theorem/axiom declarations.
-- source:
--   Freiman report, §15, printed source pages 140–144; active lower_140_144.tex and Appendix Complete finite certificates for printed pages 140–144 (late_certificates.tex); exact late_readable_certificates.json with both original cover_*_certificate.json trees.

import Definitions.Def_Freiman_lateModel

set_option maxRecDepth 8000
set_option maxHeartbeats 0

namespace Freiman

def lateOtherTree : LateDecisionTree :=
  .cut 8 (.cut 11 (.cut 137 (.cut 14 (.cut 149 (.cut 12 (.cut 259 (.path 1) (.empty 50)) (.cut 194 (.path 2) (.cut 202 (.path 3) (.cut 145 (.path 4) (.path 5))))) (.cut 206 (.cut 265 (.path 6) (.cut 194 (.path 7) (.path 8))) (.cut 151 (.cut 259 (.path 9) (.split true (.empty 312) (.split true (.empty 313) (.split true (.empty 314) (.split true (.empty 315) (.split false (.empty 316) (.split true (.empty 317) (.split false (.empty 318) (.path 10))))))))) (.path 11)))) (.path 12)) (.path 13)) (.cut 43 (.cut 183 (.cut 237 (.path 14) (.path 15)) (.cut 237 (.path 16) (.path 17))) (.path 18))) (.cut 6 (.cut 43 (.cut 44 (.cut 144 (.cut 181 (.cut 190 (.cut 222 (.path 19) (.split true (.split true (.empty 606) (.path 20)) (.empty 627))) (.cut 222 (.cut 232 (.path 21) (.split true (.empty 639) (.path 22))) (.cut 7 (.path 23) (.split true (.split true (.empty 690) (.path 24)) (.empty 718))))) (.cut 59 (.cut 183 (.path 25) (.path 26)) (.cut 232 (.path 27) (.path 28)))) (.empty 783)) (.empty 786)) (.cut 144 (.cut 193 (.cut 328 (.path 29) (.cut 7 (.path 30) (.cut 191 (.cut 222 (.path 31) (.empty 814)) (.cut 190 (.cut 222 (.path 32) (.split true (.path 33) (.empty 849))) (.split true (.split true (.empty 850) (.split true (.cut 109 (.path 34) (.empty 883)) (.empty 890))) (.empty 891)))))) (.split true (.split true (.split true (.path 35) (.empty 926)) (.empty 927)) (.empty 928))) (.split true (.split true (.empty 929) (.split true (.empty 930) (.path 36))) (.empty 785)))) (.cut 43 (.cut 44 (.cut 144 (.path 37) (.path 38)) (.cut 197 (.cut 257 (.path 39) (.empty 967)) (.cut 257 (.path 40) (.empty 978)))) (.cut 197 (.cut 257 (.cut 328 (.path 41) (.split true (.empty 984) (.split true (.empty 985) (.split true (.empty 986) (.split true (.empty 987) (.split false (.empty 988) (.split true (.empty 991) (.path 42)))))))) (.cut 328 (.path 43) (.empty 1008))) (.split true (.empty 1011) (.cut 44 (.cut 144 (.path 44) (.split true (.empty 1036) (.path 45))) (.cut 9 (.cut 144 (.path 46) (.path 47)) (.cut 257 (.path 48) (.path 49))))))))

def lateRight3Tree : LateDecisionTree :=
  .cut 11 (.cut 14 (.cut 149 (.cut 12 (.path 50) (.cut 194 (.path 51) (.path 52))) (.path 53)) (.cut 185 (.path 54) (.path 55))) (.cut 7 (.cut 43 (.cut 8 (.path 56) (.path 57)) (.cut 44 (.cut 237 (.cut 195 (.path 58) (.path 59)) (.path 60)) (.path 61))) (.cut 328 (.path 62) (.path 63)))

end Freiman


