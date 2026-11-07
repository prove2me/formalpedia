-- Prove2me | Definitions.Def_KarpLiptonOM_gateCode
-- name    : KarpLiptonOM_gateCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:39:23.703777+00:00
-- url     : https://prove2.me/theorems/61ac352a-b5fa-479a-85f9-fa3d8c689055
-- title:
--   Code of a gate in the fixed circuit encoding
-- statement:
--   In the fixed circuit encoding each gate occupies a slot of $3 + 2b$ bits: a presence bit $1$, two bits for the gate type (constant, NOT, AND, OR), and two fields of $b$ bits holding the binary codes of the wires read (for a constant, its value; unused fields are $0$).
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), §A.2.1, p.20 (fixed encoding of circuits)

import Mathlib
import Definitions.Def_KarpLiptonOM_Gate
import Definitions.Def_KarpLiptonOM_binW

namespace KarpLiptonOM

/-- The code of one gate in the fixed circuit encoding (Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b), §A.2.1, p.20): a presence bit `1`,
two type bits (`00` constant, `01` NOT, `10` AND, `11` OR) and two wire fields of `b` bits each
(the constant's value in the first field; unused fields `0`). Length `3 + 2b`. -/
def gateCode (b : ℕ) : Gate → List Bool
  | .const c => [true, false, false] ++ binW b (if c then 1 else 0) ++ binW b 0
  | .not i => [true, false, true] ++ binW b i ++ binW b 0
  | .and i j => [true, true, false] ++ binW b i ++ binW b j
  | .or i j => [true, true, true] ++ binW b i ++ binW b j

end KarpLiptonOM


