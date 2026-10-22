-- Prove2me | Definitions.Def_HardyCapsetBinaryStorage20261020
-- name    : HardyCapsetBinaryStorage20261020
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-20T16:16:38.849231+00:00
-- url     : https://prove2.me/theorems/d5feb76c-d4b3-4fcc-adb2-7ed05831ac4e
-- title:
--   HardyCapsetBinaryStorage20261020
-- statement:
--   Natural-number bit packing of finite blocking witnesses, with explicit decoding and no asserted mathematical facts.
-- source:
--   Private source: 八维 cap 的超平面补点定理, 2026-10-13, sections 2–5. The exact baseline is the previously uploaded HardyCapsetModel20261020. This is a conditional fixed-core theorem for that baseline.

import Definitions.Def_HardyCapsetCertificateModel20261020
set_option autoImplicit false
namespace HardyCapset20261020.Cert

/-- Each natural-number literal stores 64 witness pairs in 21-bit slots. -/
def binaryPair (chunks : Array ℕ) (q : ℕ) : ℕ × ℕ :=
  let word := (entry chunks (q / 64) >>> (21 * (q % 64))) % 2097152
  (word / 512, word % 512)

def binaryBlockers (chunks : Array ℕ) : Array (ℕ × ℕ) :=
  Array.ofFn (fun q : Fin 6561 => binaryPair chunks q.val)

end HardyCapset20261020.Cert


