-- Prove2me | Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
-- name    : D1Bound5_PairLightArithmeticChunks_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-24T02:36:11.222424+00:00
-- url     : https://prove2.me/theorems/8769fdff-93fc-4032-b5c0-1dbb3a2b63bb
-- title:
--   Pair Light Arithmetic Chunks
-- statement:
--   Check at most n complete head rows. Every selected head is checked against its entire remaining tail, including vertices beyond the cut. This computation-only module retains the Init-only import closure. The named objects in this bundle include `pairLightSelectedFloorPrefixBool`.
-- source:
--   D1Bound5/PairLightArithmeticChunks.lean, lines 5-15, SHA-256 f6567fcbc7792894e8607b67148594c393fe089550470cc632f4beffbdcfaca7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions

section
namespace D1Bound5

/-- Check at most n complete head rows. Every selected head is checked
against its entire remaining tail, including vertices beyond the cut.
This computation-only module retains the Init-only import closure. -/
def pairLightSelectedFloorPrefixBool (tau nu : Int) (sieve : List (Nat × Nat)) :
    Nat → List PairLightCachedVertex → List (Nat × List Nat) → Bool
  | 0, _, _ => true
  | _ + 1, [], [] => true
  | n + 1, x :: xs, (code, ks) :: rows =>
      pairLightSelectedFloorRowBool tau nu sieve x xs code ks &&
        pairLightSelectedFloorPrefixBool tau nu sieve n xs rows
  | _ + 1, _, _ => false

end D1Bound5
end


