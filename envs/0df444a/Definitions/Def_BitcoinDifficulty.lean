-- Prove2me | Definitions.Def_BitcoinDifficulty
-- name    : BitcoinDifficulty
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T13:49:28.089991+00:00
-- url     : https://prove2.me/theorems/13c2746c-d8f4-41e7-be98-e5bb3c8ddb10
-- title:
--   The raw next target of a retarget period and the target after a sequence of periods
-- statement:
--   Two names over the proof-of-work mission's `BitcoinPow`; nothing is re-transcribed.
--
--   **`rawNextTarget t lastTime firstTime`** — the value `CalculateNextWorkRequired` encodes: the last target $t$ times the clamped actual timespan (`clampTimespan (lastTime − firstTime)`, between `targetTimespan/4` and `4·targetTimespan`), taken modulo $2^{256}$, divided by `targetTimespan` (1,209,600 s), and capped at `powLimit`. `calculateNextWork bits lastTime firstTime` is by definition `getCompact (rawNextTarget (setCompact bits) lastTime firstTime)`.
--
--   **`targetAfter bits periods`** — the encoded target after applying `calculateNextWork` once per element of `periods`, a list of (last time, first time) pairs, starting from `bits`.
--
--   **Formalization Note.** `setCompact`, `getCompact`, `clampTimespan`, `calculateNextWork`, `nextWorkRequired`, `powLimit`, `width` are the proof-of-work mission's; `ChainState.requiredBits` is the block mission's `GetNextWorkRequired` on a chain. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: CalculateNextWorkRequired, GetNextWorkRequired, src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact/GetCompact (arith_uint256.cpp); CMainParams (kernel/chainparams.cpp)

import Definitions.Def_BitcoinPow
import Definitions.Def_BitcoinBlockV2

/-!
# How fast the difficulty can move

`CalculateNextWorkRequired` multiplies the last target by the clamped actual timespan of the
period and divides by two weeks, caps at `powLimit`, and re-encodes. The clamp bounds the ratio
by a factor of four in either direction; this file names the raw (unencoded) next target so the
theorems can state that bound exactly, before the compact rounding, and then transfer it to the
encoded value and along a chain of periods. These are the limits on what an adversary who controls
timestamps can do to the difficulty: a "timewarp" moves the target by at most this much per period.
-/

namespace BitcoinDifficulty

open BitcoinPow

/-- The raw next target of a period: the last target times the clamped timespan, divided by the
target timespan, capped at `powLimit` — the value `CalculateNextWorkRequired` encodes. -/
def rawNextTarget (lastTarget : Nat) (lastTime firstTime : Int) : Nat :=
  let ts := (clampTimespan (lastTime - firstTime)).toNat
  let bn := (lastTarget * ts) % width / targetTimespan
  if powLimit < bn then powLimit else bn

/-- The encoded target after `m` retargets starting from `bits`, with the given sequence of
(last time, first time) pairs, one per period. -/
def targetAfter : BitVec 32 → List (Int × Int) → BitVec 32
  | bits, [] => bits
  | bits, (lastTime, firstTime) :: rest => targetAfter (calculateNextWork bits lastTime firstTime) rest

end BitcoinDifficulty


