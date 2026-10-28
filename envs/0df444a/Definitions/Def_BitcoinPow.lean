-- Prove2me | Definitions.Def_BitcoinPow
-- name    : BitcoinPow
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-26T04:27:50.885563+00:00
-- url     : https://prove2.me/theorems/5d077a41-dea4-448f-a43b-559476c02bcf
-- title:
--   Compact targets, proof of work, and difficulty retargeting at mainnet parameters
-- statement:
--   This file transcribes the mainnet proof-of-work arithmetic of Bitcoin Core. An `arith_uint256` is modelled by its value, a natural number below $2^{256}$ (`width`); its left shift and its multiplications discard carries out of the top word, so they reduce modulo $2^{256}$, and its division is exact integer division.
--
--   **Parameters.** $\mathrm{powLimit} = 2^{224} - 1$, the target timespan $T = 14 \cdot 24 \cdot 60 \cdot 60 = 1{,}209{,}600$ seconds, the target spacing $600$ seconds, and the difficulty adjustment interval $T / 600 = 2016$ blocks.
--
--   **Compact words.** For a 32-bit word $c$: the size $S = \lfloor c / 2^{24} \rfloor$ and the mantissa $W = c \mathbin{\&} \mathtt{0x007fffff}$. `SetCompact` yields $\lfloor W / 2^{8(3-S)} \rfloor$ when $S \le 3$ and $(W \cdot 2^{8(S-3)}) \bmod 2^{256}$ otherwise. The word is **negative** when $W \ne 0$ and $c \mathbin{\&} \mathtt{0x00800000} \ne 0$; it **overflows** when $W \ne 0$ and ($S > 34$, or $W > \mathtt{0xff}$ and $S > 33$, or $W > \mathtt{0xffff}$ and $S > 32$). The **exact value** $\mathrm{specTarget}(c)$ is the same formula without the reduction modulo $2^{256}$.
--
--   **Encoding.** `bitLength` is $0$ at $0$ and $\lfloor \log_2 v \rfloor + 1$ otherwise. `GetCompact` of $v$ sets $S = \lfloor (\mathrm{bitLength}(v) + 7) / 8 \rfloor$, forms the mantissa as $((v \bmod 2^{64}) \cdot 2^{8(3-S)}) \bmod 2^{32}$ when $S \le 3$ and as $((\lfloor v / 2^{8(S-3)} \rfloor \bmod 2^{64}) \bmod 2^{32})$ otherwise; if bit 23 of the mantissa is set it divides the mantissa by $256$ and increments $S$; the result is the 32-bit word mantissa $\lor (S \cdot 2^{24})$.
--
--   **Validation.** `deriveTarget` returns the decoded value unless the word is negative, decodes to $0$, overflows, or exceeds $\mathrm{powLimit}$. `checkProofOfWork`(hash, word) holds when a target is derived and $\mathrm{hash} \le$ target. `clampTimespan` raises a signed timespan to $T/4$ and lowers it to $4T$. `calculateNextWork`(last word, last time, first time) decodes the last word, multiplies by the clamped elapsed time modulo $2^{256}$, divides by $T$, caps at $\mathrm{powLimit}$, and re-encodes. `permittedTransition`(height, old, new) at a height divisible by $2016$ requires the decoded new word to lie between the re-encoded caps of old $\cdot (T/4) / T$ and old $\cdot 4T / T$ (products modulo $2^{256}$); at other heights it requires old $=$ new. `nextWorkRequired` returns the last word unless the next height is divisible by $2016$, in which case it retargets.
--
--   These definitions fix the meaning of `nBits` on the wire and the retarget rule, as inputs for header validation.
--
--   **Formalization Note.** Compact words are `BitVec 32` read through `toNat`; values are `Nat`; block times are `Int`, converted with `Int.toNat` only after clamping. `fPowAllowMinDifficultyBlocks`, `fPowNoRetargeting`, and `enforce_BIP94` are fixed to `false` as on mainnet. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetNextWorkRequired (lines 14-48), CalculateNextWorkRequired (50-85), PermittedDifficultyTransition (89-136), DeriveTarget (146-159), CheckProofOfWorkImpl (161-171), src/pow.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/pow.cpp; arith_uint256::SetCompact (176-194), GetCompact (196-216), base_uint::operator<<= (15-30), operator*=(uint32_t) (49-59), operator/= (77-104), bits() (205-218), src/arith_uint256.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/arith_uint256.cpp; CMainParams powLimit, nPowTargetTimespan, nPowTargetSpacing, fPowAllowMinDifficultyBlocks, fPowNoRetargeting, enforce_BIP94, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Std

namespace BitcoinPow

/-! Transcription of the mainnet proof-of-work arithmetic of Bitcoin Core at revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`: `arith_uint256::SetCompact` / `GetCompact`
(`arith_uint256.cpp`), and `DeriveTarget`, `CheckProofOfWorkImpl`, `CalculateNextWorkRequired`,
`PermittedDifficultyTransition`, `GetNextWorkRequired` (`pow.cpp`), with `CMainParams`
(`kernel/chainparams.cpp`): `fPowAllowMinDifficultyBlocks = false`, `fPowNoRetargeting = false`,
`enforce_BIP94 = false`.

An `arith_uint256` is modelled by its value, a natural number below `2 ^ 256`. Its left shift and
its multiplications discard carries out of the top word, i.e. they reduce modulo `2 ^ 256`; its
division is exact integer division. -/

/-- `2 ^ 256`, the modulus of `arith_uint256` arithmetic. -/
def width : Nat := 2 ^ 256

/-- `consensus.powLimit = uint256{"00000000ffff…ff"}`: `2 ^ 224 - 1`. -/
def powLimit : Nat := 2 ^ 224 - 1

/-- `consensus.nPowTargetTimespan = 14 * 24 * 60 * 60`. -/
def targetTimespan : Nat := 14 * 24 * 60 * 60

/-- `consensus.nPowTargetSpacing = 10 * 60`. -/
def targetSpacing : Nat := 10 * 60

/-- `Consensus::Params::DifficultyAdjustmentInterval() = nPowTargetTimespan / nPowTargetSpacing`. -/
def difficultyAdjustmentInterval : Nat := targetTimespan / targetSpacing

/-- `int nSize = nCompact >> 24`. -/
def compactSize (c : BitVec 32) : Nat := (c >>> 24).toNat

/-- `uint32_t nWord = nCompact & 0x007fffff`. -/
def compactWord (c : BitVec 32) : Nat := (c &&& 0x007fffff).toNat

/-- The value produced by `SetCompact`: the mantissa shifted right by `8 * (3 - nSize)` bytes when
`nSize <= 3`, otherwise shifted left by `8 * (nSize - 3)` bytes inside 256 bits. -/
def setCompact (c : BitVec 32) : Nat :=
  let nSize := compactSize c
  let nWord := compactWord c
  if nSize ≤ 3 then nWord >>> (8 * (3 - nSize)) else (nWord <<< (8 * (nSize - 3))) % width

/-- `*pfNegative = nWord != 0 && (nCompact & 0x00800000) != 0`. -/
def compactNegative (c : BitVec 32) : Bool :=
  compactWord c != 0 && (c &&& 0x00800000) != 0

/-- `*pfOverflow = nWord != 0 && ((nSize > 34) || (nWord > 0xff && nSize > 33) || (nWord > 0xffff && nSize > 32))`. -/
def compactOverflow (c : BitVec 32) : Bool :=
  let nSize := compactSize c
  let nWord := compactWord c
  nWord != 0 && (decide (34 < nSize) || (decide (0xff < nWord) && decide (33 < nSize)) ||
    (decide (0xffff < nWord) && decide (32 < nSize)))

/-- The exact mathematical value `mantissa * 256 ^ (nSize - 3)` encoded by a compact word, with no
256-bit truncation (and floor division for `nSize <= 3`). -/
def specTarget (c : BitVec 32) : Nat :=
  let nSize := compactSize c
  let nWord := compactWord c
  if nSize ≤ 3 then nWord / 256 ^ (3 - nSize) else nWord * 256 ^ (nSize - 3)

/-- `base_uint::bits()`: the bit length, `0` for `0`. -/
def bitLength (v : Nat) : Nat := if v = 0 then 0 else Nat.log2 v + 1

/-- `GetCompact(fNegative = false)` on a value below `2 ^ 256`. `GetLow64()` is the value modulo
`2 ^ 64`; the assignment to the `uint32_t nCompact` reduces modulo `2 ^ 32`; when bit `0x00800000`
of the mantissa is set, the mantissa is divided by 256 and the exponent incremented. -/
def getCompact (v : Nat) : BitVec 32 :=
  let nSize := (bitLength v + 7) / 8
  let nCompact :=
    if nSize ≤ 3 then ((v % 2 ^ 64) <<< (8 * (3 - nSize))) % 2 ^ 32
    else ((v >>> (8 * (nSize - 3))) % 2 ^ 64) % 2 ^ 32
  let adjust := nCompact &&& 0x00800000 != 0
  let nCompact' := if adjust then nCompact >>> 8 else nCompact
  let nSize' := if adjust then nSize + 1 else nSize
  BitVec.ofNat 32 (nCompact' ||| (nSize' <<< 24))

/-- `DeriveTarget`: the target, unless negative, zero, overflowing, or above `powLimit`. -/
def deriveTarget (nBits : BitVec 32) : Option Nat :=
  let t := setCompact nBits
  if compactNegative nBits || decide (t = 0) || compactOverflow nBits || decide (powLimit < t) then none
  else some t

/-- `CheckProofOfWorkImpl`: the header hash, read as a 256-bit number, is at most the derived target. -/
def checkProofOfWork (hash : Nat) (nBits : BitVec 32) : Bool :=
  match deriveTarget nBits with
  | none => false
  | some t => decide (hash ≤ t)

/-- The timespan clamp of `CalculateNextWorkRequired`: `nActualTimespan` (a signed difference of
block times) is raised to `nPowTargetTimespan / 4` and lowered to `nPowTargetTimespan * 4`. -/
def clampTimespan (actual : Int) : Int :=
  let lo : Int := (targetTimespan / 4 : Nat)
  let hi : Int := (targetTimespan * 4 : Nat)
  if actual < lo then lo else if hi < actual then hi else actual

/-- `CalculateNextWorkRequired(pindexLast, nFirstBlockTime)` at mainnet parameters: decode the last
target, multiply by the clamped timespan (modulo `2 ^ 256`), divide by the target timespan, cap at
`powLimit`, and re-encode. -/
def calculateNextWork (lastBits : BitVec 32) (lastTime firstTime : Int) : BitVec 32 :=
  let ts := (clampTimespan (lastTime - firstTime)).toNat
  let bn := (setCompact lastBits * ts) % width
  let bn := bn / targetTimespan
  let bn := if powLimit < bn then powLimit else bn
  getCompact bn

/-- `PermittedDifficultyTransition(params, height, old_nbits, new_nbits)` at mainnet parameters. -/
def permittedTransition (height : Nat) (oldBits newBits : BitVec 32) : Bool :=
  if height % difficultyAdjustmentInterval = 0 then
    let observed := setCompact newBits
    let largest := (setCompact oldBits * (targetTimespan * 4)) % width / targetTimespan
    let largest := if powLimit < largest then powLimit else largest
    let maximum := setCompact (getCompact largest)
    let smallest := (setCompact oldBits * (targetTimespan / 4)) % width / targetTimespan
    let smallest := if powLimit < smallest then powLimit else smallest
    let minimum := setCompact (getCompact smallest)
    !(decide (maximum < observed)) && !(decide (minimum > observed))
  else
    decide (oldBits = newBits)

/-- `GetNextWorkRequired` at mainnet parameters, with the first block time of the period supplied
by the caller. -/
def nextWorkRequired (lastHeight : Nat) (lastBits : BitVec 32) (lastTime firstTime : Int) : BitVec 32 :=
  if (lastHeight + 1) % difficultyAdjustmentInterval ≠ 0 then lastBits
  else calculateNextWork lastBits lastTime firstTime

end BitcoinPow


