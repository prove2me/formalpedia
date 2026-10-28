-- Prove2me | Definitions.Def_BitcoinSig
-- name    : BitcoinSig
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-26T14:18:50.641178+00:00
-- url     : https://prove2.me/theorems/5b61bbdb-2d01-4608-a443-d0e28740a23b
-- title:
--   Signature encodings, signature hashes, secp256k1 ECDSA and Schnorr verification, and the transaction signature checker
-- statement:
--   **secp256k1.** $p = 2^{256} - 2^{32} - 977$, the order $n$, the generator $G$; `powMod` is square-and-multiply with explicit fuel, `finv`/`ninv` are Fermat inverses; a `Point` is an affine pair or infinity; `padd` is affine addition with the doubling and inverse cases; `pmul` is double-and-add. `liftXParity` is `secp256k1_ge_set_xo_var` (square root by $(p+1)/4$, parity selection); `parsePubkey` is `secp256k1_eckey_pubkey_parse` (33-byte `02`/`03`, 65-byte `04`/`06`/`07` with coordinates below $p$, on-curve and, for hybrid, parity check); `pubkeyValid` is `CPubKey::IsValid` (the header byte announces the length). `isHighS` is $s > n/2$, `normalizeS` replaces a high $s$ by $n - s$.
--
--   **Signatures.** `parseDerLax` is `ecdsa_signature_parse_der_lax` with its exact control flow: `none` where it returns $0$ (missing tags, length overruns, a long-form length of 4 or more significant bytes), `some (0,0)` where an integer has more than 32 significant bytes or a value at or above $n$ (the "correctly parsed but invalid" signature), trailing bytes ignored. `ecdsaVerifyRaw` is `secp256k1_ecdsa_sig_verify`: $r, s \in [1, n)$, $u_1 = e s^{-1}$, $u_2 = r s^{-1}$, $R = u_1 G + u_2 Q \ne \infty$ and $R_x \bmod n = r$. `pubkeyVerify` is `CPubKey::Verify`: valid and parsable key, lax-parsed signature, $s$ normalized, message reduced modulo $n$. `checkLowS` is `CPubKey::CheckLowS`. `schnorrVerify` is BIP340 / `secp256k1_schnorrsig_verify` with `taggedHash`.
--
--   **Byte-level scripts.** `getOp` is `GetScriptOp` (direct pushes, `PUSHDATA1/2/4`, `none` on a truncated push); `parseScript` parses a whole script; `pushBytes` is `CScript() << vch`; `findAndDelete` is `FindAndDelete` (occurrences removed at instruction boundaries, count returned); `serScriptCode` is `SerializeScriptCode` (`OP_CODESEPARATOR`s dropped, length-prefixed).
--
--   **Signature hashes.** `serSigTx` is `CTransactionSignatureSerializer` (`ANYONECANPAY` keeps only the signed input, other inputs' scripts blanked, their sequences zeroed under `SINGLE`/`NONE`, outputs truncated under `SINGLE`, dropped under `NONE`); `sigHashLegacy` is `SignatureHash` for `SigVersion::BASE` with the `SIGHASH_SINGLE` bug returning `uint256::ONE`; `sigHashWitnessV0` is the BIP143 algorithm (hashPrevouts, hashSequence, hashOutputs under the same flags, the amount, the script code).
--
--   **Encoding checks and the checker.** `isValidSignatureEncoding` is the strict-DER test (BIP66) byte for byte; `isLowDERSignature`, `isCompressedOrUncompressedPubKey`, `isCompressedPubKey`, `isDefinedHashtypeSignature`, `checkSignatureEncoding`, `checkPubKeyEncoding` under `SigFlags` (`dersig` is the only mainnet consensus flag; `lowS`, `strictenc`, `witnessPubkeyType` are policy and carried for fidelity). `checkECDSASignature` is the checker's method (hash type = last byte, witness v0 needs a non-negative amount); `checkSigPreTapscript` is `EvalChecksigPreTapscript` (`FindAndDelete` of the signature push for legacy scripts, encoding checks as `none`, verdict as `some`). `checkLockTime`/`checkSequence` are the checker's lock-time methods (`LOCKTIME_THRESHOLD`, `SEQUENCE_FINAL`, BIP68 masks). `legacyOracle` assembles Core's hashes, the checker and the lock-time checks into the `BitcoinScript.Oracle` of the legacy interpreter for a given script code.
--
--   **Auxiliary.** `p2pkhBytes` is the P2PKH output script as bytes; `sameSkeleton` relates transactions differing only in scriptSigs and witnesses; `minimalInt` and `derEncode` describe the DER layout.
--
--   **Formalization Note.** The script code handed to the oracle is the executed script, which is exact for scripts without `OP_CODESEPARATOR`. Field and scalar arithmetic are on `Nat` modulo $p$ and $n$; no claim about libsecp256k1's constant-time implementation is made, only about its mathematical semantics. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsValidSignatureEncoding, IsLowDERSignature, IsCompressedOrUncompressedPubKey, IsCompressedPubKey, IsDefinedHashtypeSignature, CheckSignatureEncoding, CheckPubKeyEncoding, FindAndDelete, CTransactionSignatureSerializer, SignatureHash (BASE and WITNESS_V0), EvalChecksigPreTapscript, GenericTransactionSignatureChecker::CheckECDSASignature/CheckLockTime/CheckSequence, src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp; GetScriptOp, src/script/script.cpp; CPubKey::IsValid/Verify/CheckLowS and ecdsa_signature_parse_der_lax, src/pubkey.cpp and pubkey.h; secp256k1_eckey_pubkey_parse (src/secp256k1/src/eckey_impl.h), secp256k1_ecdsa_sig_verify (ecdsa_impl.h), secp256k1_schnorrsig_verify (modules/schnorrsig/main_impl.h); BIP66, BIP143, BIP340 at bips revision 100ba872c808946155b1eeb8c4568058f2eea0a7

import Std
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinScript

namespace BitcoinSig

/-! Transcription of Bitcoin Core's signature layer at revision
`a773e1e33b349dc819b5a0edc1c7a4839dc73b48`: `GetScriptOp` (`script/script.cpp`), `FindAndDelete`,
`IsValidSignatureEncoding`, `IsLowDERSignature`, `IsCompressedOrUncompressedPubKey`,
`IsCompressedPubKey`, `IsDefinedHashtypeSignature`, `CheckSignatureEncoding`, `CheckPubKeyEncoding`,
`CTransactionSignatureSerializer`, `SignatureHash` (legacy and BIP143), `EvalChecksigPreTapscript`,
`GenericTransactionSignatureChecker::{CheckECDSASignature, CheckLockTime, CheckSequence}`
(`script/interpreter.cpp`); `CPubKey::{IsValid, Verify, CheckLowS}` and `ecdsa_signature_parse_der_lax`
(`pubkey.cpp`); and the secp256k1 semantics of `secp256k1_eckey_pubkey_parse`, `secp256k1_ecdsa_verify`
with signature normalization, and `secp256k1_schnorrsig_verify` (BIP340). -/

open BitcoinSer (Byte Bytes Tx TxIn TxOut OutPoint)

/-! ### secp256k1 -/

/-- The field prime `p = 2^256 - 2^32 - 977`. -/
def p : Nat := 2 ^ 256 - 2 ^ 32 - 977
/-- The group order `n`. -/
def n : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
def Gx : Nat := 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
def Gy : Nat := 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8

/-- Square-and-multiply modular exponentiation with explicit fuel. -/
def powModAux (m : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | fuel + 1, b, e, acc =>
    if e = 0 then acc
    else powModAux m fuel (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc)

def powMod (b e m : Nat) : Nat := powModAux m (e + 1) (b % m) e (1 % m)

/-- Field inverse by Fermat (`0` maps to `0`). -/
def finv (a : Nat) : Nat := powMod a (p - 2) p
/-- Scalar inverse modulo the group order. -/
def ninv (a : Nat) : Nat := powMod a (n - 2) n

/-- An affine point, or the point at infinity. -/
abbrev Point := Option (Nat × Nat)

def onCurve (P : Nat × Nat) : Bool := (P.2 * P.2) % p = (P.1 * P.1 * P.1 + 7) % p

/-- Affine addition on secp256k1 (`y^2 = x^3 + 7`). -/
def padd (P Q : Point) : Point :=
  match P, Q with
  | none, q => q
  | q, none => q
  | some (x1, y1), some (x2, y2) =>
    if x1 % p = x2 % p then
      if (y1 + y2) % p = 0 then none
      else
        -- doubling
        let l := (3 * x1 * x1) * finv (2 * y1 % p) % p
        let x3 := (l * l + 2 * (p - x1 % p)) % p
        let y3 := (l * ((x1 + p - x3) % p) + (p - y1 % p)) % p
        some (x3, y3)
    else
      let l := ((y2 + p - y1 % p) % p) * finv ((x2 + p - x1 % p) % p) % p
      let x3 := (l * l + (p - x1 % p) + (p - x2 % p)) % p
      let y3 := (l * ((x1 + p - x3) % p) + (p - y1 % p)) % p
      some (x3, y3)

/-- Double-and-add scalar multiplication with explicit fuel. -/
def pmulAux : Nat → Nat → Point → Point → Point
  | 0, _, _, acc => acc
  | fuel + 1, k, P, acc =>
    if k = 0 then acc
    else pmulAux fuel (k / 2) (padd P P) (if k % 2 = 1 then padd acc P else acc)

def pmul (k : Nat) (P : Point) : Point := pmulAux 257 k P none

def G : Point := some (Gx, Gy)

def beVal (b : Bytes) : Nat := b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- `secp256k1_ge_set_xo_var`: the point with abscissa `x` and the given parity of `y`, if any. -/
def liftXParity (x : Nat) (odd : Bool) : Point :=
  let y := powMod (x * x * x + 7) ((p + 1) / 4) p
  if y * y % p = (x * x * x + 7) % p then
    some (x, if (y % 2 = 1) = odd then y else (p - y) % p)
  else none

/-- `secp256k1_eckey_pubkey_parse`: compressed (`02`/`03`, 33 bytes), uncompressed (`04`) and hybrid
(`06`/`07`, 65 bytes, parity of `y` must match). Coordinates must be below `p` and on the curve. -/
def parsePubkey (pk : Bytes) : Point :=
  match pk with
  | tag :: rest =>
    if pk.length = 33 ∧ (tag.toNat = 2 ∨ tag.toNat = 3) then
      let x := beVal rest
      if x < p then liftXParity x (tag.toNat = 3) else none
    else if pk.length = 65 ∧ (tag.toNat = 4 ∨ tag.toNat = 6 ∨ tag.toNat = 7) then
      let x := beVal (rest.take 32); let y := beVal (rest.drop 32)
      if x < p ∧ y < p ∧ ((tag.toNat = 6 ∨ tag.toNat = 7) → ((y % 2 = 1) = (tag.toNat = 7))) ∧ onCurve (x, y) = true
      then some (x, y) else none
    else none
  | [] => none

/-- `CPubKey::GetLen` and `CPubKey::IsValid`: the header byte announces the length. -/
def pubkeyLen (header : Nat) : Nat :=
  if header = 2 ∨ header = 3 then 33 else if header = 4 ∨ header = 6 ∨ header = 7 then 65 else 0
def pubkeyValid (pk : Bytes) : Bool :=
  match pk with
  | [] => false
  | h :: _ => decide (pubkeyLen h.toNat = pk.length)

/-- `secp256k1_scalar_is_high`: `s > n/2`. -/
def isHighS (s : Nat) : Bool := decide (n / 2 < s)
/-- `secp256k1_ecdsa_signature_normalize`: replace a high `s` by `n - s`. -/
def normalizeS (s : Nat) : Nat := if isHighS s then n - s else s

/-- The scalar read of a big-endian value (`secp256k1_scalar_set_b32`, overflow flagged). -/
def scalarOf (b : Bytes) : Option Nat := let v := beVal b; if v < n then some v else none

/-- `ecdsa_signature_parse_der_lax`: `none` where the parser returns `0`; `some (0, 0)` where an
integer overflows (the "correctly-parsed but invalid" signature); trailing bytes are ignored. -/
def parseDerLax (input : Bytes) : Option (Nat × Nat) :=
  let len := input.length
  let at_ (i : Nat) : Nat := (input.getD i 0).toNat
  -- sequence tag
  if len = 0 ∨ at_ 0 ≠ 0x30 then none else
  let pos := 1
  if pos = len then none else
  let lenbyte := at_ pos
  let pos := pos + 1
  -- sequence length (long form: skip the length bytes)
  let pos? : Option Nat :=
    if 0x80 ≤ lenbyte then
      let lb := lenbyte - 0x80
      if len - pos < lb then none else some (pos + lb)
    else some pos
  match pos? with
  | none => none
  | some pos =>
  -- an integer: tag, length (short or long form with leading zeros stripped, at most 3 bytes)
  let readInt (pos : Nat) : Option (Nat × Nat × Nat) :=  -- (start, length, position after)
    if pos = len ∨ at_ pos ≠ 0x02 then none else
    let pos := pos + 1
    if pos = len then none else
    let lenbyte := at_ pos
    let pos := pos + 1
    if 0x80 ≤ lenbyte then
      let lb := lenbyte - 0x80
      if len - pos < lb then none else
      -- skip leading zero length bytes
      let rec skipZeros (pos lb : Nat) (fuel : Nat) : Nat × Nat :=
        match fuel with
        | 0 => (pos, lb)
        | f + 1 => if 0 < lb ∧ at_ pos = 0 then skipZeros (pos + 1) (lb - 1) f else (pos, lb)
      let (pos, lb) := skipZeros pos lb lb
      if 4 ≤ lb then none else
      let rlen := (List.range lb).foldl (fun acc i => acc * 256 + at_ (pos + i)) 0
      let pos := pos + lb
      if len - pos < rlen then none else some (pos, rlen, pos + rlen)
    else
      if len - pos < lenbyte then none else some (pos, lenbyte, pos + lenbyte)
  match readInt pos with
  | none => none
  | some (rpos, rlen, pos) =>
  match readInt pos with
  | none => none
  | some (spos, slen, _) =>
  -- strip leading zeros, reject more than 32 significant bytes
  let strip (pos len : Nat) : Nat × Nat :=
    let rec go (pos len : Nat) (fuel : Nat) : Nat × Nat :=
      match fuel with
      | 0 => (pos, len)
      | f + 1 => if 0 < len ∧ at_ pos = 0 then go (pos + 1) (len - 1) f else (pos, len)
    go pos len len
  let (rpos, rlen) := strip rpos rlen
  let (spos, slen) := strip spos slen
  if 32 < rlen ∨ 32 < slen then some (0, 0) else
  let r := beVal ((input.drop rpos).take rlen)
  let s := beVal ((input.drop spos).take slen)
  -- `secp256k1_ecdsa_signature_parse_compact`: a scalar at or above `n` is an overflow
  if r < n ∧ s < n then some (r, s) else some (0, 0)

/-- `secp256k1_ecdsa_sig_verify` on a parsed key, a message scalar and a (normalized) signature. -/
def ecdsaVerifyRaw (Q : Point) (e r s : Nat) : Bool :=
  if r = 0 ∨ s = 0 ∨ n ≤ r ∨ n ≤ s then false
  else
    let w := ninv s
    let u1 := e * w % n
    let u2 := r * w % n
    match padd (pmul u1 G) (pmul u2 Q) with
    | none => false
    | some (x, _) => decide (x % n = r)

/-- `CPubKey::Verify(hash, vchSig)`: key validity and parsing, lax DER parsing, S normalization,
then `secp256k1_ecdsa_verify` with the message reduced modulo `n`. -/
def pubkeyVerify (pk : Bytes) (hash : Bytes) (sig : Bytes) : Bool :=
  if !pubkeyValid pk then false
  else match parsePubkey pk with
    | none => false
    | some Q =>
      match parseDerLax sig with
      | none => false
      | some (r, s) => ecdsaVerifyRaw (some Q) (beVal hash % n) r (normalizeS s)

/-- `CPubKey::CheckLowS`. -/
def checkLowS (sig : Bytes) : Bool :=
  match parseDerLax sig with
  | none => false
  | some (_, s) => !isHighS s

/-! ### BIP340 Schnorr -/

/-- `tagged_hash(tag, m) = SHA256(SHA256(tag) || SHA256(tag) || m)`. -/
def taggedHash (tag : Bytes) (m : Bytes) : Bytes :=
  let th := BitcoinSer.sha256 tag
  BitcoinSer.sha256 (th ++ th ++ m)

def ascii (s : String) : Bytes := s.toUTF8.toList.map fun c => BitVec.ofNat 8 c.toNat

/-- `lift_x` of BIP340: the point with abscissa `x` and even `y`. -/
def liftX (x : Nat) : Point := if x < p then liftXParity x false else none

/-- `secp256k1_schnorrsig_verify(sig64, msg, pk32)`. -/
def schnorrVerify (pk32 : Bytes) (msg : Bytes) (sig64 : Bytes) : Bool :=
  if pk32.length ≠ 32 ∨ sig64.length ≠ 64 then false
  else
    let r := beVal (sig64.take 32)
    let s := beVal (sig64.drop 32)
    if p ≤ r ∨ n ≤ s then false
    else match liftX (beVal pk32) with
      | none => false
      | some P =>
        let e := beVal (taggedHash (ascii "BIP0340/challenge") (sig64.take 32 ++ pk32 ++ msg)) % n
        match padd (pmul s G) (pmul ((n - e) % n) (some P)) with
        | none => false
        | some (rx, ry) => decide (ry % 2 = 0 ∧ rx = r)

/-! ### Byte-level scripts (`script/script.cpp`) -/

open BitcoinScript (Instr Script)

def OP_PUSHDATA1 : Nat := 0x4c
def OP_PUSHDATA2 : Nat := 0x4d
def OP_PUSHDATA4 : Nat := 0x4e

/-- `GetScriptOp`: one instruction and the remaining bytes, `none` where it returns `false`. -/
def getOp (s : Bytes) : Option (Instr × Bytes) :=
  match s with
  | [] => none
  | op :: rest =>
    let o := op.toNat
    if o ≤ OP_PUSHDATA4 then
      let sz? : Option (Nat × Bytes) :=
        if o < OP_PUSHDATA1 then some (o, rest)
        else if o = OP_PUSHDATA1 then
          match rest with
          | b :: r => some (b.toNat, r)
          | [] => none
        else if o = OP_PUSHDATA2 then
          if rest.length < 2 then none else some (BitcoinSer.leVal (rest.take 2), rest.drop 2)
        else
          if rest.length < 4 then none else some (BitcoinSer.leVal (rest.take 4), rest.drop 4)
      match sz? with
      | none => none
      | some (sz, r) => if r.length < sz then none else some (.push (r.take sz), r.drop sz)
    else some (.op op, rest)

/-- Parse a whole script; `none` on a malformed push (`SCRIPT_ERR_BAD_OPCODE`). -/
def parseScriptAux : Nat → Bytes → Option Script
  | _, [] => some []
  | 0, _ => none
  | fuel + 1, s =>
    match getOp s with
    | none => none
    | some (i, r) =>
      match parseScriptAux fuel r with
      | none => none
      | some is => some (i :: is)

def parseScript (s : Bytes) : Option Script := parseScriptAux s.length s

/-- `CScript() << vch`: the canonical push of a byte string. -/
def pushBytes (d : Bytes) : Bytes :=
  if d.length < OP_PUSHDATA1 then BitVec.ofNat 8 d.length :: d
  else if d.length ≤ 0xff then [BitVec.ofNat 8 OP_PUSHDATA1, BitVec.ofNat 8 d.length] ++ d
  else if d.length ≤ 0xffff then BitVec.ofNat 8 OP_PUSHDATA2 :: BitcoinSer.leBytes 2 d.length ++ d
  else BitVec.ofNat 8 OP_PUSHDATA4 :: BitcoinSer.leBytes 4 d.length ++ d

/-- `FindAndDelete(script, b)`: at every instruction boundary remove every occurrence of `b`;
returns the result and the number found. -/
def findAndDeleteAux (b : Bytes) : Nat → Bytes → Bytes → Nat → Bytes × Nat
  | 0, s, acc, found => (acc ++ s, found)
  | fuel + 1, s, acc, found =>
    -- strip repeated occurrences at the current position
    let rec strip (s : Bytes) (found : Nat) (f : Nat) : Bytes × Nat :=
      match f with
      | 0 => (s, found)
      | f + 1 => if b.length ≤ s.length ∧ s.take b.length = b then strip (s.drop b.length) (found + 1) f else (s, found)
    let (s, found) := strip s found (s.length + 1)
    match getOp s with
    | none => (acc ++ s, found)
    | some (_, r) =>
      let consumed := s.take (s.length - r.length)
      findAndDeleteAux b fuel r (acc ++ consumed) found

def findAndDelete (script b : Bytes) : Bytes × Nat :=
  if b.isEmpty then (script, 0) else findAndDeleteAux b (script.length + 1) script [] 0

/-- `SerializeScriptCode`: the script code with every `OP_CODESEPARATOR` instruction removed,
written as a byte string. -/
def scriptCodeBytesAux : Nat → Bytes → Bytes
  | 0, s => s
  | fuel + 1, s =>
    match getOp s with
    | none => s
    | some (i, r) =>
      let consumed := s.take (s.length - r.length)
      (if i = .op BitcoinScript.OP_CODESEPARATOR then [] else consumed) ++ scriptCodeBytesAux fuel r

def serScriptCode (sc : Bytes) : Bytes :=
  let body := scriptCodeBytesAux (sc.length + 1) sc
  BitcoinSer.writeCompactSize body.length ++ body

/-! ### Signature hashes (`SignatureHash`) -/

def SIGHASH_ALL : Nat := 1
def SIGHASH_NONE : Nat := 2
def SIGHASH_SINGLE : Nat := 3
def SIGHASH_ANYONECANPAY : Nat := 0x80

/-- `uint256::ONE` in serialized byte order. -/
def uint256One : Bytes := 1 :: List.replicate 31 0

/-- `CTransactionSignatureSerializer::SerializeInput`. -/
def serSigInput (tx : Tx) (scriptCode : Bytes) (nIn : Nat) (anyoneCanPay single none_ : Bool) (nInput : Nat) : Bytes :=
  let nInput := if anyoneCanPay then nIn else nInput
  let i := tx.vin.getD nInput ⟨⟨[], 0⟩, [], 0, []⟩
  BitcoinSer.serOutPoint i.prevout ++
  (if nInput ≠ nIn then BitcoinSer.serBytes [] else serScriptCode scriptCode) ++
  (if nInput ≠ nIn ∧ (single ∨ none_) then BitcoinSer.ser32 0 else BitcoinSer.ser32 i.nSequence)

/-- `CTransactionSignatureSerializer::SerializeOutput`. -/
def serSigOutput (tx : Tx) (nIn : Nat) (single : Bool) (nOutput : Nat) : Bytes :=
  if single ∧ nOutput ≠ nIn then BitcoinSer.serTxOut ⟨-1, []⟩
  else BitcoinSer.serTxOut (tx.vout.getD nOutput ⟨-1, []⟩)

/-- `CTransactionSignatureSerializer::Serialize`. -/
def serSigTx (tx : Tx) (scriptCode : Bytes) (nIn : Nat) (hashType : Nat) : Bytes :=
  let anyoneCanPay := decide (hashType &&& SIGHASH_ANYONECANPAY ≠ 0)
  let single := decide (hashType &&& 0x1f = SIGHASH_SINGLE)
  let none_ := decide (hashType &&& 0x1f = SIGHASH_NONE)
  let nInputs := if anyoneCanPay then 1 else tx.vin.length
  let nOutputs := if none_ then 0 else if single then nIn + 1 else tx.vout.length
  BitcoinSer.ser32 tx.version ++
  BitcoinSer.writeCompactSize nInputs ++
  (List.range nInputs).flatMap (serSigInput tx scriptCode nIn anyoneCanPay single none_) ++
  BitcoinSer.writeCompactSize nOutputs ++
  (List.range nOutputs).flatMap (serSigOutput tx nIn single) ++
  BitcoinSer.ser32 tx.nLockTime

/-- `SignatureHash(scriptCode, tx, nIn, nHashType, amount, SigVersion::BASE)`: the SIGHASH_SINGLE
bug returns `uint256::ONE`; otherwise SHA-256d of the serializer output and the 4-byte hash type. -/
def sigHashLegacy (scriptCode : Bytes) (tx : Tx) (nIn : Nat) (hashType : Nat) : Bytes :=
  if hashType &&& 0x1f = SIGHASH_SINGLE ∧ tx.vout.length ≤ nIn then uint256One
  else BitcoinSer.hash256 (serSigTx tx scriptCode nIn hashType ++ BitcoinSer.ser32 hashType)

/-- `SignatureHash(..., SigVersion::WITNESS_V0)` (BIP143). -/
def sigHashWitnessV0 (scriptCode : Bytes) (tx : Tx) (nIn : Nat) (hashType : Nat) (amount : Int) : Bytes :=
  let anyoneCanPay := hashType &&& SIGHASH_ANYONECANPAY ≠ 0
  let single := hashType &&& 0x1f = SIGHASH_SINGLE
  let none_ := hashType &&& 0x1f = SIGHASH_NONE
  let zero : Bytes := List.replicate 32 0
  let hashPrevouts := if ¬ anyoneCanPay then BitcoinSer.hash256 (tx.vin.flatMap fun i => BitcoinSer.serOutPoint i.prevout) else zero
  let hashSequence := if ¬ anyoneCanPay ∧ ¬ single ∧ ¬ none_ then BitcoinSer.hash256 (tx.vin.flatMap fun i => BitcoinSer.ser32 i.nSequence) else zero
  let hashOutputs :=
    if ¬ single ∧ ¬ none_ then BitcoinSer.hash256 (tx.vout.flatMap BitcoinSer.serTxOut)
    else if single ∧ nIn < tx.vout.length then BitcoinSer.hash256 (BitcoinSer.serTxOut (tx.vout.getD nIn ⟨-1, []⟩))
    else zero
  let i := tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩
  BitcoinSer.hash256 (
    BitcoinSer.ser32 tx.version ++ hashPrevouts ++ hashSequence ++
    BitcoinSer.serOutPoint i.prevout ++ BitcoinSer.serBytes scriptCode ++ BitcoinSer.serInt64 amount ++
    BitcoinSer.ser32 i.nSequence ++ hashOutputs ++ BitcoinSer.ser32 tx.nLockTime ++ BitcoinSer.ser32 hashType)

/-! ### Encoding checks (`interpreter.cpp`) -/

/-- `IsValidSignatureEncoding` (strict DER with a trailing hash-type byte). -/
def isValidSignatureEncoding (sig : Bytes) : Bool :=
  let at_ (i : Nat) : Nat := (sig.getD i 0).toNat
  let len := sig.length
  if len < 9 then false
  else if 73 < len then false
  else if at_ 0 ≠ 0x30 then false
  else if at_ 1 ≠ len - 3 then false
  else
    let lenR := at_ 3
    if len ≤ 5 + lenR then false
    else
      let lenS := at_ (5 + lenR)
      if lenR + lenS + 7 ≠ len then false
      else if at_ 2 ≠ 0x02 then false
      else if lenR = 0 then false
      else if 0x80 ≤ at_ 4 then false
      else if 1 < lenR ∧ at_ 4 = 0 ∧ at_ 5 < 0x80 then false
      else if at_ (lenR + 4) ≠ 0x02 then false
      else if lenS = 0 then false
      else if 0x80 ≤ at_ (lenR + 6) then false
      else if 1 < lenS ∧ at_ (lenR + 6) = 0 ∧ at_ (lenR + 7) < 0x80 then false
      else true

/-- `IsLowDERSignature`: strict DER and low S (of the signature without the hash-type byte). -/
def isLowDERSignature (sig : Bytes) : Bool :=
  isValidSignatureEncoding sig && checkLowS sig.dropLast

def isCompressedOrUncompressedPubKey (pk : Bytes) : Bool :=
  match pk with
  | [] => false
  | h :: _ =>
    if pk.length < 33 then false
    else if h.toNat = 4 then decide (pk.length = 65)
    else if h.toNat = 2 ∨ h.toNat = 3 then decide (pk.length = 33)
    else false

def isCompressedPubKey (pk : Bytes) : Bool :=
  match pk with
  | [] => false
  | h :: _ => decide (pk.length = 33) && decide (h.toNat = 2 ∨ h.toNat = 3)

def isDefinedHashtypeSignature (sig : Bytes) : Bool :=
  match sig.getLast? with
  | none => false
  | some b => let t := b.toNat &&& (0xff ^^^ SIGHASH_ANYONECANPAY); decide (SIGHASH_ALL ≤ t ∧ t ≤ SIGHASH_SINGLE)

/-- The `script_verify_flags` consulted by the signature layer. Only `dersig` is a consensus flag on
mainnet; the others are relay policy and are carried for fidelity. -/
structure SigFlags where
  dersig : Bool
  lowS : Bool
  strictenc : Bool
  witnessPubkeyType : Bool
  deriving DecidableEq, Repr

/-- `CheckSignatureEncoding`: `true` where the source returns `true`, `false` where it sets an error. -/
def checkSignatureEncoding (f : SigFlags) (sig : Bytes) : Bool :=
  if sig.isEmpty then true
  else if (f.dersig || f.lowS || f.strictenc) && !isValidSignatureEncoding sig then false
  else if f.lowS && !isLowDERSignature sig then false
  else if f.strictenc && !isDefinedHashtypeSignature sig then false
  else true

inductive SigVersion where
  | base
  | witnessV0
  deriving DecidableEq, Repr

/-- `CheckPubKeyEncoding`. -/
def checkPubKeyEncoding (f : SigFlags) (v : SigVersion) (pk : Bytes) : Bool :=
  if f.strictenc && !isCompressedOrUncompressedPubKey pk then false
  else if f.witnessPubkeyType && v = .witnessV0 && !isCompressedPubKey pk then false
  else true

/-! ### The transaction signature checker -/

/-- `GenericTransactionSignatureChecker::CheckECDSASignature`. -/
def checkECDSASignature (tx : Tx) (nIn : Nat) (amount : Int) (v : SigVersion) (sig pk scriptCode : Bytes) : Bool :=
  if !pubkeyValid pk then false
  else match sig.getLast? with
    | none => false
    | some ht =>
      let sig' := sig.dropLast
      let hashType := ht.toNat
      let sighash := match v with
        | .base => sigHashLegacy scriptCode tx nIn hashType
        | .witnessV0 => sigHashWitnessV0 scriptCode tx nIn hashType amount
      if v = .witnessV0 ∧ amount < 0 then false
      else pubkeyVerify pk sighash sig'

/-- `EvalChecksigPreTapscript`: `FindAndDelete` of the signature push (legacy only), the two encoding
checks (`none` = script error), then the checker's verdict. -/
def checkSigPreTapscript (f : SigFlags) (tx : Tx) (nIn : Nat) (amount : Int) (v : SigVersion)
    (scriptCode : Bytes) (sig pk : Bytes) : Option Bool :=
  let sc := match v with
    | .base => (findAndDelete scriptCode (pushBytes sig)).1
    | .witnessV0 => scriptCode
  if !checkSignatureEncoding f sig ∨ !checkPubKeyEncoding f v pk then none
  else some (checkECDSASignature tx nIn amount v sig pk sc)

def LOCKTIME_THRESHOLD : Nat := 500000000
def SEQUENCE_FINAL : Nat := 0xffffffff
def SEQUENCE_LOCKTIME_DISABLE_FLAG : Nat := 2 ^ 31
def SEQUENCE_LOCKTIME_TYPE_FLAG : Nat := 2 ^ 22
def SEQUENCE_LOCKTIME_MASK : Nat := 0xffff

/-- `GenericTransactionSignatureChecker::CheckLockTime(nLockTime)`. -/
def checkLockTime (tx : Tx) (nIn : Nat) (lockTime : Int) : Bool :=
  if ¬ ((tx.nLockTime < LOCKTIME_THRESHOLD ∧ lockTime < LOCKTIME_THRESHOLD) ∨
        (LOCKTIME_THRESHOLD ≤ tx.nLockTime ∧ (LOCKTIME_THRESHOLD : Int) ≤ lockTime)) then false
  else if (tx.nLockTime : Int) < lockTime then false
  else if (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence = SEQUENCE_FINAL then false
  else true

/-- `GenericTransactionSignatureChecker::CheckSequence(nSequence)`. -/
def checkSequence (tx : Tx) (nIn : Nat) (sequence : Int) : Bool :=
  let txToSequence := (tx.vin.getD nIn ⟨⟨[], 0⟩, [], 0, []⟩).nSequence
  if tx.version < 2 then false
  else if txToSequence &&& SEQUENCE_LOCKTIME_DISABLE_FLAG ≠ 0 then false
  else
    let mask := SEQUENCE_LOCKTIME_TYPE_FLAG ||| SEQUENCE_LOCKTIME_MASK
    let txMasked := txToSequence &&& mask
    -- `CScriptNum & mask` on a 5-byte script number: the operand is non-negative here, since
    -- `OP_CHECKSEQUENCEVERIFY` rejects negative values before calling the checker
    let seqMasked := sequence.toNat &&& mask
    if ¬ ((txMasked < SEQUENCE_LOCKTIME_TYPE_FLAG ∧ seqMasked < SEQUENCE_LOCKTIME_TYPE_FLAG) ∨
          (SEQUENCE_LOCKTIME_TYPE_FLAG ≤ txMasked ∧ SEQUENCE_LOCKTIME_TYPE_FLAG ≤ seqMasked)) then false
    else if txMasked < seqMasked then false
    else true

/-- The concrete oracle for the legacy interpreter: Core's hashes, the pre-tapscript signature check
on `scriptCode` (the script being executed, for scripts without `OP_CODESEPARATOR`), and the
lock-time checks of the transaction being validated. -/
def legacyOracle (f : SigFlags) (tx : Tx) (nIn : Nat) (amount : Int) (v : SigVersion) (scriptCode : Bytes) :
    BitcoinScript.Oracle where
  ripemd160 := BitcoinSer.ripemd160
  sha1 := BitcoinSer.sha1
  sha256 := BitcoinSer.sha256
  hash160 := BitcoinSer.hash160
  hash256 := BitcoinSer.hash256
  checkSig := checkSigPreTapscript f tx nIn amount v scriptCode
  checkLockTime := checkLockTime tx nIn
  checkSequence := checkSequence tx nIn

/-- The P2PKH output script as bytes: `OP_DUP OP_HASH160 <h> OP_EQUALVERIFY OP_CHECKSIG`. -/
def p2pkhBytes (h : Bytes) : Bytes := [0x76, 0xa9] ++ pushBytes h ++ [0x88, 0xac]

/-- Two transactions with the same version, outputs, lock time, and the same prevouts and sequence
numbers in order (scriptSigs and witnesses may differ): what the signature hashes may depend on. -/
def sameSkeleton (tx tx' : Tx) : Prop :=
  tx'.version = tx.version ∧ tx'.vout = tx.vout ∧ tx'.nLockTime = tx.nLockTime ∧
  tx'.vin.map (fun i => (i.prevout, i.nSequence)) = tx.vin.map (fun i => (i.prevout, i.nSequence))

/-- The minimal big-endian positive integer encoding DER requires. -/
def minimalInt (v : Bytes) : Prop :=
  v ≠ [] ∧ (v.getD 0 0).toNat < 0x80 ∧ (1 < v.length → (v.getD 0 0).toNat = 0 → 0x80 ≤ (v.getD 1 0).toNat)

/-- The DER layout `30 len 02 |r| r 02 |s| s ht`. -/
def derEncode (r s : Bytes) (ht : Byte) : Bytes :=
  [0x30, BitVec.ofNat 8 (r.length + s.length + 4), 0x02, BitVec.ofNat 8 r.length] ++ r ++
  [0x02, BitVec.ofNat 8 s.length] ++ s ++ [ht]

end BitcoinSig


