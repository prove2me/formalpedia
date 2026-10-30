-- Prove2me | Definitions.Def_BitcoinAnchors
-- name    : BitcoinAnchors
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T19:41:52.074539+00:00
-- url     : https://prove2.me/theorems/90ad13a8-00ee-43d6-bc66-a7f06ec4c949
-- title:
--   The Lightning anchor-output scripts (to_remote, anchor, CSV-1 HTLCs) and their spending conditions
-- statement:
--   Names over the script, signature, verification, `to_local` and HTLC missions; nothing of Core is re-transcribed. These are the BOLT #3 scripts with `option_anchors`, the form every modern channel uses.
--
--   **`toRemoteScript remoteKey`** / **`toRemoteBytes`** — `<remote_pubkey> OP_CHECKSIGVERIFY 1 OP_CHECKSEQUENCEVERIFY`. **`anchorScript fundingKey`** / **`anchorBytes`** — `<funding_pubkey> OP_CHECKSIG OP_IFDUP OP_NOTIF 16 OP_CHECKSEQUENCEVERIFY OP_ENDIF`. **`offeredScript …`**, **`receivedScript … expiry`** / their byte forms — the HTLC mission's scripts with `1 OP_CHECKSEQUENCEVERIFY OP_DROP` inserted after the inner `OP_ENDIF`, inside the outer `OP_ELSE`.
--
--   **`ToRemoteSpend f o remoteKey st`** — `st = [sig]` with `sig` valid for `remoteKey` and `CsvPasses f o 1`. **`AnchorSpend f o fundingKey st`** — `st = [sig]` and either `sig` valid for `fundingKey` (the key holder, at any time) or the check returns a clean `false` (as for the empty signature) and `CsvPasses f o 16` (anyone, after 16 blocks). **`OfferedSpend`**, **`ReceivedSpend`** — the HTLC mission's three paths each, with `CsvPasses f o 1` added to the two non-revocation paths.
--
--   **Formalization Note.** `CsvPasses`, `numInstr`, `inputSequence` are the `to_local` mission's; `CltvPasses`, `multisigLoop` the HTLC and script missions'; `legacyOracle`, `checkSequence`, `parseScript` the signature mission's; `verifyScript` the verification mission's. The 20-byte hashes are parameters. Only `Std` is imported.
-- source:
--   BOLT #3 with option_anchors: to_remote Output, Anchor Outputs, Offered/Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#to_remote-output; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_CHECKSIGVERIFY, OP_IFDUP, OP_NOTIF, OP_CHECKSEQUENCEVERIFY, OP_CHECKMULTISIG), GenericTransactionSignatureChecker::CheckSequence (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinHtlc

/-!
# The Lightning anchor-output commitment scripts under Bitcoin's script interpreter

BOLT #3 (Lightning Network specification, *Bitcoin Transaction and Script Formats*) with
`option_anchors` changes three outputs of a commitment transaction and adds a fourth:

`to_remote` (the counterparty's balance, now delayed by one block so that the anchor can be used
for fee bumping first):
```
<remote_pubkey> OP_CHECKSIGVERIFY 1 OP_CHECKSEQUENCEVERIFY
```
Anchor (one per side, keyed by that side's funding key; spendable by the key holder at once and by
anyone after 16 blocks):
```
<funding_pubkey> OP_CHECKSIG OP_IFDUP
OP_NOTIF
    16 OP_CHECKSEQUENCEVERIFY
OP_ENDIF
```
Offered HTLC (the non-anchor script of `BitcoinHtlc.offeredScript` with `1 OP_CHECKSEQUENCEVERIFY
OP_DROP` at the end of the outer `OP_ELSE` branch):
```
OP_DUP OP_HASH160 <RIPEMD160(SHA256(revocationpubkey))> OP_EQUAL
OP_IF OP_CHECKSIG
OP_ELSE <remote_htlcpubkey> OP_SWAP OP_SIZE 32 OP_EQUAL
  OP_NOTIF OP_DROP 2 OP_SWAP <local_htlcpubkey> 2 OP_CHECKMULTISIG
  OP_ELSE OP_HASH160 <RIPEMD160(payment_hash)> OP_EQUALVERIFY OP_CHECKSIG
  OP_ENDIF
  1 OP_CHECKSEQUENCEVERIFY OP_DROP
OP_ENDIF
```
Received HTLC (likewise, from `BitcoinHtlc.receivedScript`):
```
OP_DUP OP_HASH160 <RIPEMD160(SHA256(revocationpubkey))> OP_EQUAL
OP_IF OP_CHECKSIG
OP_ELSE <remote_htlcpubkey> OP_SWAP OP_SIZE 32 OP_EQUAL
  OP_IF OP_HASH160 <RIPEMD160(payment_hash)> OP_EQUALVERIFY 2 OP_SWAP <local_htlcpubkey> 2 OP_CHECKMULTISIG
  OP_ELSE OP_DROP <cltv_expiry> OP_CHECKLOCKTIMEVERIFY OP_DROP OP_CHECKSIG
  OP_ENDIF
  1 OP_CHECKSEQUENCEVERIFY OP_DROP
OP_ENDIF
```
All four are paid to as pay-to-witness-script-hash. `1` and `16` are `CScript << 1` / `<< 16`,
i.e. `OP_1` (`0x51`) and `OP_16` (`0x60`); `2`, `32` and the expiry are as in `BitcoinHtlc`
(`BitcoinToLocal.numInstr` / `numBytes`). The hashes and keys are arbitrary byte strings.

Witness stacks are listed top first, as `evalScript` takes them (the reverse of BOLT #3's
`CScriptWitness` order): `to_remote` is spent with `<remote_sig>`; an anchor with `<sig>` by the key
holder, or with the empty signature `<>` by anyone once 16 blocks have passed (the interpreter turns
the empty signature into a clean `false`, which `OP_IFDUP` does not duplicate and `OP_NOTIF` consumes,
so the `16 OP_CHECKSEQUENCEVERIFY` branch runs and leaves `16` as the lone true value); the HTLCs
exactly as in `BitcoinHtlc`, now with `OP_CHECKSEQUENCEVERIFY 1` enforced on every non-revocation path.
-/

namespace BitcoinAnchors

open BitcoinScript BitcoinSig BitcoinVerify BitcoinToLocal

/-- The BOLT #3 `to_remote` witness script (`option_anchors`), parsed. -/
def toRemoteScript (remoteKey : Bytes) : Script :=
  [.push remoteKey, .op OP_CHECKSIGVERIFY, numInstr 1, .op OP_CHECKSEQUENCEVERIFY]

/-- The `to_remote` witness script, as `CScript` serializes it. -/
def toRemoteBytes (remoteKey : Bytes) : Bytes :=
  pushBytes remoteKey ++ [OP_CHECKSIGVERIFY] ++ numBytes 1 ++ [OP_CHECKSEQUENCEVERIFY]

/-- The BOLT #3 anchor witness script, parsed. -/
def anchorScript (fundingKey : Bytes) : Script :=
  [.push fundingKey, .op OP_CHECKSIG, .op OP_IFDUP, .op OP_NOTIF, numInstr 16, .op OP_CHECKSEQUENCEVERIFY,
   .op OP_ENDIF]

/-- The anchor witness script, as `CScript` serializes it. -/
def anchorBytes (fundingKey : Bytes) : Bytes :=
  pushBytes fundingKey ++ [OP_CHECKSIG, OP_IFDUP, OP_NOTIF] ++ numBytes 16 ++ [OP_CHECKSEQUENCEVERIFY, OP_ENDIF]

/-- The BOLT #3 offered-HTLC witness script with `option_anchors`, parsed. -/
def offeredScript (revHash remoteKey localKey payHash : Bytes) : Script :=
  [.op OP_DUP, .op OP_HASH160, .push revHash, .op OP_EQUAL,
   .op OP_IF, .op OP_CHECKSIG,
   .op OP_ELSE, .push remoteKey, .op OP_SWAP, .op OP_SIZE, numInstr 32, .op OP_EQUAL,
   .op OP_NOTIF, .op OP_DROP, numInstr 2, .op OP_SWAP, .push localKey, numInstr 2, .op OP_CHECKMULTISIG,
   .op OP_ELSE, .op OP_HASH160, .push payHash, .op OP_EQUALVERIFY, .op OP_CHECKSIG,
   .op OP_ENDIF,
   numInstr 1, .op OP_CHECKSEQUENCEVERIFY, .op OP_DROP,
   .op OP_ENDIF]

/-- The BOLT #3 received-HTLC witness script with `option_anchors`, parsed. -/
def receivedScript (revHash remoteKey localKey payHash : Bytes) (expiry : Int) : Script :=
  [.op OP_DUP, .op OP_HASH160, .push revHash, .op OP_EQUAL,
   .op OP_IF, .op OP_CHECKSIG,
   .op OP_ELSE, .push remoteKey, .op OP_SWAP, .op OP_SIZE, numInstr 32, .op OP_EQUAL,
   .op OP_IF, .op OP_HASH160, .push payHash, .op OP_EQUALVERIFY, numInstr 2, .op OP_SWAP, .push localKey,
     numInstr 2, .op OP_CHECKMULTISIG,
   .op OP_ELSE, .op OP_DROP, numInstr expiry, .op OP_CHECKLOCKTIMEVERIFY, .op OP_DROP, .op OP_CHECKSIG,
   .op OP_ENDIF,
   numInstr 1, .op OP_CHECKSEQUENCEVERIFY, .op OP_DROP,
   .op OP_ENDIF]

/-- The offered-HTLC witness script (`option_anchors`), as `CScript` serializes it. -/
def offeredBytes (revHash remoteKey localKey payHash : Bytes) : Bytes :=
  [OP_DUP, OP_HASH160] ++ pushBytes revHash ++ [OP_EQUAL, OP_IF, OP_CHECKSIG, OP_ELSE] ++
    pushBytes remoteKey ++ [OP_SWAP, OP_SIZE] ++ numBytes 32 ++ [OP_EQUAL, OP_NOTIF, OP_DROP] ++
    numBytes 2 ++ [OP_SWAP] ++ pushBytes localKey ++ numBytes 2 ++ [OP_CHECKMULTISIG, OP_ELSE, OP_HASH160] ++
    pushBytes payHash ++ [OP_EQUALVERIFY, OP_CHECKSIG, OP_ENDIF] ++ numBytes 1 ++
    [OP_CHECKSEQUENCEVERIFY, OP_DROP, OP_ENDIF]

/-- The received-HTLC witness script (`option_anchors`), as `CScript` serializes it. -/
def receivedBytes (revHash remoteKey localKey payHash : Bytes) (expiry : Int) : Bytes :=
  [OP_DUP, OP_HASH160] ++ pushBytes revHash ++ [OP_EQUAL, OP_IF, OP_CHECKSIG, OP_ELSE] ++
    pushBytes remoteKey ++ [OP_SWAP, OP_SIZE] ++ numBytes 32 ++ [OP_EQUAL, OP_IF, OP_HASH160] ++
    pushBytes payHash ++ [OP_EQUALVERIFY] ++ numBytes 2 ++ [OP_SWAP] ++ pushBytes localKey ++ numBytes 2 ++
    [OP_CHECKMULTISIG, OP_ELSE, OP_DROP] ++ numBytes expiry ++
    [OP_CHECKLOCKTIMEVERIFY, OP_DROP, OP_CHECKSIG, OP_ENDIF] ++ numBytes 1 ++
    [OP_CHECKSEQUENCEVERIFY, OP_DROP, OP_ENDIF]

/-- The one way of satisfying the `to_remote` script, on a witness stack `st` (top first): a lone
signature valid for the remote key, and the one-block delay check (`OP_CHECKSEQUENCEVERIFY 1`)
passing. `OP_CHECKSIGVERIFY` fails the script outright on an invalid signature, so the only value
ever left is the pushed `1`. -/
def ToRemoteSpend (f : Flags) (o : Oracle) (remoteKey : Bytes) (st : List Bytes) : Prop :=
  ∃ sig, st = [sig] ∧ o.checkSig sig remoteKey = some true ∧ CsvPasses f o 1

/-- The two ways of satisfying the anchor script, on a witness stack `st` (top first): a lone element
`sig` that is either a valid signature for the funding key (the key holder, at any time: `OP_IFDUP`
keeps the `true` and `OP_NOTIF` skips the delay), or a *clean* `false` of the signature check (such as
the empty signature) together with the 16-block delay check passing (anyone, after the delay: the
`16` pushed for `OP_CHECKSEQUENCEVERIFY` is the value left). A signature the oracle rejects outright
(`none`, e.g. a malformed encoding) fails the script. -/
def AnchorSpend (f : Flags) (o : Oracle) (fundingKey : Bytes) (st : List Bytes) : Prop :=
  ∃ sig, st = [sig] ∧
    (o.checkSig sig fundingKey = some true ∨ (o.checkSig sig fundingKey = some false ∧ CsvPasses f o 16))

/-- The three ways of satisfying the offered-HTLC script with `option_anchors`: exactly
`BitcoinHtlc.OfferedSpend`, with the one-block delay check `CsvPasses f o 1` added to the preimage
and timeout paths (the revocation path skips it). -/
def OfferedSpend (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash : Bytes) (st : List Bytes) : Prop :=
  (∃ pk sig, st = [pk, sig] ∧ o.hash160 pk = revHash ∧ o.checkSig sig pk = some true) ∨
  (∃ preimage sig, st = [preimage, sig] ∧ o.hash160 preimage ≠ revHash ∧ preimage.length = 32 ∧
      o.hash160 preimage = payHash ∧ o.checkSig sig remoteKey = some true ∧ CsvPasses f o 1) ∨
  (∃ x localSig remoteSig dummy, st = [x, localSig, remoteSig, dummy] ∧ o.hash160 x ≠ revHash ∧ x.length ≠ 32 ∧
      multisigLoop o [localSig, remoteSig] [localKey, remoteKey] = some true ∧ (f.nulldummy = true → dummy = []) ∧
      CsvPasses f o 1)

/-- The three ways of satisfying the received-HTLC script with `option_anchors`: exactly
`BitcoinHtlc.ReceivedSpend`, with the one-block delay check `CsvPasses f o 1` added to the success
and timeout paths (the revocation path skips it). -/
def ReceivedSpend (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash : Bytes) (expiry : Int)
    (st : List Bytes) : Prop :=
  (∃ pk sig, st = [pk, sig] ∧ o.hash160 pk = revHash ∧ o.checkSig sig pk = some true) ∨
  (∃ preimage localSig remoteSig dummy, st = [preimage, localSig, remoteSig, dummy] ∧
      o.hash160 preimage ≠ revHash ∧ preimage.length = 32 ∧ o.hash160 preimage = payHash ∧
      multisigLoop o [localSig, remoteSig] [localKey, remoteKey] = some true ∧ (f.nulldummy = true → dummy = []) ∧
      CsvPasses f o 1) ∨
  (∃ x sig, st = [x, sig] ∧ o.hash160 x ≠ revHash ∧ x.length ≠ 32 ∧ BitcoinHtlc.CltvPasses f o expiry ∧
      o.checkSig sig remoteKey = some true ∧ CsvPasses f o 1)

end BitcoinAnchors


