-- Prove2me | Definitions.Def_BitcoinHtlc
-- name    : BitcoinHtlc
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T17:25:52.461809+00:00
-- url     : https://prove2.me/theorems/fc1a24bf-6065-4a51-82b7-feb770659e30
-- title:
--   The Lightning offered and received HTLC witness scripts and their spending conditions
-- statement:
--   Names over the script, signature, verification and `to_local` missions; nothing of Core is re-transcribed.
--
--   **`offeredScript revHash remoteKey localKey payHash`** / **`offeredBytes …`** — the BOLT #3 offered-HTLC witness script `OP_DUP OP_HASH160 <revHash> OP_EQUAL OP_IF OP_CHECKSIG OP_ELSE <remoteKey> OP_SWAP OP_SIZE 32 OP_EQUAL OP_NOTIF OP_DROP 2 OP_SWAP <localKey> 2 OP_CHECKMULTISIG OP_ELSE OP_HASH160 <payHash> OP_EQUALVERIFY OP_CHECKSIG OP_ENDIF OP_ENDIF`, parsed and as `CScript` serializes it (`2` as `OP_2`, `32` as the one-byte push `0x20`).
--
--   **`receivedScript … expiry`** / **`receivedBytes …`** — the received-HTLC script, whose inner branches are `OP_IF OP_HASH160 <payHash> OP_EQUALVERIFY 2 OP_SWAP <localKey> 2 OP_CHECKMULTISIG OP_ELSE OP_DROP <expiry> OP_CHECKLOCKTIMEVERIFY OP_DROP OP_CHECKSIG OP_ENDIF`, the expiry encoded by the `to_local` mission's `numInstr`/`numBytes`.
--
--   **`CltvPasses f o expiry`** — what `OP_CHECKLOCKTIMEVERIFY` lets through: the flag is off, or `expiry` is non-negative and the oracle's `checkLockTime expiry` holds.
--
--   **`OfferedSpend f o revHash remoteKey localKey payHash st`** — for a witness stack `st` (top first): the revocation path `[pk, sig]` with `hash160 pk = revHash` and `sig` valid for `pk`; the preimage path `[preimage, sig]` with `hash160 preimage ≠ revHash`, a 32-byte preimage hashing to `payHash`, and `sig` valid for `remoteKey`; or the timeout path `[x, localSig, remoteSig, dummy]` with `hash160 x ≠ revHash`, `x` not 32 bytes, the 2-of-2 `multisigLoop o [localSig, remoteSig] [localKey, remoteKey]` passing, and an empty dummy when `NULLDUMMY` is enforced.
--
--   **`ReceivedSpend … expiry st`** — the revocation path as above; the success path `[preimage, localSig, remoteSig, dummy]` (32-byte preimage hashing to `payHash`, not to `revHash`, the 2-of-2 passing, dummy as above); or the timeout path `[x, sig]` with `hash160 x ≠ revHash`, `x` not 32 bytes, `CltvPasses`, and `sig` valid for `remoteKey`.
--
--   **Formalization Note.** `multisigLoop`, `Flags`, `Oracle`, `evalScript` are the script mission's; `legacyOracle`, `checkLockTime`, `parseScript` the signature mission's; `verifyScript`, `topTrue` the verification mission's; `numInstr`, `inputSequence` the `to_local` mission's. The two 20-byte hashes are free parameters. Only `Std` is imported.
-- source:
--   BOLT #3, Bitcoin Transaction and Script Formats, 'Offered HTLC Outputs' and 'Received HTLC Outputs': https://github.com/lightning/bolts/blob/master/03-transactions.md#offered-htlc-outputs; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: EvalScript (OP_DUP, OP_HASH160, OP_EQUAL, OP_IF/OP_NOTIF, OP_SWAP, OP_SIZE, OP_CHECKMULTISIG, OP_CHECKLOCKTIMEVERIFY, OP_CHECKSIG), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/script/interpreter.cpp); BIP65, BIP141, BIP147

import Definitions.Def_BitcoinToLocal

/-!
# The Lightning HTLC outputs under Bitcoin's script interpreter

BOLT #3 (Lightning Network specification, *Bitcoin Transaction and Script Formats*, non-anchor
form) gives the two HTLC outputs of a commitment transaction the witness scripts

Offered HTLC (the local node offered the HTLC):
```
OP_DUP OP_HASH160 <RIPEMD160(SHA256(revocationpubkey))> OP_EQUAL
OP_IF OP_CHECKSIG
OP_ELSE <remote_htlcpubkey> OP_SWAP OP_SIZE 32 OP_EQUAL
  OP_NOTIF OP_DROP 2 OP_SWAP <local_htlcpubkey> 2 OP_CHECKMULTISIG
  OP_ELSE OP_HASH160 <RIPEMD160(payment_hash)> OP_EQUALVERIFY OP_CHECKSIG
  OP_ENDIF
OP_ENDIF
```
Received HTLC:
```
OP_DUP OP_HASH160 <RIPEMD160(SHA256(revocationpubkey))> OP_EQUAL
OP_IF OP_CHECKSIG
OP_ELSE <remote_htlcpubkey> OP_SWAP OP_SIZE 32 OP_EQUAL
  OP_IF OP_HASH160 <RIPEMD160(payment_hash)> OP_EQUALVERIFY 2 OP_SWAP <local_htlcpubkey> 2 OP_CHECKMULTISIG
  OP_ELSE OP_DROP <cltv_expiry> OP_CHECKLOCKTIMEVERIFY OP_DROP OP_CHECKSIG
  OP_ENDIF
OP_ENDIF
```
paid to as pay-to-witness-script-hash. The 20-byte hashes are parameters `revHash` and `payHash`
(any bytes), the keys `remoteKey` and `localKey`. `2` is `CScript << 2` (`OP_2`), `32` is
`CScript << 32` (the one-byte script-number push `01 20`), and `<cltv_expiry>` is
`CScript << int64` (`BitcoinToLocal.numInstr` / `numBytes`).

Witness stacks are listed top first, as `evalScript` takes them. In BOLT #3's `CScriptWitness`
order (last element on top) the witnesses are: revocation `<revocation_sig> <revocationpubkey>`;
offered-timeout `0 <remotehtlcsig> <localhtlcsig> <>`; offered-preimage
`<remotehtlcsig> <payment_preimage>`; received-success `0 <remotehtlcsig> <localhtlcsig>
<payment_preimage>`; received-timeout `<remotehtlcsig> <>`.
-/

namespace BitcoinHtlc

open BitcoinScript BitcoinSig BitcoinVerify BitcoinToLocal

/-- The BOLT #3 offered-HTLC witness script, parsed. -/
def offeredScript (revHash remoteKey localKey payHash : Bytes) : Script :=
  [.op OP_DUP, .op OP_HASH160, .push revHash, .op OP_EQUAL,
   .op OP_IF, .op OP_CHECKSIG,
   .op OP_ELSE, .push remoteKey, .op OP_SWAP, .op OP_SIZE, numInstr 32, .op OP_EQUAL,
   .op OP_NOTIF, .op OP_DROP, numInstr 2, .op OP_SWAP, .push localKey, numInstr 2, .op OP_CHECKMULTISIG,
   .op OP_ELSE, .op OP_HASH160, .push payHash, .op OP_EQUALVERIFY, .op OP_CHECKSIG,
   .op OP_ENDIF,
   .op OP_ENDIF]

/-- The BOLT #3 received-HTLC witness script, parsed. -/
def receivedScript (revHash remoteKey localKey payHash : Bytes) (expiry : Int) : Script :=
  [.op OP_DUP, .op OP_HASH160, .push revHash, .op OP_EQUAL,
   .op OP_IF, .op OP_CHECKSIG,
   .op OP_ELSE, .push remoteKey, .op OP_SWAP, .op OP_SIZE, numInstr 32, .op OP_EQUAL,
   .op OP_IF, .op OP_HASH160, .push payHash, .op OP_EQUALVERIFY, numInstr 2, .op OP_SWAP, .push localKey,
     numInstr 2, .op OP_CHECKMULTISIG,
   .op OP_ELSE, .op OP_DROP, numInstr expiry, .op OP_CHECKLOCKTIMEVERIFY, .op OP_DROP, .op OP_CHECKSIG,
   .op OP_ENDIF,
   .op OP_ENDIF]

/-- The offered-HTLC witness script, as `CScript` serializes it. -/
def offeredBytes (revHash remoteKey localKey payHash : Bytes) : Bytes :=
  [OP_DUP, OP_HASH160] ++ pushBytes revHash ++ [OP_EQUAL, OP_IF, OP_CHECKSIG, OP_ELSE] ++
    pushBytes remoteKey ++ [OP_SWAP, OP_SIZE] ++ numBytes 32 ++ [OP_EQUAL, OP_NOTIF, OP_DROP] ++
    numBytes 2 ++ [OP_SWAP] ++ pushBytes localKey ++ numBytes 2 ++ [OP_CHECKMULTISIG, OP_ELSE, OP_HASH160] ++
    pushBytes payHash ++ [OP_EQUALVERIFY, OP_CHECKSIG, OP_ENDIF, OP_ENDIF]

/-- The received-HTLC witness script, as `CScript` serializes it. -/
def receivedBytes (revHash remoteKey localKey payHash : Bytes) (expiry : Int) : Bytes :=
  [OP_DUP, OP_HASH160] ++ pushBytes revHash ++ [OP_EQUAL, OP_IF, OP_CHECKSIG, OP_ELSE] ++
    pushBytes remoteKey ++ [OP_SWAP, OP_SIZE] ++ numBytes 32 ++ [OP_EQUAL, OP_IF, OP_HASH160] ++
    pushBytes payHash ++ [OP_EQUALVERIFY] ++ numBytes 2 ++ [OP_SWAP] ++ pushBytes localKey ++ numBytes 2 ++
    [OP_CHECKMULTISIG, OP_ELSE, OP_DROP] ++ numBytes expiry ++
    [OP_CHECKLOCKTIMEVERIFY, OP_DROP, OP_CHECKSIG, OP_ENDIF, OP_ENDIF]

/-- What `OP_CHECKLOCKTIMEVERIFY` lets through for the operand `expiry`: nothing is checked when the
`CHECKLOCKTIMEVERIFY` flag is off; otherwise the operand must be non-negative and satisfy the
checker's `CheckLockTime` (there is no disable bit for lock times). -/
def CltvPasses (f : Flags) (o : Oracle) (expiry : Int) : Prop :=
  f.cltv = false ∨ (0 ≤ expiry ∧ o.checkLockTime expiry = true)

instance (f : Flags) (o : Oracle) (expiry : Int) : Decidable (CltvPasses f o expiry) := by
  unfold CltvPasses; infer_instance

/-- The three ways of satisfying the offered-HTLC script, on a witness stack `st` (top first):
the revocation path `[pubkey, sig]` with the pubkey hashing to `revHash` and `sig` valid for it;
the preimage path `[preimage, sig]` with a 32-byte preimage hashing to `payHash` (and not to
`revHash`) and `sig` valid for the remote key; or the timeout path `[x, localSig, remoteSig, dummy]`
with `x` neither hashing to `revHash` nor 32 bytes long, the 2-of-2 check of the local then the
remote signature passing, and an empty dummy when `NULLDUMMY` is enforced. -/
def OfferedSpend (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash : Bytes) (st : List Bytes) : Prop :=
  (∃ pk sig, st = [pk, sig] ∧ o.hash160 pk = revHash ∧ o.checkSig sig pk = some true) ∨
  (∃ preimage sig, st = [preimage, sig] ∧ o.hash160 preimage ≠ revHash ∧ preimage.length = 32 ∧
      o.hash160 preimage = payHash ∧ o.checkSig sig remoteKey = some true) ∨
  (∃ x localSig remoteSig dummy, st = [x, localSig, remoteSig, dummy] ∧ o.hash160 x ≠ revHash ∧ x.length ≠ 32 ∧
      multisigLoop o [localSig, remoteSig] [localKey, remoteKey] = some true ∧ (f.nulldummy = true → dummy = []))

/-- The three ways of satisfying the received-HTLC script, on a witness stack `st` (top first):
the revocation path `[pubkey, sig]`; the success path `[preimage, localSig, remoteSig, dummy]` with a
32-byte preimage hashing to `payHash` (and not to `revHash`), the 2-of-2 check passing and an empty
dummy when `NULLDUMMY` is enforced; or the timeout path `[x, sig]` with `x` neither hashing to
`revHash` nor 32 bytes long, the lock-time check passing and `sig` valid for the remote key. -/
def ReceivedSpend (f : Flags) (o : Oracle) (revHash remoteKey localKey payHash : Bytes) (expiry : Int)
    (st : List Bytes) : Prop :=
  (∃ pk sig, st = [pk, sig] ∧ o.hash160 pk = revHash ∧ o.checkSig sig pk = some true) ∨
  (∃ preimage localSig remoteSig dummy, st = [preimage, localSig, remoteSig, dummy] ∧
      o.hash160 preimage ≠ revHash ∧ preimage.length = 32 ∧ o.hash160 preimage = payHash ∧
      multisigLoop o [localSig, remoteSig] [localKey, remoteKey] = some true ∧ (f.nulldummy = true → dummy = [])) ∨
  (∃ x sig, st = [x, sig] ∧ o.hash160 x ≠ revHash ∧ x.length ≠ 32 ∧ CltvPasses f o expiry ∧
      o.checkSig sig remoteKey = some true)

end BitcoinHtlc


