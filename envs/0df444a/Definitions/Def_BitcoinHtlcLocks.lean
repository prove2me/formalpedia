-- Prove2me | Definitions.Def_BitcoinHtlcLocks
-- name    : BitcoinHtlcLocks
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T19:35:27.216477+00:00
-- url     : https://prove2.me/theorems/ee564ab2-537d-4c47-8282-7e5d96a77c97
-- title:
--   Revocation spends and height-locked transactions
-- statement:
--   Two names over the HTLC and block missions.
--
--   **`RevocationSpend c script revHash pk sig`** — in verification context $c$ (transaction, input index, amount, flags), the witness's public key hashes (`hash160`) to the revocation hash and the signature verifies for it under the signature mission's `checkSigPreTapscript` with the witness-v0 sighash on `script`: the revocation path of an HTLC output.
--
--   **`HeightLocked tx`** — the transaction's `nLockTime` is nonzero and below `LOCKTIME_THRESHOLD` (500,000,000), i.e. a block height, as for a BOLT #3 HTLC-timeout transaction whose lock time is `cltv_expiry`.
--
--   **Formalization Note.** `isFinalTx`, `LOCKTIME_THRESHOLD`, `SEQUENCE_FINAL` are the block mission's (`BitcoinBlockV2`); `receivedBytes`, `ReceivedSpend` the HTLC mission's; `verifyScript`, `Ctx` the verification mission's. Only `Std` is imported.
-- source:
--   BOLT #3, HTLC-Timeout and HTLC-Success Transactions (locktime = cltv_expiry), Received HTLC Outputs: https://github.com/lightning/bolts/blob/master/03-transactions.md#htlc-timeout-and-htlc-success-transactions; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: IsFinalTx (src/consensus/tx_verify.cpp) as the block mission's `isFinalTx`, ContextualCheckBlock (src/validation.cpp), GenericTransactionSignatureChecker::CheckLockTime (src/script/interpreter.cpp); BIP65

import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinBlockV2

/-!
# HTLC lock times at the block level

The HTLC mission proves which witnesses spend a received HTLC output under `VerifyScript`; the
timeout path carries `OP_CHECKLOCKTIMEVERIFY <cltv_expiry>`. The block mission's
`ContextualCheckBlock` requires every transaction of a block to be final (`IsFinalTx`) at the
block's height. This file composes the two: a transaction that spends a received HTLC with a
two-element witness and sits in a block at height `h` is either a revocation spend or has
`cltv_expiry < h`. The same bound holds for a pre-signed HTLC-timeout transaction whose
`nLockTime` is the expiry.
-/

namespace BitcoinHtlcLocks

open BitcoinSer BitcoinScript BitcoinSig BitcoinVerify BitcoinHtlc BitcoinBlockV2

/-- The revocation spend of an HTLC output in context `c`: the witness's public key hashes to the
revocation hash and the signature verifies for it under the context's checker on `script`. -/
def RevocationSpend (c : BitcoinVerify.Ctx) (script revHash pk sig : BitcoinSer.Bytes) : Prop :=
  BitcoinSer.hash160 pk = revHash ∧
    BitcoinSig.checkSigPreTapscript (BitcoinVerify.sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 script sig pk = some true

/-- A transaction whose lock time is a block height (nonzero and below the threshold), as a
second-stage HTLC-timeout transaction's is. -/
def HeightLocked (tx : BitcoinSer.Tx) : Prop := 0 < tx.nLockTime ∧ tx.nLockTime < BitcoinBlockV2.LOCKTIME_THRESHOLD

end BitcoinHtlcLocks


