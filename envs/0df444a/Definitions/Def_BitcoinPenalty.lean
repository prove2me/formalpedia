-- Prove2me | Definitions.Def_BitcoinPenalty
-- name    : BitcoinPenalty
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T22:51:00.785021+00:00
-- url     : https://prove2.me/theorems/3dfa1122-fefd-4695-9c72-3910a4bfc996
-- title:
--   A revoked commitment transaction's outputs, the holder of the revocation key, and the cheater
-- statement:
--   Names over the `to_local`, HTLC, anchor, funding and lock-time missions.
--
--   **`CommitmentKeys`** — the keys of one commitment transaction: `revPk` and its hash `revHash`, `localDelayedPk`, `remoteKey`, `localHtlcKey`, `remoteHtlcKey`, the two funding keys, and `toSelfDelay`; **`Htlc`** — a payment hash and an expiry; **`WellFormed K`**, **`HtlcWellFormed h`** — the 520-byte bounds, $0 \le$ `toSelfDelay` $< 2^{16}$, $|{\rm expiry}| < 2^{32}$.
--
--   **Output scripts** — `toLocalBytes K`, `offeredBytes K h`, `receivedBytes K h`, their anchors forms, `toRemoteBytes K`, `anchorLocalBytes K`, `anchorRemoteBytes K`, all through the published constructors; **`p2wshOf sc`** — the pay-to-witness-script-hash program of a script; **`oracleOf c sc`** — the signature mission's `legacyOracle` for context $c$ with witness-v0 sighash on `sc`.
--
--   **`HoldsRevocation o K`** — the oracle accepts some signature (at most 520 bytes) for `revPk`, and `hash160 revPk = revHash`: the honest party after a revocation. **`NoRevocationSig o K`** — the oracle accepts no signature for `revPk`: the cheater, who never learned the revocation secret. **`NoRevHashPreimage o K`** — `revPk` is the only `hash160` preimage of `revHash` the oracle knows (second-preimage resistance, needed because the HTLC scripts test the hash of the pushed key).
--
--   **Witnesses** — `toLocalPenaltyWitness K sigR = [sigR, [1], script]`, `htlcPenaltyWitness K sigR sc = [sigR, revPk, sc]`. **Cheater paths** — `DelayedSpend` (the `to_local` delayed path), `OfferedNonRevocation`, `ReceivedNonRevocation` and their anchors forms (the HTLC paths other than revocation, with the one-block delay in the anchors form).
--
--   **Formalization Note.** Everything else is the published missions'. Unforgeability is a hypothesis on one oracle and one key; there is no key derivation, signing oracle, ECDSA or network model. Only `Std` is imported.
-- source:
--   BOLT #3 (commitment transaction outputs, revocation) and BOLT #5 (penalty transactions): https://github.com/lightning/bolts/blob/master/03-transactions.md, https://github.com/lightning/bolts/blob/master/05-onchain.md#revoked-transaction-close-handling; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: VerifyScript, EvalScript, CheckSequence, IsFinalTx (src/script/interpreter.cpp, src/consensus/tx_verify.cpp); BIP68, BIP112, BIP141

import Definitions.Def_BitcoinToLocal
import Definitions.Def_BitcoinHtlc
import Definitions.Def_BitcoinAnchors
import Definitions.Def_BitcoinFunding
import Definitions.Def_BitcoinHtlcLocks

/-!
# The Lightning penalty: a revoked commitment transaction under Bitcoin's script interpreter

BOLT #3 (*Bitcoin Transaction and Script Formats*) and BOLT #5 (*Recommendations for On-chain
Transaction Handling*) rest on one mechanism: when a party broadcasts a commitment transaction it
has already *revoked*, the counterparty, who learned the revocation secret, can spend every
output of that transaction at once with the revocation key, while the broadcaster itself is held
back by `to_self_delay` on its own balance. This file names the outputs of such a commitment
transaction, built from the script constructors of the `BitcoinToLocal`, `BitcoinHtlc` and
`BitcoinAnchors` missions, and the two hypotheses on the interpreter's signature oracle under
which the penalty is stated:

* `HoldsRevocation o K`: the oracle accepts some (witness-sized) signature for the revocation
  public key `revPk`, and `hash160 revPk` is the hash `revHash` the HTLC scripts carry — the
  honest party's side.
* `NoRevocationSig o K`: the oracle accepts *no* signature for `revPk` — the cheater's side, an
  unforgeability hypothesis on the oracle for this one key. `NoRevHashPreimage o K` adds that
  `revPk` is the only byte string hashing to `revHash` (second-preimage resistance of `hash160`
  at `revPk`), which the HTLC scripts need since they check the hash of the pushed key.

The oracle is abstract (`BitcoinScript.Oracle`); the `*_p2wsh_spend` theorems of the sibling
missions instantiate it with `BitcoinSig.legacyOracle` on the spending transaction, the input
index, the amount and the witness script (`oracleOf`). Witnesses are listed in `CScriptWitness`
order (last element on top of the stack, the script last), as `BitcoinVerify.verifyScript` takes
them.
-/

namespace BitcoinPenalty

open BitcoinScript BitcoinSig BitcoinVerify BitcoinToLocal

/-- The keys and parameters of one commitment transaction, as seen from the party that
broadcasts it ("local"): the revocation key and its `hash160`, the delayed key of `to_local`, the
`to_remote` key, the two HTLC keys, the two funding keys (the anchors' keys) and `to_self_delay`. -/
structure CommitmentKeys where
  revPk : Bytes
  revHash : Bytes
  localDelayedPk : Bytes
  remoteKey : Bytes
  localHtlcKey : Bytes
  remoteHtlcKey : Bytes
  fundingKeyLocal : Bytes
  fundingKeyRemote : Bytes
  toSelfDelay : Int

/-- One HTLC output's parameters: the (`hash160`) payment hash and the `cltv_expiry`. -/
structure Htlc where
  payHash : Bytes
  expiry : Int

/-- The size and range hypotheses of the sibling missions' theorems: every pushed string fits a
stack element (`MAX_SCRIPT_ELEMENT_SIZE = 520`) and `to_self_delay` is a plain block count below
`2 ^ 16` (no sequence-lock flag bits). -/
structure WellFormed (K : CommitmentKeys) : Prop where
  revPk : K.revPk.length ≤ MAX_SCRIPT_ELEMENT_SIZE
  revHash : K.revHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE
  localDelayedPk : K.localDelayedPk.length ≤ MAX_SCRIPT_ELEMENT_SIZE
  remoteKey : K.remoteKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE
  localHtlcKey : K.localHtlcKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE
  remoteHtlcKey : K.remoteHtlcKey.length ≤ MAX_SCRIPT_ELEMENT_SIZE
  fundingKeyLocal : K.fundingKeyLocal.length ≤ MAX_SCRIPT_ELEMENT_SIZE
  fundingKeyRemote : K.fundingKeyRemote.length ≤ MAX_SCRIPT_ELEMENT_SIZE
  delayNonneg : 0 ≤ K.toSelfDelay
  delayLt : K.toSelfDelay < 2 ^ 16

/-- The size and range hypotheses on one HTLC: the payment hash fits a stack element and the
expiry is a 5-byte script number. -/
structure HtlcWellFormed (h : Htlc) : Prop where
  payHash : h.payHash.length ≤ MAX_SCRIPT_ELEMENT_SIZE
  expiry : h.expiry.natAbs < 2 ^ 32

/-! ### The outputs of the commitment transaction (witness scripts as `CScript` bytes) -/

/-- `to_local`: `BitcoinToLocal.toLocalBytes revPk to_self_delay localDelayedPk`. -/
def toLocalBytes (K : CommitmentKeys) : Bytes :=
  BitcoinToLocal.toLocalBytes K.revPk K.toSelfDelay K.localDelayedPk

/-- An offered HTLC (non-anchor form). -/
def offeredBytes (K : CommitmentKeys) (h : Htlc) : Bytes :=
  BitcoinHtlc.offeredBytes K.revHash K.remoteHtlcKey K.localHtlcKey h.payHash

/-- A received HTLC (non-anchor form). -/
def receivedBytes (K : CommitmentKeys) (h : Htlc) : Bytes :=
  BitcoinHtlc.receivedBytes K.revHash K.remoteHtlcKey K.localHtlcKey h.payHash h.expiry

/-- An offered HTLC with `option_anchors`. -/
def offeredBytesAnchors (K : CommitmentKeys) (h : Htlc) : Bytes :=
  BitcoinAnchors.offeredBytes K.revHash K.remoteHtlcKey K.localHtlcKey h.payHash

/-- A received HTLC with `option_anchors`. -/
def receivedBytesAnchors (K : CommitmentKeys) (h : Htlc) : Bytes :=
  BitcoinAnchors.receivedBytes K.revHash K.remoteHtlcKey K.localHtlcKey h.payHash h.expiry

/-- `to_remote` with `option_anchors` (`<remote_pubkey> OP_CHECKSIGVERIFY 1 OP_CHECKSEQUENCEVERIFY`). -/
def toRemoteBytes (K : CommitmentKeys) : Bytes := BitcoinAnchors.toRemoteBytes K.remoteKey

/-- The broadcaster's anchor (keyed by its funding key). -/
def anchorLocalBytes (K : CommitmentKeys) : Bytes := BitcoinAnchors.anchorBytes K.fundingKeyLocal

/-- The counterparty's anchor (keyed by its funding key). -/
def anchorRemoteBytes (K : CommitmentKeys) : Bytes := BitcoinAnchors.anchorBytes K.fundingKeyRemote

/-- The P2WSH output script paying to a witness script: `OP_0 <SHA256(script)>`. -/
def p2wshOf (script : Bytes) : Bytes := witnessBytes 0 (BitcoinSer.sha256 script)

/-- The concrete oracle under which `verifyScript` runs a version-0 witness script `script` in
the verification context `c` (what the `*_p2wsh_spend` theorems instantiate). -/
def oracleOf (c : Ctx) (script : Bytes) : Oracle :=
  legacyOracle (sigFlagsOf c.flags) c.tx c.nIn c.amount .witnessV0 script

/-! ### The two sides of the penalty -/

/-- The honest party holds the revocation key: the oracle accepts some signature `sigR` (of
witness-element size) for `revPk`, and `revPk` hashes to the `revHash` of the HTLC scripts. -/
def HoldsRevocation (o : Oracle) (K : CommitmentKeys) : Prop :=
  (∃ sigR, sigR.length ≤ MAX_SCRIPT_ELEMENT_SIZE ∧ o.checkSig sigR K.revPk = some true) ∧
  o.hash160 K.revPk = K.revHash

/-- The cheater has no signature for the revocation key: the oracle accepts none. -/
def NoRevocationSig (o : Oracle) (K : CommitmentKeys) : Prop :=
  ∀ sig, o.checkSig sig K.revPk ≠ some true

/-- `revPk` is the only byte string the oracle hashes to `revHash`. -/
def NoRevHashPreimage (o : Oracle) (K : CommitmentKeys) : Prop :=
  ∀ pk, o.hash160 pk = K.revHash → pk = K.revPk

/-! ### The penalty witnesses (`CScriptWitness` order, script last) -/

/-- The `to_local` penalty witness `<revocation_sig> 1 <witness_script>`. -/
def toLocalPenaltyWitness (K : CommitmentKeys) (sigR : Bytes) : List Bytes :=
  [sigR, [1], toLocalBytes K]

/-- An HTLC penalty witness `<revocation_sig> <revocationpubkey> <witness_script>`. -/
def htlcPenaltyWitness (K : CommitmentKeys) (sigR script : Bytes) : List Bytes :=
  [sigR, K.revPk, script]

/-! ### The paths left to the cheater -/

/-- `BitcoinToLocal.SpendCondition` without its revocation path: `b` false, the delay check
passing and `sig` valid for the delayed key. -/
def DelayedSpend (f : Flags) (o : Oracle) (K : CommitmentKeys) (b sig : Bytes) : Prop :=
  castToBool b = false ∧ CsvPasses f o K.toSelfDelay ∧ o.checkSig sig K.localDelayedPk = some true

/-- `BitcoinHtlc.OfferedSpend` without its revocation path: the preimage path or the timeout path. -/
def OfferedNonRevocation (f : Flags) (o : Oracle) (K : CommitmentKeys) (h : Htlc) (st : List Bytes) : Prop :=
  (∃ preimage sig, st = [preimage, sig] ∧ o.hash160 preimage ≠ K.revHash ∧ preimage.length = 32 ∧
      o.hash160 preimage = h.payHash ∧ o.checkSig sig K.remoteHtlcKey = some true) ∨
  (∃ x localSig remoteSig dummy, st = [x, localSig, remoteSig, dummy] ∧ o.hash160 x ≠ K.revHash ∧ x.length ≠ 32 ∧
      multisigLoop o [localSig, remoteSig] [K.localHtlcKey, K.remoteHtlcKey] = some true ∧
      (f.nulldummy = true → dummy = []))

/-- `BitcoinHtlc.ReceivedSpend` without its revocation path: the success path or the timeout path. -/
def ReceivedNonRevocation (f : Flags) (o : Oracle) (K : CommitmentKeys) (h : Htlc) (st : List Bytes) : Prop :=
  (∃ preimage localSig remoteSig dummy, st = [preimage, localSig, remoteSig, dummy] ∧
      o.hash160 preimage ≠ K.revHash ∧ preimage.length = 32 ∧ o.hash160 preimage = h.payHash ∧
      multisigLoop o [localSig, remoteSig] [K.localHtlcKey, K.remoteHtlcKey] = some true ∧
      (f.nulldummy = true → dummy = [])) ∨
  (∃ x sig, st = [x, sig] ∧ o.hash160 x ≠ K.revHash ∧ x.length ≠ 32 ∧ BitcoinHtlc.CltvPasses f o h.expiry ∧
      o.checkSig sig K.remoteHtlcKey = some true)

/-- `BitcoinAnchors.OfferedSpend` without its revocation path: `OfferedNonRevocation` with the
one-block delay check on both paths. -/
def OfferedNonRevocationAnchors (f : Flags) (o : Oracle) (K : CommitmentKeys) (h : Htlc) (st : List Bytes) : Prop :=
  OfferedNonRevocation f o K h st ∧ CsvPasses f o 1

/-- `BitcoinAnchors.ReceivedSpend` without its revocation path: `ReceivedNonRevocation` with the
one-block delay check on both paths. -/
def ReceivedNonRevocationAnchors (f : Flags) (o : Oracle) (K : CommitmentKeys) (h : Htlc) (st : List Bytes) : Prop :=
  ReceivedNonRevocation f o K h st ∧ CsvPasses f o 1

end BitcoinPenalty


