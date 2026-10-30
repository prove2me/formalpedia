-- Prove2me | Definitions.Def_BitcoinUniqueness
-- name    : BitcoinUniqueness
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T13:46:48.224911+00:00
-- url     : https://prove2.me/theorems/7fddff20-47c0-4819-8c16-94c56171642e
-- title:
--   The BIP30 scan condition, freshness of a block's outputs, and the coinbase scriptSig
-- statement:
--   Three names over the block mission's `BitcoinBlockV2` and the reorganization mission's `BitcoinReorg`; nothing is re-transcribed.
--
--   **`coinbaseScriptSig b`** — the `scriptSig` of the first input of the first transaction of a block (defaults: the genesis coinbase, an empty input).
--
--   **`ScanRuns S b`** — `ConnectBlock` performs the BIP30 scan when connecting `b` to `S`: `fEnforceBIP30 || nHeight >= BIP34_IMPLIES_BIP30_LIMIT`, i.e. the block mission's `bip30Checked` at the next height and the block's hash.
--
--   **`FreshOutputs u b`** — for every transaction of `b` and every output index below its output count, the ledger `u` holds no coin at that outpoint.
--
--   **Formalization Note.** `validate`, `Reachable`, `heightScript` (`CScript() << nHeight`), `bip30Checked`, `isBIP30Repeat` are the block mission's; `connectChain` is the reorganization mission's; `pushBytes` is the signature mission's push encoder and `serialize` the Script mission's `CScriptNum::serialize`. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock (fEnforceBIP30, BIP34_IMPLIES_BIP30_LIMIT), ContextualCheckBlock (the BIP34 height push), src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CScript::push_int64, CScriptNum::serialize (script/script.h); BIP30, BIP34

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinReorg

/-!
# Transaction uniqueness: BIP30 and BIP34

Two transactions with the same identifier would let a block overwrite coins that already exist,
which is what the undo data cannot restore. BIP30 forbids a block from creating a coin at an
outpoint that already has one; its scan is skipped once the BIP34 activation block is an ancestor
(until height 1,983,702), because BIP34 makes every coinbase start with a push of its height, and
a height push is never a prefix of another. This file names the quantities those two rules speak
about, so that the theorems can say exactly what validation guarantees where the scan runs and
what the height rule guarantees where it does not.
-/

namespace BitcoinUniqueness

open BitcoinSer BitcoinBlockV2

/-- The `scriptSig` of a block's coinbase (its first transaction's first input). -/
def coinbaseScriptSig (b : Block) : Bytes :=
  ((b.vtx.headD genesisCoinbase).vin.headD ⟨⟨[], 0⟩, [], 0, []⟩).scriptSig

/-- The BIP30 scan runs when `ConnectBlock` connects `b` to `S` (`fEnforceBIP30 || nHeight >=
BIP34_IMPLIES_BIP30_LIMIT`). -/
def ScanRuns (S : ChainState) (b : Block) : Prop :=
  bip30Checked S S.nextHeight (headerHash b.header) = true

/-- Freshness of a block against a ledger, over the output indices the block creates: no outpoint
of any of its transactions already holds a coin. -/
def FreshOutputs (u : Ledger) (b : Block) : Prop :=
  ∀ tx ∈ b.vtx, ∀ o, o < tx.vout.length → getCoin u ⟨txid tx, o⟩ = none

end BitcoinUniqueness


