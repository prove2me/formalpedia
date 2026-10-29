-- Prove2me | Definitions.Def_BitcoinReorg
-- name    : BitcoinReorg
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T01:24:17.97252+00:00
-- url     : https://prove2.me/theorems/d49ab644-37c9-4e07-bff6-c39a662893e7
-- title:
--   Chains of blocks connected and disconnected: state equivalence, connectChain, disconnectChain, the freshness conditions, consistency
-- statement:
--   Six names over the block mission's `BitcoinBlockV2`; nothing is re-transcribed.
--
--   **`StateEquiv S T`** — two chain states with the same header list whose ledgers hold the same coin at every outpoint (`getCoin` agrees everywhere; the association lists may differ in order).
--
--   **`connectChain S bs`** — connect the blocks of `bs` in order, each with its own clock reading, through the block mission's `validate`; `none` if any block is not accepted, else the final state and the list of the blocks' undo data (`CBlockUndo` of each, in connection order).
--
--   **`disconnectTip S b undo`** — `DisconnectBlock` on `S.utxo` at the tip's height with `b`'s hash and undo data, then the tip header popped; `none` is `DISCONNECT_FAILED`, the flag is `DISCONNECT_OK` (clean) versus `DISCONNECT_UNCLEAN`.
--
--   **`disconnectChain S l`** — `disconnectTip` for each (block, undo) pair of `l` in the order given (the tip first), the flags conjoined.
--
--   **`FreshChain S bs`** — the side conditions under which undo data restores a ledger exactly, continued along the states each accepted block produces: the txids within each block are distinct, no txid of the block already has a coin in the ledger it is connected to (the BIP30 condition, which `ConnectBlock` enforces only where its scan runs), and the block does not hash to the genesis hash.
--
--   **`Consistent S`** — `S` is `StateEquiv` to some state reachable from the genesis.
--
--   **Formalization Note.** `validate`, `disconnectBlock`, `Reachable`, `Equiv`, `updateCoins`, `connectBlock` are the block mission's. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: ConnectBlock, DisconnectBlock, UpdateCoins, ApplyTxInUndo, Chainstate::ConnectTip, Chainstate::DisconnectTip, Chainstate::ActivateBestChainStep, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CCoinsViewCache (coins.cpp)

import Definitions.Def_BitcoinBlockV2

/-!
# Reorganizations

A node that learns of a better chain disconnects blocks from its tip, restoring the UTXO set from
the undo data it recorded when it connected them, and then connects the blocks of the new branch.
`DisconnectBlock` and `ConnectBlock` are the block mission's; this file names the sequences — a
chain of blocks connected in order with one clock reading each, a chain disconnected from the tip
with the recorded undo data — and the relation under which two chain states are the same up to
the order of their ledgers, so that the theorems can say: the state a reorganization produces is,
up to that order, a state reachable from the genesis by direct validation.
-/

namespace BitcoinReorg

open BitcoinSer BitcoinBlockV2

/-- Two chain states with the same headers whose ledgers hold the same coin at every outpoint. -/
def StateEquiv (S T : ChainState) : Prop := S.headers = T.headers ∧ Equiv S.utxo T.utxo

/-- Connect blocks in order, each with its clock reading; the undo data of every block is kept.
`none` if any block is not accepted. -/
def connectChain : ChainState → List (Block × Int) → Option (ChainState × List BlockUndo)
  | S, [] => some (S, [])
  | S, (b, now) :: rest =>
    match validate S b now with
    | .accept S' undo =>
      match connectChain S' rest with
      | none => none
      | some (T, undos) => some (T, undo :: undos)
    | _ => none

/-- Disconnect the tip block `b` with its undo data: `DisconnectBlock` on the ledger at the tip's
height and hash, and the header popped. The flag is `DISCONNECT_OK` versus `DISCONNECT_UNCLEAN`. -/
def disconnectTip (S : ChainState) (b : Block) (undo : BlockUndo) : Option (ChainState × Bool) :=
  match disconnectBlock S.utxo S.tipHeight (headerHash b.header) b undo with
  | none => none
  | some (u, clean) => some (⟨S.headers.dropLast, u⟩, clean)

/-- Disconnect blocks from the tip, in the order given (the tip block first). -/
def disconnectChain : ChainState → List (Block × BlockUndo) → Option (ChainState × Bool)
  | S, [] => some (S, true)
  | S, (b, undo) :: rest =>
    match disconnectTip S b undo with
    | none => none
    | some (S', clean) =>
      match disconnectChain S' rest with
      | none => none
      | some (T, c) => some (T, clean && c)

/-- The side conditions under which undo data restores a ledger exactly, along a chain: every
block's txids are distinct, none of them already has a coin in the ledger it is connected to
(the BIP30 condition, which `ConnectBlock` enforces only where its scan runs), and no block
hashes to the genesis hash; the condition continues from the state each block produces. -/
def FreshChain : ChainState → List (Block × Int) → Prop
  | _, [] => True
  | S, (b, now) :: rest =>
    (b.vtx.map txid).Nodup ∧ (∀ tx ∈ b.vtx, ∀ o, getCoin S.utxo ⟨txid tx, o⟩ = none) ∧
    headerHash b.header ≠ genesisHash ∧
    ∀ S' undo, validate S b now = .accept S' undo → FreshChain S' rest

/-- A chain state that is, up to the order of its ledger, reachable from the genesis. -/
def Consistent (S : ChainState) : Prop := ∃ S₀, Reachable S₀ ∧ StateEquiv S S₀

end BitcoinReorg


