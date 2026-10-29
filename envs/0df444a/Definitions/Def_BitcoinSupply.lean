-- Prove2me | Definitions.Def_BitcoinSupply
-- name    : BitcoinSupply
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-28T23:49:39.469468+00:00
-- url     : https://prove2.me/theorems/13f74335-8684-47b2-b600-3dbb49c1895a
-- title:
--   The money supply of a chain state: the total value of the UTXO set, the issued subsidy, and the value-range invariant
-- statement:
--   Four names over the block mission's `BitcoinBlockV2` and the subsidy mission's `BitcoinSubsidy`; nothing is re-transcribed.
--
--   **`totalValue u`** — the sum of `nValue` over the coins of a ledger $u$ (an association list of outpoints and coins), as an integer.
--
--   **`ValuesInRange u`** — every coin of $u$ has `0 ≤ nValue ≤ MAX_MONEY` (the `MoneyRange` of `consensus/amount.h`).
--
--   **`issued n`** — `BitcoinSubsidy.issuedBelow n` as an integer: the sum of `GetBlockSubsidy` over heights $0, \dots, n-1$, i.e. the subsidy a chain of $n$ blocks has issued.
--
--   **`genesisSubsidy`** — `GetBlockSubsidy 0` as an integer, the fifty bitcoin of the genesis coinbase, which the source never adds to the UTXO set (`ConnectBlock`'s genesis shortcut; `CMainParams`).
--
--   **Formalization Note.** The chain state, the ledger, `updateCoins`, `validate` and `Reachable` are the block mission's; `coreSubsidy` and `issuedBelow` are the subsidy mission's. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockSubsidy, ConnectBlock (the coinbase bound), UpdateCoins, src/validation.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp; CheckTxInputs (consensus/tx_verify.cpp); CheckTransaction (consensus/tx_check.cpp); AddCoin, SpendCoin (coins.cpp); MAX_MONEY (consensus/amount.h)

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSubsidy

/-!
# The money supply as a chain invariant

`GetBlockSubsidy` bounds what each coinbase may create; `CheckTxInputs` requires every other
transaction to spend at least what it creates. Together they bound the total value of the UTXO
set of every chain state reachable from the genesis by the subsidy issued so far. This file names
the quantities the theorems speak about; the rules themselves are those of the block mission
(`BitcoinBlockV2`) and the subsidy mission (`BitcoinSubsidy`).
-/

namespace BitcoinSupply

open BitcoinBlockV2

/-- The total value of the coins of a ledger. -/
def totalValue : Ledger → Int
  | [] => 0
  | e :: rest => e.2.out.nValue + totalValue rest

/-- Every coin's value lies in `[0, MAX_MONEY]`. -/
def ValuesInRange (u : Ledger) : Prop :=
  ∀ e ∈ u, 0 ≤ e.2.out.nValue ∧ e.2.out.nValue ≤ MAX_MONEY

/-- The subsidy a chain of `n` blocks (heights `0..n-1`) has issued, as `GetBlockSubsidy` sums it. -/
def issued (n : Nat) : Int := (BitcoinSubsidy.issuedBelow n : Int)

/-- The genesis subsidy: its coinbase is not in the UTXO set (`CMainParams`, `ConnectBlock`'s
genesis shortcut), so it is issued but never spendable. -/
def genesisSubsidy : Int := (BitcoinSubsidy.coreSubsidy 0 : Int)

end BitcoinSupply


