-- Prove2me | Definitions.Def_BitcoinSubsidy
-- name    : BitcoinSubsidy
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-26T04:33:04.875174+00:00
-- url     : https://prove2.me/theorems/93882714-422c-4ebd-aca2-67f8a75abc87
-- title:
--   Block subsidy, issuance schedule, and cumulative issuance
-- statement:
--   Amounts are counted in satoshi. One bitcoin is $\mathrm{COIN} = 10^{8}$ satoshi and $\mathrm{MAX\_MONEY} = 21{,}000{,}000 \cdot \mathrm{COIN} = 2.1 \times 10^{15}$ satoshi. The mainnet halving interval is $I = 210{,}000$ blocks.
--
--   The **Core subsidy** at a block height $h \in \mathbb N$ transcribes `GetBlockSubsidy` at mainnet parameters. With $k = \lfloor h / I \rfloor$ halvings, the subsidy is $0$ when $k \ge 64$, and otherwise the right shift $(50 \cdot \mathrm{COIN}) \gg k$. Heights are nonnegative in the source and the shifted value is nonnegative, so natural numbers represent both exactly; the explicit $k \ge 64$ branch mirrors the source's guard against an undefined shift.
--
--   The **declarative schedule** is
--   $$\mathrm{specSubsidy}(h) = \left\lfloor \frac{50 \cdot \mathrm{COIN}}{2^{\lfloor h / I \rfloor}} \right\rfloor ,$$
--   fifty bitcoin halved once per interval with the remainder discarded.
--
--   **Cumulative issuance** below height $n$ is the running sum $\mathrm{issuedBelow}(0) = 0$, $\mathrm{issuedBelow}(n+1) = \mathrm{issuedBelow}(n) + \mathrm{coreSubsidy}(n)$. The **interval sum** $\mathrm{intervalSum}(m) = \sum_{j<m} \lfloor 50 \cdot \mathrm{COIN} / 2^{j} \rfloor$ collects one subsidy per interval. The **zero height** is $33 I = 6{,}930{,}000$, the first height whose subsidy the theorems show to be zero.
--
--   These definitions are the inputs for the issuance theorems and for any later ledger-supply argument, which will cite the cumulative issuance as its upper bound.
--
--   **Formalization Note.** All quantities are natural numbers. The shift is Lean's `>>>` on `Nat`, which is exact division by a power of two; the recursive definitions are structural so that proofs proceed by induction on height or interval count. Only `Std` is imported.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48, GetBlockSubsidy, src/validation.cpp lines 1833-1844: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/validation.cpp#L1833; COIN and MAX_MONEY, src/consensus/amount.h: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/consensus/amount.h; nSubsidyHalvingInterval = 210000, CMainParams, src/kernel/chainparams.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/kernel/chainparams.cpp

import Std

namespace BitcoinSubsidy

/-- `consensus/amount.h`: `COIN{100'000'000}`, the number of satoshis in one bitcoin. -/
def COIN : Nat := 100000000

/-- `consensus/amount.h`: `MAX_MONEY{21'000'000 * COIN}`, the consensus sanity bound on amounts. -/
def MAX_MONEY : Nat := 21000000 * COIN

/-- `kernel/chainparams.cpp`, `CMainParams`: `consensus.nSubsidyHalvingInterval = 210000`. -/
def halvingInterval : Nat := 210000

/-- Transcription of `GetBlockSubsidy` (`validation.cpp`) at mainnet parameters.
Block heights are nonnegative, and the `CAmount` right shift `nSubsidy >>= halvings` acts on the
nonnegative value `50 * COIN`, so it is division by `2 ^ halvings`; the source returns `0`
outright once `halvings >= 64`, where the C++ shift would be undefined. -/
def coreSubsidy (height : Nat) : Nat :=
  let halvings := height / halvingInterval
  if 64 ≤ halvings then 0 else (50 * COIN) >>> halvings

/-- Declarative issuance schedule: fifty bitcoin, halved once per `halvingInterval` blocks. -/
def specSubsidy (height : Nat) : Nat := (50 * COIN) / 2 ^ (height / halvingInterval)

/-- Total subsidy of all blocks at heights `0, 1, …, n - 1`, as `GetBlockSubsidy` computes it. -/
def issuedBelow : Nat → Nat
  | 0 => 0
  | n + 1 => issuedBelow n + coreSubsidy n

/-- Sum of the per-interval subsidies for the first `m` intervals. -/
def intervalSum : Nat → Nat
  | 0 => 0
  | m + 1 => intervalSum m + (50 * COIN) / 2 ^ m

/-- The first height whose subsidy is zero: thirty-three halvings. -/
def zeroHeight : Nat := 33 * halvingInterval

end BitcoinSubsidy


