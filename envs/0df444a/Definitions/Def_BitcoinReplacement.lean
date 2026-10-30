-- Prove2me | Definitions.Def_BitcoinReplacement
-- name    : BitcoinReplacement
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T14:04:39.121865+00:00
-- url     : https://prove2.me/theorems/13accbe6-bcae-4888-9654-ebe53f812f6a
-- title:
--   The fee rules of transaction replacement over an abstract mempool
-- statement:
--   An abstract mempool: no scripts, inputs or topology, only fees and sizes.
--
--   **`Tx`** — a (modified) fee in satoshi and a positive virtual size. **`FeeRate`** — Core's `FeePerVSize`: `fee` satoshi per `size` vbytes with `size > 0`; **`FeeRate.perKvB k`** is `CFeeRate(k)` $= k/1000$; **`DEFAULT_INCREMENTAL_RELAY_FEE`** $= 100$ (sat/kvB at this revision) and **`defaultIncrementalRelayFee`** its rate; **`MAX_REPLACEMENT_CANDIDATES`** $= 100$ (recorded, unused). **`FeeRate.getFee r v`** $= \lceil r.\text{fee} \cdot v / r.\text{size} \rceil$, computed as $(\text{fee} \cdot v + \text{size} - 1) / \text{size}$ in $\mathbb{N}$ (`CFeeRate::GetFee` = `FeePerVSize::EvaluateFeeUp`). **`Tx.feeRate`** is the exact fraction (fee, vsize); **`FeeRate.lt a b`** $\iff a.\text{fee} \cdot b.\text{size} < b.\text{fee} \cdot a.\text{size}$ and **`FeeRate.le`** likewise (`ByRatio`); **`Tx.feeRateQ`** $= \text{fee}/\text{vsize} \in \mathbb{Q}$.
--
--   **`Replacement`** — a new transaction, the multiset `evicted` of all entries it would remove (`all_conflicts`: direct conflicts and their descendants) and the sub-multiset `direct` of direct conflicts (`iters_conflicting`), with `direct ≤ evicted`. **`totalFee`, `totalVsize`** sum over a multiset.
--
--   **`PaysMoreThanConflicts R`** — every direct conflict's fee rate is strictly below the replacement's (`FeeRate.lt`), BIP125 rule 3 as implemented up to v29. **`PaysForRBF rate R`** — `totalFee evicted ≤ new.fee` and `rate.getFee new.vsize ≤ new.fee - totalFee evicted` (Core's `PaysForRBF`: at least the evicted fees, plus the incremental relay fee for the replacement's size). **`Valid rate R`** — both. **`IsChain rate t₀ [R₁, …, Rₙ]`** — each $R_i$ valid, $R_1$ evicts $t_0$, $R_{i+1}$ evicts $R_i$'s new transaction; **`chainEnd t₀ Rs`** is the last new transaction ($t_0$ for the empty chain); **`chainVsizes Rs`** the list of the new transactions' sizes.
--
--   **Formalization Note.** Imports Mathlib. `PaysForRBF` is transcribed from revision `a773e1e`; `PaysMoreThanConflicts` is absent there (replaced by the cluster-mempool feerate-diagram check, out of scope) and is transcribed from its last form (v29.0) with the exact `ByRatio` comparison of `a773e1e`. Fees are modified fees; structural rules, opt-in signalling, package relay and TRUC are not modelled; the eviction multiset is given, not computed from the mempool graph. The `getFee` of a zero-size or negative rate is not modelled.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: PaysForRBF (src/policy/rbf.cpp: https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/policy/rbf.cpp), CFeeRate::GetFee = FeePerVSize::EvaluateFeeUp (policy/feerate.cpp, util/feefrac.h), DEFAULT_INCREMENTAL_RELAY_FEE (policy/policy.h); PaysMoreThanConflicts as last present in policy/rbf.cpp at v29.0; BIP125

import Mathlib

/-!
# Bitcoin Core transaction replacement (BIP125 / RBF) — fee rules, abstract mempool model

This file transcribes the two *fee* rules that Bitcoin Core's `policy/rbf.cpp` imposes on a
replacement transaction, over an abstract mempool with no scripts, no inputs and no topology:

* a transaction is a pair (fee in satoshi, virtual size in vbytes) with positive vsize;
* a replacement is a new transaction together with the multiset of mempool entries it would evict
  (`all_conflicts` as `GetEntriesForConflicts` collects it: the directly conflicting entries
  `iters_conflicting` plus all their descendants) and the sub-multiset of direct conflicts;
* `PaysForRBF` (revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48`, `policy/rbf.cpp`) is
  transcribed verbatim, with `CFeeRate::GetFee` = `FeePerVSize::EvaluateFeeUp`, i.e. the exact
  ceiling `⌈fee · vsize / size⌉` of the configured incremental relay fee rate;
* `PaysMoreThanConflicts` (BIP125 rule 3) is transcribed from the last form in which it existed in
  `policy/rbf.cpp` (e.g. tag `v29.0`); at revision `a773e1e` that function has been removed and
  replaced by the cluster-mempool feerate-diagram check `ImprovesFeerateDiagram`, which is out of
  scope here.  Fee rates are compared as `CFeeRate::operator<=>` does at `a773e1e`, i.e. through
  `ByRatio` cross-multiplication `a.fee * b.size <=> b.fee * a.size`, with no rounding.

Fees are the mempool's *modified* fees (`GetModifiedFee`), which the model does not distinguish
from raw fees.  Nothing here models descendant/package relay, cluster linearisation, the
structural rules (no new unconfirmed inputs, cluster-count limit), or opt-in signalling.
-/

namespace BitcoinReplacement

/-- An abstract mempool transaction: its (modified) fee in satoshi and its virtual size in vbytes.
`CTxMemPoolEntry::GetTxSize()` is always positive, so the model records `0 < vsize`. -/
structure Tx where
  /-- Fee in satoshi (`CAmount`, nonnegative for a mempool entry). -/
  fee : ℕ
  /-- Virtual size in vbytes (`GetVirtualTransactionSize`). -/
  vsize : ℕ
  /-- Mempool entries have positive virtual size. -/
  vsize_pos : 0 < vsize
  deriving DecidableEq

/-- A fee rate as Bitcoin Core's `FeePerVSize` stores it at revision `a773e1e`: `fee` satoshi per
`size` vbytes, with `size > 0` (`CFeeRate(const FeePerVSize&)` maps a nonpositive size to the
empty rate, which `GetFee` treats as zero; the model only admits the positive-size case, which is
the one that is reached for a configured incremental relay fee rate). -/
structure FeeRate where
  /-- Numerator: satoshi. -/
  fee : ℕ
  /-- Denominator: vbytes. -/
  size : ℕ
  /-- `FeePerVSize::EvaluateFee` requires `size > 0`. -/
  size_pos : 0 < size

/-- `CFeeRate(const I m_feerate_kvb)` : a rate given in satoshi per 1000 vbytes is stored losslessly
as `FeePerVSize(m_feerate_kvb, 1000)`. -/
def FeeRate.perKvB (satPerKvB : ℕ) : FeeRate := ⟨satPerKvB, 1000, by norm_num⟩

/-- `policy/policy.h` at `a773e1e`: `DEFAULT_INCREMENTAL_RELAY_FEE{100}` (satoshi per kvB), the
default `-incrementalrelayfee`.  (Before PR #33106, i.e. up to and including v29.x, it was 1000.) -/
def DEFAULT_INCREMENTAL_RELAY_FEE : ℕ := 100

/-- The node's incremental relay fee rate at default settings:
`CFeeRate{DEFAULT_INCREMENTAL_RELAY_FEE}` = 100 sat per 1000 vB = 0.1 sat/vB. -/
def defaultIncrementalRelayFee : FeeRate := FeeRate.perKvB DEFAULT_INCREMENTAL_RELAY_FEE

/-- `policy/rbf.h`: `MAX_REPLACEMENT_CANDIDATES{100}`, the Rule #5 limit on the number of distinct
mempool clusters a replacement may touch (checked by `GetEntriesForConflicts`; not used by the fee
theorems). -/
def MAX_REPLACEMENT_CANDIDATES : ℕ := 100

/-- `CFeeRate::GetFee(v)` = `FeePerVSize::EvaluateFeeUp(v)` = `CeilDiv(fee * v, size)`, the fee for
`v` vbytes at this rate rounded *up* to the next satoshi: `⌈fee · v / size⌉`, computed in ℕ as
`(fee * v + (size - 1)) / size`.  (Only the `fee ≥ 0` branch of `EvaluateFee` is modelled; the
`IsEmpty` and negative-fee special cases of `GetFee` are unreachable for a positive-size,
nonnegative rate.) -/
def FeeRate.getFee (r : FeeRate) (v : ℕ) : ℕ := (r.fee * v + (r.size - 1)) / r.size

/-- `CFeeRate(nFeePaid, virtual_bytes)` for a mempool entry: with `virtual_bytes > 0` the rate is
the exact fraction `FeePerVSize(fee, vsize)`. -/
def Tx.feeRate (t : Tx) : FeeRate := ⟨t.fee, t.vsize, t.vsize_pos⟩

/-- `ByRatio` strict comparison of two fee rates, exactly as `CFeeRate::operator<=>` evaluates it:
`a < b` iff `a.fee * b.size < b.fee * a.size` (cross-multiplication in exact integer arithmetic,
no rounding). -/
def FeeRate.lt (a b : FeeRate) : Prop := a.fee * b.size < b.fee * a.size

/-- `ByRatio` non-strict comparison: `a ≤ b` iff `a.fee * b.size ≤ b.fee * a.size`. -/
def FeeRate.le (a b : FeeRate) : Prop := a.fee * b.size ≤ b.fee * a.size

/-- The fee rate of a transaction as an exact rational number of satoshi per vbyte, used only to
state that the `ByRatio` comparison is the ordinary comparison of fractions. -/
def Tx.feeRateQ (t : Tx) : ℚ := (t.fee : ℚ) / (t.vsize : ℚ)

/-- A candidate replacement, as the RBF checks see it (`MemPoolAccept::ReplacementChecks`):
the new transaction, the multiset `evicted` of all mempool entries that would be removed
(`all_conflicts` = direct conflicts plus all of their descendants), and the sub-multiset `direct`
of the directly conflicting entries (`iters_conflicting`).  Entries are recorded by their
(fee, vsize) data only, as a multiset so that distinct entries with equal data are not merged. -/
structure Replacement where
  /-- The replacement transaction. -/
  new : Tx
  /-- Every mempool entry the replacement would evict (`all_conflicts`). -/
  evicted : Multiset Tx
  /-- The directly conflicting entries (`iters_conflicting`). -/
  direct : Multiset Tx
  /-- `GetEntriesForConflicts` starts from `iters_conflicting`, so direct conflicts are evicted. -/
  direct_le : direct ≤ evicted

/-- `original_fees`: the total (modified) fee of a multiset of mempool entries, the quantity
`MemPoolAccept` sums over `all_conflicts` before calling `PaysForRBF`. -/
def totalFee (s : Multiset Tx) : ℕ := (s.map Tx.fee).sum

/-- Total virtual size of a multiset of transactions. -/
def totalVsize (s : Multiset Tx) : ℕ := (s.map Tx.vsize).sum

/-- BIP125 rule 3 as `PaysMoreThanConflicts` implemented it (`policy/rbf.cpp`, up to v29.x):
for every directly conflicting entry `mi`, with
`original_feerate = CFeeRate(mi->GetModifiedFee(), mi->GetTxSize())`, the replacement is rejected
when `replacement_feerate <= original_feerate`; so it passes iff every direct conflict's fee rate
is strictly below the replacement's, in the `ByRatio` order. -/
def PaysMoreThanConflicts (R : Replacement) : Prop :=
  ∀ t ∈ R.direct, FeeRate.lt t.feeRate R.new.feeRate

/-- `PaysForRBF(original_fees, replacement_fees, replacement_vsize, relay_fee, txid)` at
`a773e1e`, with `original_fees = totalFee R.evicted`, `replacement_fees = R.new.fee` and
`replacement_vsize = R.new.vsize`:
* Rule #3 (there): reject if `replacement_fees < original_fees`;
* Rule #4: `additional_fees = replacement_fees - original_fees`; reject if
  `additional_fees < relay_fee.GetFee(replacement_vsize)`.
The subtraction is performed only after the first check, so ℕ truncated subtraction agrees with
the `CAmount` subtraction. -/
def PaysForRBF (rate : FeeRate) (R : Replacement) : Prop :=
  totalFee R.evicted ≤ R.new.fee ∧
    rate.getFee R.new.vsize ≤ R.new.fee - totalFee R.evicted

/-- A replacement that passes both fee rules at incremental relay fee rate `rate`. -/
def Valid (rate : FeeRate) (R : Replacement) : Prop :=
  PaysMoreThanConflicts R ∧ PaysForRBF rate R

/-- `IsChain rate t₀ [R₁, …, Rₙ]`: a sequence of valid replacements in which `R₁` evicts `t₀` and
each `Rᵢ₊₁` evicts `Rᵢ.new`; so the network relays `R₁.new, …, Rₙ.new` in turn, each one
replacing the previous. -/
def IsChain (rate : FeeRate) : Tx → List Replacement → Prop
  | _, [] => True
  | t, R :: Rs => Valid rate R ∧ t ∈ R.evicted ∧ IsChain rate R.new Rs

/-- The last transaction of a replacement chain (`t₀` itself for the empty chain). -/
def chainEnd (t₀ : Tx) (Rs : List Replacement) : Tx :=
  Rs.foldl (fun _ R => R.new) t₀

/-- The virtual sizes of the replacement transactions of a chain, `vsize(t₁), …, vsize(tₙ)`. -/
def chainVsizes (Rs : List Replacement) : List ℕ := Rs.map fun R => R.new.vsize

end BitcoinReplacement


