-- Prove2me | Definitions.Def_BitcoinBackbone
-- name    : BitcoinBackbone
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T15:03:07.378647+00:00
-- url     : https://prove2.me/theorems/2a2cf47d-b4eb-4d6f-a7cf-0ea00405cd7e
-- title:
--   The synchronous backbone model: executions, valid chains, typical executions
-- statement:
--   The deterministic core of Garay, Kiayias and Leonardos's synchronous analysis, over Mathlib.
--
--   **`Block`** — `honest p r` (found by honest party $p$ in round $r$) or `adv r j` (the $j$-th adversarial block of round $r$); `Block.round`, `Block.isHonest`. **`Chain`** — a list of blocks oldest first (genesis omitted); `Chain.work` is its length; `Chain.upTo C t` the prefix of blocks of round $\le t$.
--
--   **`Execution`** — a trace: the number $n$ of honest parties, `mined p r` (whether $p$ found a block in round $r$), `Z r` (the adversary's block count in round $r$), `base p r` (the chain $p$ adopted at the start of round $r$ after `maxvalid`), `advParent r j` (the chain the adversary's $j$-th block of round $r$ extends). Derived: **`chain p r`** (the end-of-round chain: `base`, plus $p$'s own block if mined; the empty chain at round 0), **`honestCount r`**, **`X r`** (1 iff some honest block in round $r$), **`Y r`** (1 iff exactly one honest block in round $r$).
--
--   **`Extends E parent B`** and **`ValidChain E C`** — every block of $C$ sits on exactly the chain its creator extended (the hash-chain abstraction: a block determines its ancestry). **`Legal E`** — the rules of the synchronous model: nothing mined in round 0; adopted chains are valid and made of earlier rounds' blocks; every honest chain of round $r$ is at most as long as what any honest party adopts in round $r+1$ (`maxvalid` over delivered chains); the adversary extends valid chains of rounds $\le r$ (rushing). **`Typical E λ`** — on every window $[a, b]$ with $a + λ \le b$, the adversary's blocks in $[a, b]$ are strictly fewer than the uniquely successful rounds strictly inside $(a, b)$. **`advBlocks E a b`** — the adversarial blocks of rounds $a$ to $b$ as a finite set.
--
--   **Formalization Note.** Imports Mathlib and the block mission's `BitcoinBlockV2`. `Typical` is the paper's typical-execution property combined with honest majority, assumed rather than derived from Chernoff bounds; boundary rounds are credited to the adversary.
-- source:
--   J. Garay, A. Kiayias, N. Leonardos, The Bitcoin Backbone Protocol: Analysis and Applications, EUROCRYPT 2015 (full version ePrint 2014/765): https://eprint.iacr.org/2014/765; Lemmas 7, 14, 15, Theorem 16, the chain-quality theorem; Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: GetBlockProof (chain.cpp) through the block mission's chainWork

import Mathlib
import Definitions.Def_BitcoinBlockV2

/-!
# The Bitcoin backbone protocol: deterministic core of the synchronous analysis

This file models the *synchronous* ("rounds", `Δ = 1`) execution model of Garay, Kiayias and
Leonardos, *The Bitcoin Backbone Protocol: Analysis and Applications* (EUROCRYPT 2015, full version
ePrint 2014/765), with the proof-of-work abstracted by the paper's random-oracle counts:

* `X r` — successful round (at least one honest block found in round `r`),
* `Y r` — uniquely successful round (exactly one honest block found in round `r`),
* `Z r` — number of adversarial blocks found in round `r`.

A block records who created it and in which round (`Block.honest p r`, `Block.adv r j`); a chain
is a list of blocks, oldest first; extending a chain is appending.  The hash-chain structure of
Bitcoin (a block commits to all of its ancestors) is modelled by `ValidChain`: every block of a
valid chain sits on top of *exactly* the chain its creator was extending when it was found
(`base p r` for honest party `p` in round `r`, `advParent r j` for the `j`-th adversarial block of
round `r`).  Thus a block determines its ancestry, exactly as a hash does under collision
resistance, which is what the paper's "typical execution" assumes (no insertions/copies).

An `Execution` is the trace of one run: the number of honest parties, who mined when, the
adversary's block counts, the chain each honest party adopted at the start of each round (after
`maxvalid` over its own chain and the chains delivered to it, honest or adversarial), and the parent
chain of every adversarial block.  `Execution.Legal` lists the rules of the synchronous model
that the proofs rely on (every honest chain of round `r` reaches every honest party by round
`r + 1`; the chains adopted in round `r` consist of blocks found before round `r`; the adversary is
"rushing": its blocks of round `r` may extend anything found up to and including round `r`).

The probabilistic part of the paper is isolated in the hypothesis `Typical`: on every window of
at least `λ + 1` consecutive rounds the uniquely successful rounds strictly inside the window
outnumber all adversarial blocks of the window.  The paper derives this (with constants) from
Chernoff bounds and the honest-majority assumption; here it is simply assumed, and the theorems
state that *every* execution that is typical in this sense has chain growth, common prefix and
chain quality.
-/

namespace BitcoinBackbone

/-- A block of the abstract blockchain: either the block found by honest party `p` in round `r`
(an honest party finds at most one block per round, as the backbone protocol's `pow` stops after
the first success), or the `j`-th of the `Z r` blocks the adversary finds in round `r`. -/
inductive Block
  | honest (p : ℕ) (r : ℕ)
  | adv (r : ℕ) (j : ℕ)
  deriving DecidableEq, Repr

instance : Inhabited Block := ⟨Block.adv 0 0⟩

/-- The round in which a block was found. -/
def Block.round : Block → ℕ
  | .honest _ r => r
  | .adv r _ => r

/-- Whether a block was found by an honest party. -/
def Block.isHonest : Block → Bool
  | .honest _ _ => true
  | .adv _ _ => false

/-- A chain: the list of its blocks after the genesis, oldest first.  Extending a chain by a block
is `C ++ [B]`; the length of a chain is its (fixed-difficulty) work. -/
abbrev Chain := List Block

/-- The work of a chain in the fixed-difficulty model of the paper: its number of blocks. -/
def Chain.work (C : Chain) : ℕ := C.length

/-- The blocks of `C` found in round `t` or earlier.  For a valid chain (whose rounds are
nondecreasing, `round_mono` in the solutions) this is exactly the prefix of `C` older than `t`. -/
def Chain.upTo (C : Chain) (t : ℕ) : Chain := C.takeWhile (fun B => decide (B.round ≤ t))

/-- The trace of one execution of the backbone protocol in the synchronous model.

* `n`: the honest parties are `0, …, n - 1`.
* `mined p r`: honest party `p` found a block in round `r` (rounds are `1, 2, …`; round `0` is the
  initial state in which every party holds the empty chain, i.e. the genesis block only).
* `Z r`: the number of blocks the adversary found in round `r`.
* `base p r`: the chain honest party `p` adopted in round `r ≥ 1` before mining, i.e. the longest
  valid chain among its own chain and the chains delivered to it (honest broadcasts of round
  `r - 1` and whatever the adversary chose to deliver to `p`).  If `p` finds a block in round `r`
  it extends `base p r` by it and broadcasts the result (`chain p r`).
* `advParent r j`: the chain the adversary extended with its `j`-th block of round `r`. -/
structure Execution where
  n : ℕ
  mined : ℕ → ℕ → Bool
  Z : ℕ → ℕ
  base : ℕ → ℕ → Chain
  advParent : ℕ → ℕ → Chain

/-- The chain held (and broadcast) by honest party `p` at the end of round `r`: the chain it
adopted in round `r`, extended by its own block if it found one. -/
def Execution.chain (E : Execution) (p : ℕ) : ℕ → Chain
  | 0 => []
  | r + 1 =>
    if E.mined p (r + 1) = true then E.base p (r + 1) ++ [Block.honest p (r + 1)]
    else E.base p (r + 1)

/-- The number of honest blocks found in round `r`. -/
def Execution.honestCount (E : Execution) (r : ℕ) : ℕ :=
  ((Finset.range E.n).filter (fun p => E.mined p r = true)).card

/-- The paper's `X_r`: `1` if round `r` is successful (some honest party found a block), else `0`. -/
def Execution.X (E : Execution) (r : ℕ) : ℕ := if 0 < E.honestCount r then 1 else 0

/-- The paper's `Y_r`: `1` if round `r` is uniquely successful (exactly one honest block), else `0`. -/
def Execution.Y (E : Execution) (r : ℕ) : ℕ := if E.honestCount r = 1 then 1 else 0

/-- `B` legitimately extends `parent`: an honest block `honest p r` was found by honest party
`p < n` in round `r` on top of exactly `base p r`; an adversarial block `adv r j` is one of the
`Z r` blocks of round `r` and was found on top of exactly `advParent r j`. -/
def Execution.Extends (E : Execution) (parent : Chain) : Block → Prop
  | .honest p r => p < E.n ∧ E.mined p r = true ∧ parent = E.base p r
  | .adv r j => j < E.Z r ∧ parent = E.advParent r j

/-- A valid chain: every block sits on top of exactly the chain its creator extended.  This is the
abstract form of Bitcoin's hash chain (each block commits to its ancestry). -/
def Execution.ValidChain (E : Execution) (C : Chain) : Prop :=
  ∀ i (h : i < C.length), E.Extends (C.take i) C[i]

/-- The rules of the synchronous backbone model obeyed by a trace.

* `mined_zero`: nothing is mined in the initial round `0`.
* `base_valid`, `base_rounds`: the chain an honest party adopts in round `r` is valid and consists
  of blocks found in rounds `< r` (messages are delivered at the start of the next round).
* `base_length`: every honest party's chain of round `r` is received by every honest party by
  round `r + 1`, and honest parties adopt a longest chain (`maxvalid`); so what `p` adopts in round
  `r + 1` is at least as long as every honest chain of round `r` (its own included).
* `advParent_valid`, `advParent_rounds`: the adversary extends valid chains, made of blocks found
  in rounds `≤ r` when it works in round `r` (rushing adversary: it may build on the honest blocks
  of the current round). -/
structure Execution.Legal (E : Execution) : Prop where
  mined_zero : ∀ p, E.mined p 0 = false
  base_valid : ∀ p r, p < E.n → 1 ≤ r → E.ValidChain (E.base p r)
  base_rounds : ∀ p r, p < E.n → ∀ B ∈ E.base p r, B.round < r
  base_length : ∀ p q r, p < E.n → q < E.n → (E.chain q r).length ≤ (E.base p (r + 1)).length
  advParent_valid : ∀ r j, j < E.Z r → E.ValidChain (E.advParent r j)
  advParent_rounds : ∀ r j, j < E.Z r → ∀ B ∈ E.advParent r j, B.round ≤ r

/-- Typical execution with window parameter `λ` (deterministic form of the paper's Definition of a
typical execution combined with the honest-majority assumption): for every window `[a, b]` of at
least `λ + 1` consecutive rounds, the uniquely successful rounds strictly inside the window
outnumber all adversarial blocks found in the window, boundary rounds included.  (The two boundary
rounds are credited to the adversary because a rushing adversary may build on the honest block of
round `a` during round `a`, and may deliver blocks of round `b` in round `b`; the paper absorbs
these two rounds in the `(1 ± ε)` slack of its Chernoff bounds.) -/
def Execution.Typical (E : Execution) (lam : ℕ) : Prop :=
  ∀ a b : ℕ, a + lam ≤ b → (∑ i ∈ Finset.Icc a b, E.Z i) < ∑ i ∈ Finset.Ioo a b, E.Y i

/-- The adversarial blocks of rounds `a, …, b`, as a finite set of `Block`s (its cardinality is
`∑ i ∈ Icc a b, Z i`). -/
def Execution.advBlocks (E : Execution) (a b : ℕ) : Finset Block :=
  ((Finset.Icc a b).sigma (fun s => Finset.range (E.Z s))).image (fun x => Block.adv x.1 x.2)

end BitcoinBackbone


