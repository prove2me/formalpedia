-- Prove2me | Definitions.Def_OnlineBinCover_Supplement_OrderOblivious
-- name    : OnlineBinCover_Supplement_OrderOblivious
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:35:23.102667+00:00
-- url     : https://prove2.me/theorems/2e77c1c2-3b91-47b5-9c29-44676d8448d0
-- title:
--   The order-oblivious protocol on the real RAM
-- statement:
--   An **order-oblivious** algorithm ([AKW14]) has two phases. In the sampling phase it observes the first $k$ items of a uniformly random permutation and discards them; $k$ is chosen before any item is observed, from information supplied in advance ($n$ and an estimate $B$ of $\mathrm{OPT}(I)$). In the assignment phase it processes the remaining items online, and its guarantee must hold for every order of these items. Discarded items go to a separate bin that never counts, even if covered (footnote 2).
--
--   On the real RAM: the initial memory holds the integers $n,k$ and the real $B$; all $n$ items are fed one at a time in an arrival order $\pi$ (item $\pi(t)$ at time $t$), each run for $F$ steps and labelled by integer cell $-1$. The value
--
--   $$A_{oo}(I;n,B)=\#\{\text{bins covered by the items arriving at times }k,\dots,n-1\}$$
--
--   ignores the labels given to the first $k$ arrivals.
--
--   **Formalization Note** The count is the base mission's `coveredOn` over the complement of `smp π k`, the set of the first $k$ arrivals.
-- source:
--   Ayyadevara, Khan, Kumar, Sreenivas, Optimal Online Bin Covering across Stochastic Models, STOC 2027 submission (manuscript sha256 e77e556c…), §1.1, p.4 (PDF p.5), definition of an order-oblivious algorithm and footnote 2

import Mathlib
import Definitions.Def_OnlineBinCover_Supplement_AoS

namespace OnlineBinCover.Supplement

/-!
# The order-oblivious protocol on the real RAM

Ayyadevara, Khan, Kumar, Sreenivas, *Optimal Online Bin Covering across Stochastic Models*,
STOC 2027 submission (manuscript sha256 e77e556c…), §1.1 p.4 (PDF p.5), the definition of an
order-oblivious algorithm ([AKW14]) with footnote 2, and Theorem 1.2.

The paper: "In the sampling phase, it observes the first `k` items of a uniformly random
permutation and discards them. The length `k` is chosen before observing any items, … using …
information supplied in advance, such as `n` or an estimate of `OPT(I)`. In the assignment phase,
it processes the remaining items online. Its performance guarantee holds for every ordering of
these remaining items, including an order chosen after the sample is revealed." Footnote 2: "The
algorithm places all discarded items in a separate bin. This bin does not count toward the
objective value, even if it is covered."

**Formalization Note.**
* *Advance information.* Integer cells `0, 1` hold `n` and the sampling length `k`; real cell `0`
  holds `B`; every other cell is `0`. In theorems `k` is a fixed function of `n` and `B` only,
  chosen before any item is seen.
* *Arrival.* The arrival order is a permutation `π` of the labels (item `π t` arrives at time
  `t`); theorems require its first `k` positions to be those of a uniform `σ` and let an adversary
  choose the rest. All `n` items are fed with the published `feedLoad` from the initial state
  (`feedFrom`), `F` steps each; item `π t`'s label is integer cell `−1` after its run.
* *Objective.* `ooValue` counts the bins covered by the items at positions `≥ k` only (the
  published `coveredOn` over the complement of `smp π k`); the labels the program gives to the
  sampled items never count, whatever they are.
-/

open Finset

/-- The order-oblivious initial state: integer memory `[n, k]`, real memory `[B]`. -/
noncomputable def ooInit (n k : ℕ) (B : ℝ) : PNormReg.State :=
  PNormReg.initState [(n : ℤ), (k : ℤ)] [B]

/-- The state after the first `t` arrivals of the arrival order `π`. -/
noncomputable def ooState (P : PNormReg.Program) (F k : ℕ) (B : ℝ) {n : ℕ} (s : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) (t : ℕ) : PNormReg.State :=
  feedFrom P F (ooInit n k B) (List.ofFn (s ∘ π)) t

/-- `A_oo(I; n, B)` on the arrival order `π` with sampling length `k`: the bins covered by the
items arriving at times `k, …, n − 1`, each labelled by integer cell `−1` after its run. -/
noncomputable def ooValue (P : PNormReg.Program) (F k : ℕ) (B : ℝ) {n : ℕ} (s : Fin n → ℝ)
    (π : Equiv.Perm (Fin n)) : ℕ :=
  coveredOn s (Finset.univ \ smp π k)
    (fun i => (ooState P F k B s π ((π.symm i : ℕ) + 1)).integerMemory (-1))

end OnlineBinCover.Supplement


