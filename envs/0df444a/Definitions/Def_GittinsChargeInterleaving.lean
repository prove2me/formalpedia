-- Prove2me | Definitions.Def_GittinsChargeInterleaving
-- name    : GittinsChargeInterleaving
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-07-31T21:08:00.018637+00:00
-- url     : https://prove2.me/theorems/2a8298d6-f008-4779-83d4-916ad2f034ba
-- title:
--   Gittins charge-stack interleavings
-- statement:
--   For a finite family of real-valued charge stacks, this module defines the pull count of each arm before a global round, the interleaving selected by an action sequence, and the predicate saying that every selected exposed charge is maximal. It also defines the finite prefix-allocation value and the two one-step transformations used in the induction proof.
--
--   For stacks $H_i=(H_{i,u})_{u\ge 0}$ and actions $a_0,a_1,\ldots$, the interleaved value at time $n$ is
--
--   $$
--   I_n(H,a)=H_{a_n,N_{a_n}(n)},\qquad
--   N_i(n)=\sum_{t<n}\mathbf 1\{a_t=i\}.
--   $$
--
--   These definitions isolate the deterministic reward-stack construction used in the Gittins-index interleaving argument.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms (free online edition), https://tor-lattimore.com/downloads/book/book.pdf, Section 35.4, printed p. 451 / PDF p. 459, definition of the interleaving I(g,a) immediately before Lemma 35.10.

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Finset.Interval

/-!
Deterministic reward-stack interleavings used in the proof of the Gittins
index theorem.  See Lattimore--Szepesvari, *Bandit Algorithms*, Lemma 35.10
and Exercise 35.9, printed p. 451 (free-online PDF p. 459).
-/

namespace BanditAlgorithm

/-- Number of occurrences of arm `i` strictly before global round `n`. -/
def stackPullCountBefore {k : ℕ} (a : ℕ → Fin k) (i : Fin k) (n : ℕ) : ℕ :=
  ∑ t ∈ Finset.range n, if a t = i then 1 else 0

/-- Interleave arm-indexed stacks according to the global action sequence. -/
def chargeStackInterleaving {k : ℕ}
    (H : Fin k → ℕ → ℝ) (a : ℕ → Fin k) (n : ℕ) : ℝ :=
  H (a n) (stackPullCountBefore a (a n) n)

/-- At every round, the selected arm has a maximal currently exposed charge. -/
def IsGreedyChargeStackInterleaving {k : ℕ}
    (H : Fin k → ℕ → ℝ) (a : ℕ → Fin k) : Prop :=
  ∀ n i,
    H i (stackPullCountBefore a i n) ≤
      H (a n) (stackPullCountBefore a (a n) n)

/-- Undiscounted value of taking the first `m i` entries from every stack. -/
def chargeStackAllocationValue {k : ℕ}
    (H : Fin k → ℕ → ℝ) (m : Fin k → ℕ) : ℝ :=
  ∑ i : Fin k, ∑ u ∈ Finset.range (m i), H i u

/-- Remove the exposed head of stack `j`. -/
def advanceChargeStack {k : ℕ}
    (H : Fin k → ℕ → ℝ) (j : Fin k) : Fin k → ℕ → ℝ :=
  fun i u ↦ if i = j then H i (u + 1) else H i u

/-- Remove one allocated entry from arm `i`. -/
def decrementChargeAllocation {k : ℕ}
    (m : Fin k → ℕ) (i : Fin k) : Fin k → ℕ :=
  fun j ↦ if j = i then m j - 1 else m j

end BanditAlgorithm


