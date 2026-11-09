-- Prove2me | Definitions.Def_DoublyEffIP_DecidesWithin
-- name    : DoublyEffIP_DecidesWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:17:25.573848+00:00
-- url     : https://prove2.me/theorems/dbd36433-d278-4759-96d2-c585442782d9
-- title:
--   Deciding within time $\tau$ and space $s$
-- statement:
--   A machine $M$ **decides** the input $w$ with answer $b$ **within time $\tau$ and space $s$** if it halts on $w$ after some $t\le\tau$ steps in answer state $b$, and every configuration reached in those $t$ steps has visited at most $s$ tape cells in total, over all tapes.
--
--   **Formalization Note** The count includes the input tape (and at least one cell of every tape). This is the paper's convention: the proof of Theorem 5 treats "the start state with $x$ as input" as a configuration in $\{0,1\}^S$. In particular a machine on inputs of length $n$ uses space at least $\max(n,1)$.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3, p.8 (TISP); proof of Theorem 5, p.15

import Mathlib
import Definitions.Def_DoublyEffIP_HaltsAt

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace DoublyEffIP

/-- **Deciding within time `τ` and space `s`** — "decidable by a Turing machine in time T(n) and
space S(n)", Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), Section 3, p.8.

Started on `input`, the machine `M` halts after some `t ≤ τ` steps in the answer state `b`, and
every configuration reached within those `t` steps has visited at most `s` cells in total.

**Formalization Note.** `visitedSpace` (published `SubexponentialSAT`) counts the visited cells of
every tape, the input tape included, and at least one cell per tape. The paper's space counts the
input too: the proof of Theorem 5 (p.15) takes "the start state with x as input" as a
configuration in `{0,1}^S`. No `+|x|` allowance is added. -/
def DecidesWithin (M : PrimitiveMachine) (input : List Bool) (b : Bool) (τ s : ℕ) : Prop :=
  ∃ (t : ℕ) (final : LocatedCfg M), t ≤ τ ∧ HaltsAt M input t final ∧
    final.config.state = Sum.inl b ∧
    ∀ (k : ℕ) (c : LocatedCfg M), k ≤ t →
      Trace (locatedStep M) k (locatedInit M input) c → visitedSpace c ≤ s

end DoublyEffIP


