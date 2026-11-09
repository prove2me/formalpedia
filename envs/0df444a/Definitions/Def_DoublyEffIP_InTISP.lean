-- Prove2me | Definitions.Def_DoublyEffIP_InTISP
-- name    : DoublyEffIP_InTISP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:18:04.091016+00:00
-- url     : https://prove2.me/theorems/53e7a2f9-51f7-47be-888a-16c7a7ffd8c1
-- title:
--   The class $\mathrm{TISP}(T,S)$
-- statement:
--   Let $T,S:\mathbb N\to\mathbb N$. A language $L\subseteq\{0,1\}^*$ belongs to $\mathrm{TISP}(T,S)$ if there is one machine $M$ such that for every input $x$ of length $n$, $M$ decides $x$ within time $T(n)$ and space $S(n)$, with answer $1$ when $x\in L$ and answer $0$ when $x\notin L$.
--
--   This is the class of languages "decidable by a Turing machine in time $T(n)$ and space $S(n)$" to which the paper's interactive proofs apply.
--
--   **Formalization Note** Machines are the published multitape `PrimitiveMachine`s; space counts every tape, the input included.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3, p.8

import Mathlib
import Definitions.Def_DoublyEffIP_DecidesWithin

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

namespace DoublyEffIP

/-- **The class `TISP(T, S)`** — Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*,
arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 3, p.8: "Denote by TISP(T, S)
the class of languages decidable by a Turing machine in time T(n) and space S(n)."

A language `L ⊆ {0,1}*` is in `TISP(T, S)` if one machine `M`, on every input `x` of length `n`,
halts within `T(n)` steps with answer `true` when `x ∈ L` and `false` when `x ∉ L`, using at most
`S(n)` cells.

**Formalization Note.** The machine is a published `SubexponentialSAT` `PrimitiveMachine`
(deterministic, multitape). Space counts every tape, input included (see `DecidesWithin`), so a
nonempty class forces `S(n) ≥ max(n, 1)`. -/
def InTISP (L : Set (List Bool)) (T S : ℕ → ℕ) : Prop :=
  ∃ M : PrimitiveMachine, ∀ x : List Bool,
    (x ∈ L → DecidesWithin M x true (T x.length) (S x.length)) ∧
    (x ∉ L → DecidesWithin M x false (T x.length) (S x.length))

end DoublyEffIP


