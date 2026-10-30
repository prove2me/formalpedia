-- Prove2me | Definitions.Def_ConsensusHalvingItems_Additive_tick
-- name    : ConsensusHalvingItems_Additive_tick
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:21:31.536716+00:00
-- url     : https://prove2.me/theorems/8efe78b4-ae8a-4521-8419-4f36081607d4
-- title:
--   One tick of running time (bit-cost model)
-- statement:
--   The algorithms of this mission are programs that carry a **tick counter** $s \in \mathbb{N}$. The primitive $\mathsf{tick}(c)$ increases the counter by $c$:
--
--   $$
--   \mathsf{tick}(c) : s \mapsto s + c .
--   $$
--
--   The **running time** of a run started with counter $0$ is the final value of the counter. Every algorithm of the mission obeys one convention: each arithmetic operation or comparison on rationals is charged a cost quadratic in the bit sizes of its operands, each input value read is charged its bit size, every iteration of every loop ticks at least once, and the uncharged work between two ticks is index bookkeeping of size polynomial in $n + m$. Under this convention the counter is, up to a polynomial, the running time on a bit-level machine. The algorithms never read the counter, so the cost of a run does not depend on its starting value.
--
--   This is part of the cost model in which the mission reads "polynomial-time" in Theorem 2.2; the paper itself fixes no machine model.
--
--   **Formalization Note** The monad is `StateM ℕ` and `tick c` is `modify (· + c)`.
-- source:
--   Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, Consensus Halving for Sets of Items, arXiv:2007.06754v1, Theorem 2.2, p. 4 ("polynomial-time algorithm"); proof of Theorem 2.2, ¶2, p. 5

import Mathlib

namespace ConsensusHalvingItems.Additive

/-- **Charging `c` units of running time.**
Goldberg, Hollender, Igarashi, Manurangsi, Suksompong, *Consensus Halving for Sets of Items*,
arXiv:2007.06754v1, Theorem 2.2, p. 4 ("there exists a polynomial-time algorithm") and the proof
of Theorem 2.2, p. 5 ("can be done in polynomial time via Gaussian elimination").

The algorithms of this mission are programs in the state monad `StateM ℕ`, whose state is a tick
counter. `tick c` adds `c` to the counter. The running time of a run started at `0` is the
final value of the counter.

**Formalization Note.** The paper fixes no machine model; the mission reads "polynomial-time" in
the bit model (Reading 1 of the mission). The convention binding every algorithm of the mission:
every arithmetic operation or comparison on rationals goes through the ticked helpers `qadd`,
`qsub`, `qmul`, `qdiv`, `qlt`, `qeq`, which charge `opCost a b`, quadratic in the bit sizes
of the operands; every entry of the input is read through `uAt`, which charges its bit size;
every iteration of every loop and every recursive call ticks at least once; the unticked code
between two ticks does only index bookkeeping (list positions, `Fin m` indices, membership in a
set of at most `m` indices), whose cost is bounded by a polynomial in `n + m`, and never
computes with rational data. The algorithms never read the counter, so the cost of a run does
not depend on its start value. -/
def tick (c : ℕ) : StateM ℕ Unit := modify (· + c)

end ConsensusHalvingItems.Additive


