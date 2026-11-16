-- Prove2me | Definitions.Def_StabTestMem_Supplement_IsNonAdaptive
-- name    : StabTestMem_Supplement_IsNonAdaptive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:38:17.424558+00:00
-- url     : https://prove2.me/theorems/345429c4-d715-4f72-a5d8-b2e30903326f
-- title:
--   Non-adaptive protocols with $k$ qubits of memory
-- statement:
--   A protocol with $k$ qubits of memory that consumes $t$ copies of an $n$-qubit state (Definition 3.7: at round $i$ it applies, to the fresh copy together with the memory, the instrument branch $T^{x_i}_{x_{<i}}$ selected by the history $x_{<i}$ of earlier outcomes) is **non-adaptive** if, for every round $i$, the instrument it applies does not depend on the history:
--   $$T^{x}_{x_{<i}}=T^{x}_{x'_{<i}}\quad\text{for all histories }x_{<i},x'_{<i}\text{ and every outcome }x.$$
--
--   This is the paper's notion of §6: the measurement schedule, unitaries and measurements are fixed before any outcome is observed, and classical post-processing happens only after all copies are measured. The memory may still carry correlations between rounds, since the memory state after a round depends on which branch occurred; only the operation performed is fixed in advance.
--
--   **Formalization Note** The protocol is the published `StabTestMem.MemProtocol`; its `accept` field plays no role for learners. Precommitted randomness shared by all rounds is modelled separately, by `StabTestMem.Supplement.NALearner`.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §6.1, p. 52; Definition 3.7, pp. 21–22

import Definitions.Def_StabTestMem_MemProtocol

namespace StabTestMem.Supplement

open QAlgorithms

/-- **Non-adaptive protocol with `k` qubits of memory.** Arunachalam, Schatzki, *Optimal stabilizer
testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §6.1,
p. 52: "since we are working with non-adaptive algorithms, the measurement schedule is fixed before
any outcome is observed, all choices unitaries, measurements are fixed in advance. All classical
post-processing is performed only after all copies have been measured. The coherent quantum memory
allows for correlations between rounds, but the way it is used is fixed ahead of time and
independent of all prior outcomes."

`IsNonAdaptive P`: the instrument branch `T^{x}_{h}` that round `i` of the published
`StabTestMem.MemProtocol` (Definition 3.7, pp. 21–22) applies does not depend on the history `h`
of earlier outcomes.

**Formalization Note.** The memory state after a round still depends on that round's outcome
(through the instrument branch), which is the paper's "correlations between rounds"; only the
choice of the operation is fixed. The `accept` field of `MemProtocol` plays no role for learners.
Precommitted shared randomness (random Clifford branches, p. 52) is not a property of a single
protocol; it is modelled by `StabTestMem.Supplement.NALearner` as a mixture of non-adaptive
protocols. -/
def IsNonAdaptive {n k t : ℕ} {X : Type} [Fintype X] (P : MemProtocol n k t X) : Prop :=
  ∀ (i : Fin t) (h h' : Fin i → X) (x : X), P.inst i h x = P.inst i h' x

end StabTestMem.Supplement


