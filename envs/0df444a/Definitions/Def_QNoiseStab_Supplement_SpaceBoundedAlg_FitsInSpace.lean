-- Prove2me | Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg_FitsInSpace
-- name    : QNoiseStab_Supplement_SpaceBoundedAlg_FitsInSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:18:36.639817+00:00
-- url     : https://prove2.me/theorems/84796c33-2e10-41d4-bcdd-a21bc4c8b0e4
-- title:
--   The algorithm uses at most $S$ qubits of memory
-- statement:
--   A space-bounded algorithm with query register $[n]$, phase register $\mathbb Z_d$ and workspace $W$ **uses at most $S$ qubits** if its whole memory fits in $S$ qubits:
--
--   $$
--   n\cdot d\cdot |W|\le 2^{S}.
--   $$
--
--   The query and phase registers count against the space, as in the paper, which uses this to assume $2^S\ge n$ in its time-space lower bounds.
--
--   **Formalization Note** Space is counted by the dimension of the memory; every $S$-qubit circuit whose registers are $Q,P,W$ satisfies the bound.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.2, p.7 ("we assume that the state of C is entirely stored in qubits"); Theorem 4.3, p.19; proofs on p.20, p.31, p.42

import Mathlib
import Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg

set_option autoImplicit false

namespace QNoiseStab.Supplement

/-- The algorithm **uses at most `S` qubits of memory** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.2, p.7: "we assume that the
state of C is entirely stored in qubits"; Theorem 4.3, p.19: "using S qubits of memory"; proofs on
p.20 "Since each algorithm A_h requires a register with qubits to index the n inputs values, we can
assume that 2^S ≥ n", p.31 and p.42 "the query register already takes this space"): its whole
memory `Q ⊗ P ⊗ W`, query and phase registers included, has dimension `n · d · |W| ≤ 2^S`, i.e.
it embeds in `S` qubits.

**Formalization Note** The registers are counted by dimension, not by a qubit count per register;
every `S`-qubit circuit of the paper whose registers are `Q, P, W` satisfies this bound. -/
def SpaceBoundedAlg.FitsInSpace {n d : ℕ} [NeZero d] {W K V ι : Type} [Fintype W] [DecidableEq W]
    [Fintype K] [Fintype V] [Fintype ι] {T : ℕ} (_A : SpaceBoundedAlg n d W K V ι T) (S : ℕ) :
    Prop :=
  n * d * Fintype.card W ≤ 2 ^ S

end QNoiseStab.Supplement


