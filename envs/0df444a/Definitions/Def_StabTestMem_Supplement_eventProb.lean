-- Prove2me | Definitions.Def_StabTestMem_Supplement_eventProb
-- name    : StabTestMem_Supplement_eventProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T22:38:50.072209+00:00
-- url     : https://prove2.me/theorems/dd421090-e184-4d26-ac1e-481f3e28a2a1
-- title:
--   Probability of a transcript event of a memory protocol
-- statement:
--   Let $P$ be a protocol with $k$ qubits of memory run on $t$ copies of an $n$-qubit state $\rho$. By Lemma 3.10 the transcript $x=(x_1,\dots,x_t)$ occurs with probability $\operatorname{Tr}[E_x\rho^{\otimes t}]$. For an event $E$ (a set of transcripts),
--   $$\Pr_{P,\rho}[E]=\sum_{x\in E}\operatorname{Re}\operatorname{Tr}[E_x\rho^{\otimes t}].$$
--
--   This is the success functional of the learning statements: the event is that the post-processed output is correct.
--
--   **Formalization Note** The transcript functional is the published `MemProtocol.weight` and $\rho^{\otimes t}$ the published `WildeQIT.Schumacher.tensorPow`, as in the published acceptance probability `MemProtocol.acceptProb`. For a density matrix the weights are nonnegative reals, so taking the real part loses nothing.
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 3.10, Eq. (36), p. 23

import Definitions.Def_StabTestMem_MemProtocol

namespace StabTestMem.Supplement

open QAlgorithms

/-- **Probability of a transcript event.** Arunachalam, Schatzki, *Optimal stabilizer testing and
learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 3.10,
Eq. (36), p. 23: "the probability of observing transcript x is given by Tr[E_x ρ^{⊗t}]".

`eventProb P ρ E = Σ_{x ∈ E} Re Tr[E_x ρ^{⊗t}]`, the probability that the transcript of the
published `StabTestMem.MemProtocol` `P` run on `t` copies of `ρ` lies in the event `E`, with the
transcript functional the published `MemProtocol.weight` and the tensor power the published
`WildeQIT.Schumacher.tensorPow` (as in the published `MemProtocol.acceptProb`).

**Formalization Note.** For a density matrix `ρ` the weights are nonnegative reals; the real part
only discards a zero imaginary part. The event is decided classically. -/
noncomputable def eventProb {n k t : ℕ} {X : Type} [Fintype X] (P : MemProtocol n k t X)
    (ρ : Matrix (Qubits n) (Qubits n) ℂ) (E : (Fin t → X) → Prop) : ℝ := by
  classical
  exact ∑ x, if E x then (P.weight (WildeQIT.Schumacher.tensorPow t ρ) x).re else 0

end StabTestMem.Supplement


