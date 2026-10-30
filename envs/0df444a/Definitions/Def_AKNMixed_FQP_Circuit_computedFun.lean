-- Prove2me | Definitions.Def_AKNMixed_FQP_Circuit_computedFun
-- name    : AKNMixed_FQP_Circuit_computedFun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:21:40.052469+00:00
-- url     : https://prove2.me/theorems/c51bb3dc-5978-47ed-a78c-5f03e37cfa8e
-- title:
--   Computed function $f_Q$ (Definition 4)
-- statement:
--   Let $Q$ be a circuit with $n$ inputs and $r$ result outputs. The probabilistic function $f_Q:\{0,1\}^n\to[0,1]^{\{0,1\}^r}$ that $Q$ computes is
--
--   $$f_{i,j}=\langle j|\bigl(Q\circ|i\rangle\langle i|\bigr)\big|_A\,|j\rangle ,$$
--
--   where $|i\rangle$ is the basis state with $i$ on the inputs and $|0\rangle$ on every other wire (blanks included), and $A$ is the list of result outputs. It is the distribution of the outcome of measuring the result qubits at the end of the computation.
--
--   **Formalization Note** The real part of the diagonal entry is taken, so $f_Q$ is real valued.
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Definition 4, p. 9

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_AKNMixed_FQP_marginal
import Definitions.Def_AKNMixed_FQP_Circuit
import Definitions.Def_AKNMixed_FQP_Circuit_final

namespace AKNMixed.FQP

open QAlgorithms

/-- **The probabilistic function `f_Q` computed by a circuit.**
Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Definition 4, p. 9: "Let Q be a quantum circuit, with n inputs and r "result" outputs. The
probabilistic function that Q computes, f_Q = f : {0,1}^n ⟼ [0,1]^{{0,1}^r}, is defined as
follows: For input i, the probability for output j is f_{i,j} = ⟨j| (Q ∘ |i⟩⟨i|)|_A |j⟩, where A
is the set of the "result" outputs."

`Q.computedFun i j` is the real part of the `(j, j)` entry of the reduced density matrix, on the
result wires (in the order of `Q.results`), of the final density matrix for the initial basis
state `|c_i⟩⟨c_i|`, where `c_i = Q.inputConfig i` has `i` on the input wires and `0` on every
other wire.

**Formalization Note.** Blank inputs and wires not yet created start in `|0⟩`. The diagonal
entry is real for a positive semidefinite final state; the real part is taken so that `f_Q` is
real valued. -/
noncomputable def Circuit.computedFun {m p : ℕ} {G : Set QGate} {S : Set (ProbFun m p)}
    {nIn r : ℕ} (Q : Circuit G S nIn r) (i : Qubits nIn) (j : Qubits r) : ℝ :=
  (marginal Q.results
    (Q.final (Matrix.single (Q.inputConfig i) (Q.inputConfig i) 1)) j j).re

end AKNMixed.FQP


