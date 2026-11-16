-- Prove2me | Definitions.Def_QStateSearch_Supplement_sec6Oracle
-- name    : QStateSearch_Supplement_sec6Oracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:23:59.077195+00:00
-- url     : https://prove2.me/theorems/004e8f57-653f-4109-a034-0187531baea0
-- title:
--   The random-subset oracle $T$ of Section 6
-- statement:
--   For label sets $L_n$ and vectors $\psi_x$, the oracle $T$ has, for every $n\ge4$, the components
--
--   1. the testing block $W_n$ (label $[0]$, $2n+1$ qubits);
--   2. $\mathrm{GenYes}_{n,t}=S(Y_{n,t})$ for every tag $t\ge1$ (label $[1,t]$, $n(t+1)+1$ qubits);
--   3. $\mathrm{GenNo}_n=S(N_n)$ (label $[2]$, $n+1$ qubits).
--
--   Every other label and size gives the identity. Together they form one tagged block-diagonal unitary.
--
--   **Formalization Note** The size of a call determines $n$; the tag is part of the label, which descriptions write in unary, so polynomial-time machines address only polynomial tags and registers.
-- source:
--   Barhoush, Quantum State Search with Classical Interactive Advice, arXiv:2610.25657 (held version, sha256 2a16939a…3408), Section 6.2, p.17

import Mathlib
import Definitions.Def_QStateSearch_Supplement_QOracle
import Definitions.Def_QStateSearch_Supplement_swapUnitary
import Definitions.Def_QStateSearch_Supplement_testBlock
import Definitions.Def_QStateSearch_Supplement_yesState
import Definitions.Def_QStateSearch_Supplement_noState

set_option autoImplicit false

namespace QStateSearch.Supplement

/-- The **random-subset oracle `T` of Section 6**, for label sets `L_n` and `n`-qubit vectors
`ψ_x`. Its components, for every `n ≥ 4`:
* label `[0]` on `2n + 1` qubits: the testing block `W_n` (`testBlock`);
* label `[1, t]`, `t ≥ 1`, on `n(t + 1) + 1` qubits: `GenYes_{n,t} = S(Y_{n,t})`;
* label `[2]` on `n + 1` qubits: `GenNo_n = S(N_n)`.
Every other label and size is the identity.

Barhoush, *Quantum State Search with Classical Interactive Advice*, arXiv:2610.25657
(held version, sha256 2a16939a…3408), Section 6.2, p.17: "The oracle has one testing component and two sampling components … The
oracle contains the blocks GenYes_{n,t} = S(Y_{n,t}) for every t ≥ 1, GenNo_n = S(N_n). The integer
t is a classical tag. Equivalently, all these blocks form one tagged block-diagonal unitary …
Let T denote the collection of these independently sampled components over all input lengths."

**Formalization Note.** The number of qubits of an oracle call determines `n` (`2n + 1`,
`n(t + 1) + 1` or `n + 1`); the tag `t` is part of the label. Since circuit descriptions write
labels and wire lists in unary (`decodeQCircuit`), a polynomial-time machine can address only
tags and registers of polynomial length, as on p.17. -/
noncomputable def sec6Oracle (L : (n : ℕ) → Finset (Fin n → Bool))
    (ψ : (n : ℕ) → (Fin n → Bool) → EuclideanSpace ℂ (Fin (2 ^ n))) : QOracle :=
  fun lab k => match lab with
    | [0] => if 4 ≤ (k - 1) / 2 ∧ 2 * ((k - 1) / 2) + 1 = k then
        testBlock L ψ ((k - 1) / 2) k else 1
    | [1, t] => if 1 ≤ t ∧ 4 ≤ (k - 1) / (t + 1) ∧ (k - 1) / (t + 1) * (t + 1) + 1 = k then
        swapUnitary (yesState L ψ ((k - 1) / (t + 1)) t k) else 1
    | [2] => if 4 ≤ k - 1 ∧ 1 ≤ k then swapUnitary (noState L (k - 1) k) else 1
    | _ => 1

end QStateSearch.Supplement


