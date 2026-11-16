-- Prove2me | Definitions.Def_QRetrieval_Adaptive_Supplement_productPhaseOracle
-- name    : QRetrieval_Adaptive_Supplement_productPhaseOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:58:14.41535+00:00
-- url     : https://prove2.me/theorems/bd73a84c-1c4f-438a-8896-3c33a92159cb
-- title:
--   The product oracle gate $O_y^{\otimes T}$ of a non-adaptive query scheme
-- statement:
--   Let $y\in\{0,1\}^s$ be a stored string and recall the **controlled phase oracle** $O_y:|j\rangle|b\rangle\mapsto(-1)^{y_j\cdot b}|j\rangle|b\rangle$ on an address register $j\in[s]$ and an oracle qubit $b\in\{0,1\}$. For $T\ge 0$, the **product oracle gate** $O_y^{\otimes T}$ acts on $T$ query registers $(j_1,b_1),\dots,(j_T,b_T)$ at once:
--
--   $$
--   O_y^{\otimes T}\,|j_1,\dots,j_T\rangle|b_1,\dots,b_T\rangle=\prod_{k=1}^{T}(-1)^{y_{j_k}\cdot b_k}\,|j_1,\dots,j_T\rangle|b_1,\dots,b_T\rangle .
--   $$
--
--   It is the single oracle gate of a non-adaptive (parallel) query scheme in Definition 2.1 of the paper: all $T$ probes into $y$ are made simultaneously.
--
--   **Formalization Note** The $T$ address registers and the $T$ oracle qubits are grouped as a pair of tuples $(j,b)\in(\mathrm{Fin}\,T\to\iota)\times(\mathrm{Fin}\,T\to\mathrm{Bool})$, a fixed reordering of the tensor factors of $O_y^{\otimes T}$. The gate is a diagonal complex matrix; for $T=0$ it is the identity.
-- source:
--   Dhamapurkar, Garg, Paraashar, Radhakrishnan, Optimal compression with quantum retrieval, arXiv:2610.06702, Definition 2.1, p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

namespace QRetrieval.Adaptive.Supplement

/-- **The product oracle gate `O_y^{⊗T}` of a non-adaptive query scheme (Definition 2.1).**
Dhamapurkar, Garg, Paraashar, Radhakrishnan, *Optimal compression with quantum retrieval*,
arXiv:2610.06702, Definition 2.1, p. 4: "The query scheme is non-adaptive if the oracle gates are
applied in parallel; alternatively, we may assume that the query circuit is allowed to use a
product oracle gate of the form `O_y^{⊗t′}` (for some `t′ ≤ t`), which appears exactly once in the
circuit", where `O_y : |j⟩|b⟩ ↦ (−1)^{y_j·b}|j⟩|b⟩`.

`productPhaseOracle T y` acts on `T` address/oracle-qubit pairs `(j_k, b_k)`, `k < T`, grouped as
the pair of tuples `(j, b) : (Fin T → ι) × (Fin T → Bool)`. It is the diagonal matrix with entry
`∏_{k < T} (−1)^{y_{j_k}·b_k}`, i.e. the `T`-fold tensor power of the controlled phase oracle
`QAlgorithms.controlledPhaseOracle y` (`O_y` on each of the `T` query registers), with the registers
reordered so that all addresses come first and all oracle qubits second.

**Formalization Note.** The `T` factors of `O_y^{⊗T}` are indexed by `Fin T`; a reordering of
tensor factors is a fixed permutation of basis states, so it does not change which states or
measurement statistics a circuit can produce. For `T = 0` the gate is the identity on the
one-point register. -/
noncomputable def productPhaseOracle {ι : Type*} [DecidableEq ι] (T : ℕ) (y : ι → Bool) :
    Matrix ((Fin T → ι) × (Fin T → Bool)) ((Fin T → ι) × (Fin T → Bool)) ℂ :=
  Matrix.diagonal fun p => ∏ k : Fin T, if p.2 k && y (p.1 k) then -1 else 1

end QRetrieval.Adaptive.Supplement


