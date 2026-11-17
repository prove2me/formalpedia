-- Prove2me | Definitions.Def_ApproxDegComp_Supplement_QE
-- name    : ApproxDegComp_Supplement_QE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:59:51.095592+00:00
-- url     : https://prove2.me/theorems/96e98d6e-e8ab-44af-bd3a-aca51f59f3eb
-- title:
--   Exact quantum query complexity $Q_E(f)$
-- statement:
--   The **oracle** for $x\in\{0,1\}^n$ is the unitary $O_x|i,b\rangle=|i,b\oplus x_i\rangle$ for $i\in[n]$, $b\in\{0,1\}$, extended by an additional index $i=0$ on which it acts as the identity. A **quantum algorithm with $T$ queries** consists of input-independent unitaries $U_0,\dots,U_T$ on the query register tensored with a finite workspace. It produces the final state
--
--   $$U_T\,O_x\,U_{T-1}\cdots U_1\,O_x\,U_0\,|0\rangle ,$$
--
--   with $O_x$ acting on the query register only. The final state is measured in the computational basis, and a fixed function of the outcome is the output. The **quantum query complexity** $Q_\varepsilon(f)$ of $f:\{0,1\}^n\to\{0,1\}$ is the least $T$ such that some $T$-query algorithm outputs $f(x)$ with probability at least $1-\varepsilon$ for every $x$. The **exact quantum query complexity** is
--
--   $$Q_E(f)=Q_0(f),$$
--
--   the least number of queries of an algorithm that outputs $f(x)$ with probability exactly $1$ on every input.
--
--   This is the measure of Theorems 32 and 33.
--
--   **Formalization Note** The algorithm is the published `QAlgorithms.QueryAlg`, with query register $(\{0\}\cup[n])\times\{0,1\}$ (the extra index is `none`) and workspace of any finite size, chosen with the algorithm. The start state is any fixed unit vector, which gives the same class as $|0\rangle$ since $U_0$ is arbitrary. Only oracle calls are counted. The set of admissible $T$ is nonempty (query every bit into the workspace), so the minimum exists.
-- source:
--   Pednekar–Podder, On the Composition Theorem for Approximate Degree, Randomized and Exact Quantum Query Complexity, STOC 2027 submission (manuscript sha256 b9a66c7fdb2afdb57851f3734661cd2140455987b17e2a1e2400586be814092b), Definitions 12–14, p.13

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Query

namespace ApproxDegComp

namespace Supplement

/-- The input `x ∈ {0,1}^ι` extended by the bit `0` at the additional oracle index `i = 0`
(`none`), so that the standard oracle acts as the identity there (Definition 12, p.13). -/
def extInput {ι : Type} (x : ι → Bool) : Option ι → Bool :=
  fun o => o.elim false x

/-- **Quantum query complexity** `Q_ε(f)` and **exact quantum query complexity**
`Q_E(f) = Q_0(f)` (Definitions 12–14, p.13).
Pednekar–Podder, *On the Composition Theorem for Approximate Degree, Randomized and Exact
Quantum Query Complexity*, STOC 2027 submission (manuscript sha256 b9a66c7f…), p.13.
Definition 12: "O_x |i, b⟩ = |i, b ⊕ x_i⟩, where i ∈ [n] and b ∈ {0,1}. We use a modified version
where for an additional index i = 0, this oracle acts like an identity." Definition 13: "A quantum
algorithm with T queries is a sequence of input-independent unitary operators U_0, …, U_T
interleaved with T oracle unitaries O_x and applied to a fixed state, … producing a final state
U_T O_x … O_x U_0 |0⟩. This final state is measured to give the output of the algorithm."
Definition 14: "Q_ϵ(f) is the minimum number of queries needed by any quantum algorithm to compute
f(x) for every x in the domain with an error probability at most ϵ … when ϵ = 0, it is called exact
quantum query complexity and is denoted by Q_E(f)."

`QEps ε f` is the least `T` such that some `T`-query algorithm, with query register
`{0} ∪ ι` (`Option ι`) times one target bit and a workspace `Fin k` of any finite size `k`,
measured in the computational basis and post-processed by a fixed output map, outputs `f x` with
probability at least `1 − ε` on every input `x`.

**Formalization Note** The algorithm is the published `QAlgorithms.QueryAlg` (input-independent
unit start state and unitaries `U_0, …, U_T`; the oracle acts as `O ⊗ I` on the workspace). The
oracle is `QAlgorithms.xorOracle (extInput x)` on `Option ι × Bool`: `|some i, b⟩ ↦ |some i, b ⊕ x_i⟩`,
`|none, b⟩ ↦ |none, b⟩` (the paper's index `0`). The start state is any fixed unit vector (the
paper's `|0⟩`; the same class, since `U_0` is arbitrary). The output is a fixed function of the
computational-basis outcome of the whole register. For total `f` the domain is the whole cube.
For `ε = 0` the condition is success probability exactly `1` (probabilities are at most `1`). The
set is nonempty (query every bit into the workspace), so `sInf` is the minimum. -/
noncomputable def QEps {ι : Type} [Fintype ι] [DecidableEq ι] (ε : ℝ)
    (f : (ι → Bool) → Bool) : ℕ :=
  sInf {T : ℕ | ∃ (k : ℕ) (A : QAlgorithms.QueryAlg (Option ι) Bool (Fin k) T)
    (out : (Option ι × Bool) × Fin k → Bool),
    ∀ x : ι → Bool, A.outputProb (QAlgorithms.xorOracle (extInput x)) out (f x) ≥ 1 - ε}

/-- **Exact quantum query complexity** `Q_E(f) = Q_0(f)` (Definition 14, p.13). -/
noncomputable def QE {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool) : ℕ :=
  QEps 0 f

end Supplement

end ApproxDegComp


