-- Prove2me | Definitions.Def_OAI_InformationTheory_QuantumCircuit_Model
-- name    : OAI_InformationTheory_QuantumCircuit_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T02:07:58.353626+00:00
-- url     : https://prove2.me/theorems/6e4ab508-541e-4a04-a391-8222b9afe38d
-- title:
--   Statement of the measured-output parity lower bound for constant-depth circuits with unbounded Toffoli gates
-- statement:
--   This file defines the proposition $\mathrm{ParityStatement}$: constant-depth quantum circuits built from one-qubit unitaries and Toffoli gates of unbounded arity, acting on polynomially many qubits, cannot compute the parity of their input with a constant advantage on every input.
--
--   **Setting.** Qubits are labelled $0,\dots,N-1$, computational basis states by words $y\in\{0,1\}^N$, and an $N$-qubit operator is a complex $2^N\times 2^N$ matrix indexed by such words. A *gate* is either a one-qubit unitary $u$ on a qubit $q$ (the matrix $u$ on qubit $q$ tensored with the identity elsewhere; support $\{q\}$), or a Toffoli gate with a finite control set $c$ and a target $t\notin c$ (support $c\cup\{t\}$), which maps $|y\rangle$ to $|y'\rangle$, where $y'$ is $y$ with bit $t$ flipped if $y_i=1$ for all $i\in c$, and $y'=y$ otherwise. A *physical layer* is a list of gates with pairwise disjoint supports; its matrix is the product of its gate matrices. For a list of layers $\mathcal L=(L_1,\dots,L_m)$ the circuit matrix is $W_{\mathcal L}=W_{L_m}\cdots W_{L_1}$, so the first layer acts first. For $x\in\{0,1\}^n$ the padded input $\hat x\in\{0,1\}^N$ equals $x$ on the first $n$ qubits and $0$ on all others, $\operatorname{par}(x)=x_1+\dots+x_n \bmod 2$, and for an output qubit $o$ the success probability is
--
--   $$
--   \mathrm{succ}(W,o,x)=\sum_{y\in\{0,1\}^N:\ y_o=\operatorname{par}(x)}\bigl|W_{y,\hat x}\bigr|^2 ,
--   $$
--
--   the Born probability that measuring qubit $o$ of $W|\hat x\rangle$ returns the parity of $x$. All other qubits are summed over; they are not required to return to $0$.
--
--   **Definition.** $\mathrm{ParityStatement}$ asserts: for every $d\in\mathbb N$ and all real numbers $c,\varepsilon$ with $c\ge 1$ and $0<\varepsilon\le \tfrac12$, there is $n_0\in\mathbb N$ such that for every $n\ge n_0$, every $N\in\mathbb N$ with $n\le N\le n^c$, every list $\mathcal L$ of at most $d$ physical layers on $N$ qubits and every output qubit $o$, it is **not** the case that
--
--   $$
--   \mathrm{succ}(W_{\mathcal L},o,x)\ \ge\ \tfrac12+\varepsilon\qquad\text{for all } x\in\{0,1\}^n .
--   $$
--
--   This is the general form of the parity lower bound: depth $d$, the polynomial exponent $c$ and the advantage $\varepsilon$ are arbitrary but fixed, and the threshold $n_0$ may depend on them. The version with success threshold $2/3$ and qubit bound $C(n+1)^k$ follows by choosing $\varepsilon=1/6$ and $c=k+1$.
--
--   **Formalization Note** `ParityStatement` is a `Prop`. The gate model (`Gate`, `PhysicalLayer`, `physicalCircuitMatrix`, `inputWord`, `parity`, `successProbability`) comes from the mission's base definition file. The bound $N\le n^c$ is stated with the real power `(n : ℝ) ^ c`. No positivity assumption on $d$ is imposed (for $d=0$ the circuit is the identity).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Model.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/QuantumCircuit/Model.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the RegularParity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_RegularParity

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace QAC

namespace Gate

end Gate

/-- The literal measured-output, polynomial-total-qubit parity lower bound. -/
def ParityStatement : Prop :=
  ∀ (d : ℕ) (c ε : ℝ), 1 ≤ c → 0 < ε → ε ≤ 1 / 2 →
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N : ℕ, n ≤ N → (N : ℝ) ≤ (n : ℝ) ^ c →
      ∀ layers : List (PhysicalLayer N), layers.length ≤ d →
        ∀ out : Fin N, ¬ (∀ x : Word n,
          1 / 2 + ε ≤ successProbability (physicalCircuitMatrix layers) out x)

end QAC

end

end OAI


