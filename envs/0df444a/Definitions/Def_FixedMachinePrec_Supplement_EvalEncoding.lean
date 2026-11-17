-- Prove2me | Definitions.Def_FixedMachinePrec_Supplement_EvalEncoding
-- name    : FixedMachinePrec_Supplement_EvalEncoding
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:57:53.929942+00:00
-- url     : https://prove2.me/theorems/78da4ab4-8b42-477d-85e9-5f24a2a195d3
-- title:
--   Input and output words of the explicit evaluator (Algorithms 2–5)
-- statement:
--   Fix the padded job set $J=\{1,\dots,N\}$ and write a set $X\subseteq J$ as its **incidence vector** $b_1\cdots b_N$, $b_j=1$ iff $j\in X$. Numbers are written in a self-delimiting binary code.
--
--   The **input word of the evaluator** consists of
--
--   1. the codes of $m$ and $N$;
--   2. the precomputed transitive order $\prec$ as an $N\times N$ Boolean matrix, row by row (entry $(i,j)$ is $1$ iff $i\prec j$);
--   3. the number of members of the node family $\mathcal F$, followed by each member as its $N$-bit incidence vector, in some order and without repetition;
--   4. the same for the cut family $\mathcal F_{\mathrm{cut}}$.
--
--   The **output word of the evaluator** lists, for every row $X\in\mathcal F$ in the order of Algorithm 4 (by $|X|$, then lexicographically by $b_N\cdots b_1$), the value $a(X)$ computed by Algorithms 2–5, and, when $a(X)=1$ with stored schedule $\sigma(X)=(S_1,\dots,S_k)$, the code of $k$ followed by each slot $S_i$ as its incidence vector.
--
--   These words fix what "the distinct family members supplied as $N$-bit incidence vectors and the global transitive order precomputed" and "the stored schedules of all accepted sets" mean in the cost statement of Theorem 6.3.
--
--   **Formalization Note** Jobs are `Fin N` (0-based; bit $j$ is the paper's $b_{j+1}$). The table is the published `FixedMachinePrec.evaluateFamily`; numbers use the published code `encBin`. The input lists `lF`, `lCut` are supplied by the caller in any order.
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Theorem 6.3, p.22; §6, p.20 (Boolean arrays, N × N matrix); §3.1, p.7 and Algorithm 4, p.9 (order of the rows)

import Mathlib
import Definitions.Def_FixedMachinePrec_EvaluateFamily
import Definitions.Def_FixedMachinePrec_FixedOrders
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding

namespace FixedMachinePrec.Supplement

open FixedMachinePrec
open QAlgorithms.LocalHamiltonian (encBin)

/-- The `N`-bit incidence vector of `X ⊆ Fin N`: bit `j` (0-based) is `true` iff `j ∈ X`
(Jansen, *Precedence Constraint Scheduling on a Fixed Number of Machines*, manuscript, sha256
08cdf3e1…, §3.1, p.7 and §6, p.20: "Sets are stored as Boolean arrays of length N").

**Formalization Note** Job labels are 0-based (`Fin N`); bit `j` is the paper's `b_{j+1}`. -/
def incVec {N : ℕ} (X : Finset (Fin N)) : List Bool :=
  (List.finRange N).map fun j => decide (j ∈ X)

/-- The precomputed transitive order as an `N × N` Boolean matrix, row-major: entry `(i, j)` is
`true` iff `i ≺ j` (§6, p.20: "the transitive precedence relation as an N × N Boolean matrix"). -/
def precMatrix {N : ℕ} (prec : Fin N → Fin N → Prop) [DecidableRel prec] : List Bool :=
  (List.finRange N).flatMap fun i => (List.finRange N).map fun j => decide (prec i j)

/-- **The input word of the explicit evaluator** (Theorem 6.3, p.22: "with the distinct family
members supplied as N-bit incidence vectors and the global transitive order precomputed"):
the self-delimiting codes of `m` and `N`, the `N²` bits of the order matrix, the number of members
of `F` followed by each member as its `N`-bit incidence vector, and the same for `F_cut`.

**Formalization Note** `lF` and `lCut` list the members of `F` and `F_cut` in an arbitrary order
supplied by the caller (the theorem quantifies over every duplicate-free listing); numbers use the
published self-delimiting code `encBin`. -/
def encEvalInput (m N : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (lF lCut : List (Finset (Fin N))) : List Bool :=
  encBin m ++ encBin N ++ precMatrix prec ++
    encBin lF.length ++ lF.flatMap incVec ++
    encBin lCut.length ++ lCut.flatMap incVec

/-- **The output word of the explicit evaluator** (Theorem 6.3, p.22: "including exact dictionary
construction and the stored schedules of all accepted sets"): for each row `X` of `F`, in the
order `(|X|, b_N ⋯ b_1)` of Algorithm 4, the bit `a(X)`, and, when `a(X) = 1` with stored schedule
`σ(X) = (S_1, …, S_k)`, the code of `k` followed by each slot `S_i` as its `N`-bit incidence
vector. The table is that of `evaluateFamily prec m F F_cut` (Algorithms 2–5). -/
def encEvalOutput {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec]
    (F Fcut : Finset (Finset (Fin N))) : List Bool :=
  let tab := evaluateFamily prec m F Fcut
  (listByCardCode F).flatMap fun X =>
    match tab X with
    | none => [false]
    | some S => true :: (encBin S.length ++ S.flatMap incVec)

end FixedMachinePrec.Supplement


