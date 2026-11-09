-- Prove2me | Definitions.Def_LocalPush_Layout
-- name    : LocalPush_Layout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T23:04:22.275815+00:00
-- url     : https://prove2.me/theorems/7f77395b-1d27-4601-8611-55ca1822b032
-- title:
--   Adjacency-list instances, input and output layouts for Theorems 1.2 and 4.1, and the clamped logarithm $\max\{1,\log x\}$
-- statement:
--   A graph instance is a family of adjacency lists $(\mathrm{nbrs}(v))_{v<n}$ that are duplicate-free and loop-free, symmetric ($v\in\mathrm{nbrs}(u)\iff u\in\mathrm{nbrs}(v)$) and nonempty (no isolated nodes), in any order; `toGraph` is the simple graph they describe.
--
--   1. The input of Theorem 1.2 holds the seed $s$ in integer cell $0$ and $\alpha,\varepsilon,\delta$ in real cells $0,1,2$; all other cells, registers and pointers are $0$. The program is not given $n$, $m$ or the lists.
--   2. The input of Theorem 4.1 holds $N$, the number $k$ of listed entries and their indices in integer memory, and $\mu,\delta$, the entry values and $b$ in real memory.
--   3. The output vector has entry $v$ at real memory address $-1-v$.
--   4. $\mathrm{L}(x):=\max\{1,\log x\}$ is the logarithm clamped at $1$.
--
--   **Formalization Note** The clamped logarithm replaces each logarithm of the printed running-time bounds, which contain $\log\log(1/\varepsilon)$ and $\log\log N$ and are $0$ or negative for small arguments.
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §1.1, p.4 (PDF p.4); Theorem 1.2, p.5; Theorem 4.1, p.15

import Mathlib
import Definitions.Def_LocalPush_Machine
import Definitions.Def_LocalPush_GraphMatrices

namespace LocalPush

/-!
# Instances and memory layouts: adjacency lists, the PageRank input, the SDD-solver input; the clamped logarithm

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §1.1, p.4 (PDF p.4) (the graph and
the adjacency-list model), Theorem 1.2, p.5, and Theorem 4.1, p.15.

**Formalization Note.**
* A graph instance is a list of adjacency lists `nbrs : Fin n → List (Fin n)` satisfying `IsAdjList`: every
  list is duplicate-free and loop-free, the relation is symmetric, and every list is nonempty (no isolated
  nodes, p.4). The lists may be in any order. `toGraph nbrs` is the simple graph they describe; under
  `IsAdjList` its adjacency is `v ∈ nbrs u` and the degree of `v` is the length of `nbrs v`.
* PageRank input (`pushInput`): integer memory cell `0` holds the seed `s`; real memory cells `0, 1, 2` hold
  `α, ε, δ`; everything else, including all registers and pointers, is `0`. The program is **not** given `n`,
  `m` or the lists: the graph is reachable only through the oracle instructions. Memory that starts at `0`
  serves as arrays initialized on first access (p.56).
* The output vector is dense: entry `v` is real memory at `−1 − v` (`outVec`), read at no cost on halting.
* SDD-solver input (`sddInput`, Theorem 4.1): integer memory holds `N`, `k`, then the row and column indices
  (0-based) of the `k` listed entries; real memory holds `µ`, `δ`, the `k` listed entry values, then
  `b(0), …, b(N−1)`. The solver runs on the empty graph (`n = 0`), so its oracle instructions return `−1`.
* `clog x := max{1, log x}` is the logarithm clamped at `1`, used for every logarithm of the running-time bounds
  of Theorems 1.2 and 4.1: the printed bounds contain `log log(1/ε)` and `log log N`, which are `0` or negative
  for small arguments, where no running time can be `0`.
-/

/-- `L(x) := max{1, log x}`, the logarithm clamped at `1`. -/
noncomputable def clog (x : ℝ) : ℝ :=
  max 1 (Real.log x)

/-- `nbrs` is the adjacency-list representation of a simple graph without isolated nodes. -/
structure IsAdjList {n : ℕ} (nbrs : Fin n → List (Fin n)) : Prop where
  nodup : ∀ v, (nbrs v).Nodup
  loopless : ∀ v, v ∉ nbrs v
  symm : ∀ u v, v ∈ nbrs u ↔ u ∈ nbrs v
  nonempty : ∀ v, nbrs v ≠ []

/-- The simple graph of a list of adjacency lists: `u ~ v` iff `u ≠ v` and one lists the other. Under
`IsAdjList` this is `v ∈ nbrs u`. -/
def toGraph {n : ℕ} (nbrs : Fin n → List (Fin n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun u v => v ∈ nbrs u

instance {n : ℕ} (nbrs : Fin n → List (Fin n)) : DecidableRel (toGraph nbrs).Adj :=
  fun u v => decidable_of_iff (u ≠ v ∧ (v ∈ nbrs u ∨ u ∈ nbrs v)) (by simp [toGraph])

/-- The input of Theorem 1.2: seed `s` in integer cell `0`; `α, ε, δ` in real cells `0, 1, 2`. -/
noncomputable def pushInput {n : ℕ} (s : Fin n) (α ε δ : ℝ) : State :=
  initState [((s : ℕ) : ℤ)] [α, ε, δ]

/-- The empty graph on `Fin 0`, the oracle of a run that does not use the graph. -/
def emptyGraph : Fin 0 → List (Fin 0) :=
  Fin.elim0

/-- The input of Theorem 4.1: integer memory `N, k, i_0, l_0, …, i_{k−1}, l_{k−1}`; real memory
`µ, δ, S(i_0, l_0), …, S(i_{k−1}, l_{k−1}), b(0), …, b(N−1)`. -/
noncomputable def sddInput (N k : ℕ) (ent : Fin k → Fin N × Fin N) (S : Matrix (Fin N) (Fin N) ℝ)
    (b : Fin N → ℝ) (μ δ : ℝ) : State :=
  initState
    ([(N : ℤ), (k : ℤ)] ++ (List.ofFn fun j => [(((ent j).1 : ℕ) : ℤ), (((ent j).2 : ℕ) : ℤ)]).flatten)
    ([μ, δ] ++ List.ofFn (fun j => S (ent j).1 (ent j).2) ++ List.ofFn b)

end LocalPush


