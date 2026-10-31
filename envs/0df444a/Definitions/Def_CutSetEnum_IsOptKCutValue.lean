-- Prove2me | Definitions.Def_CutSetEnum_IsOptKCutValue
-- name    : CutSetEnum_IsOptKCutValue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:15.767381+00:00
-- url     : https://prove2.me/theorems/52ddbd37-ce54-47de-8243-8f67e39c0f5a
-- title:
--   $c=OPT_{k\text{-cut}}$: the optimum value of Hypergraph-$k$-Cut
-- statement:
--   A **$k$-partition** of $V$ is an ordered tuple $(V_1,\dots,V_k)$ of non-empty, pairwise disjoint sets covering $V$, and $|\delta(V_1,\dots,V_k)|$ is the number of hyperedges meeting at least two parts. The optimum value of Hypergraph-$k$-Cut is
--   $$
--   OPT_{k\text{-cut}}=\min\{|\delta(V_1,\dots,V_k)|:\ (V_1,\dots,V_k)\ \text{is a $k$-partition of}\ V\}.
--   $$
--   The predicate "$c=OPT_{k\text{-cut}}$" holds when some $k$-partition crosses exactly $c$ hyperedges and every $k$-partition crosses at least $c$.
--
--   This is the hypothesis $d(U)=OPT_{k\text{-cut}}$ of the paper's main theorems.
--
--   **Formalization Note** $k$-partitions and their crossing numbers are the published `IsPartition` and `cost`. The minimum is written as "attained and least" rather than with `sInf`, which is $0$ on the empty set in $\mathbb N$: when $V$ has fewer than $k$ vertices there is no $k$-partition and the predicate is false for every $c$.
-- source:
--   Beideman, Chandrasekaran & Wang, Counting and enumerating optimum cut sets for hypergraph k-partitioning problems for fixed k, arXiv:2204.09178v2, §1.2, p.4 (PDF 5)

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

open HyperKCut.Structure

namespace CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **`c = OPT_k-cut`: `c` is the optimum value of Hypergraph-k-Cut.**
Beideman, Chandrasekaran & Wang, arXiv:2204.09178v2, §1.2, p.4 (PDF 5):
"OPT_k-cut := min {|δ(V₁, …, V_k)| : (V₁, …, V_k) is a k-partition of V}".

`IsOptKCutValue H k c` holds when some k-partition `P` of the vertex set has exactly `c` crossing
hyperedges, and every k-partition has at least `c` crossing hyperedges.

**Formalization Note.** A k-partition is the published `IsPartition P` for
`P : Fin k → Finset V` (ordered, non-empty, pairwise disjoint, covering parts) and
`|δ(V₁, …, V_k)|` is the published `cost H P`. The minimum is spelled out as "attained and least"
rather than written with `sInf`, because `sInf ∅ = 0` in `ℕ`: when `V` has fewer than `k`
vertices there is no k-partition, OPT_k-cut is undefined, and `IsOptKCutValue H k c` is false for
every `c`. -/
def IsOptKCutValue (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (c : ℕ) : Prop :=
  (∃ P : Fin k → Finset V, IsPartition P ∧ cost H P = c) ∧
  ∀ P : Fin k → Finset V, IsPartition P → c ≤ cost H P

end CutSetEnum


