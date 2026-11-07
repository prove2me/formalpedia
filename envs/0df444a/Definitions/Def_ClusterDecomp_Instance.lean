-- Prove2me | Definitions.Def_ClusterDecomp_Instance
-- name    : ClusterDecomp_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:08:56.097934+00:00
-- url     : https://prove2.me/theorems/e2edcf21-4cb3-4a65-8fbe-9dd2f4fe3cf8
-- title:
--   Inputs of Theorem 1.1 and of the fair-cut black box, and their memory layouts
-- statement:
--   An instance consists of $n$ vertices, $m$ edges as a list of endpoints, integer weights, sets $A_1,\dots,A_k$ and reals $\varepsilon,p$. Its hypotheses `Hyp d` are: no parallel edges, positive integer weights, $w_j\le n^d\,w_{j'}$ for all edges (the polynomial ratio of p.1, with exponent $d$), and the hypotheses of Theorem 1.1 on the resulting graph.
--
--   The input is laid out in memory. Integer memory holds $n,m,k$, the endpoints, and for each vertex its label ($0$ if it is in no $A_i$, $i+1$ if $v\in A_i$); real memory holds $\varepsilon,p$ and the weights. An output is read from integer memory at $-1-v$: the vertex $v$ is in the $i$-th output set iff its label is $i+1$. The black box's input holds $n,m$, the endpoints, $\eta$ and the capacities, with $s$ the vertex $0$ and $t$ the vertex $1$, and its source side is the set of vertices with label $1$.
--
--   These layouts make the running-time claims of the goal and the black box precise; the paper names no format.
--
--   **Formalization Note** Memory starts at $0$, so an algorithm need not touch a vertex whose label is $0$.
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), Theorem 1.1, p.2 (PDF p.4); standing assumption, p.1 (PDF p.3); black box, p.9 (PDF p.11); the layout is a reading of this mission

import Mathlib
import Definitions.Def_ClusterDecomp_Conductance
import Definitions.Def_ClusterDecomp_Machine

open Finset

namespace ClusterDecomp

/-!
# Instances of Theorem 1.1 and of the fair-cut black box, and their memory layouts

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027
submission (manuscript sha256 ba091f54…), Theorem 1.1, p.2 (PDF p.4); standing assumption, p.1 (PDF p.3); black box, p.9
(PDF p.11).

**Formalization Note.**
* An instance has an explicit edge list of `m` edges on `n` vertices, so `m` of the running time is the number of edges
  of the graph. Parallel edges are excluded by `Injective` on unordered pairs, and loops are allowed.
* Integer weights sit in real cells, and `ε`, `p` are real inputs: `β = (1+ε/10)p` is a real when they are.
* Theorem input. Integer memory: cell `0` = `n`, `1` = `m`, `2` = `k`, then the two endpoints of each edge, then for each
  vertex `v` the value `0` if `v` is in no `A_i` and `i + 1` if `v ∈ A_i`. Real memory: `ε`, `p`, then the weights.
* Black-box input. Integer memory: `n`, `m`, then the endpoints, with `s` = vertex `0`, `t` = vertex `1`. Real memory: `η`,
  then the capacities.
* Outputs are read from integer memory at `−1 − v` (`label`): in the theorem, `v` is in the `i`-th output set iff its
  label is `i + 1`, so those sets are automatically disjoint; in the black box, `v` is on the source side iff its label
  is `1`. Memory starts at `0`, so an algorithm need not touch vertices it assigns label `0`.
-/

/-- An input to Theorem 1.1 (`A_i` given by labels, weights integer). -/
structure Instance where
  /-- The number of vertices. -/
  n : ℕ
  /-- The number of edges. -/
  m : ℕ
  /-- The number of input sets. -/
  k : ℕ
  /-- The endpoints of each edge. -/
  e : Fin m → Fin n × Fin n
  /-- The integer weight of each edge. -/
  wt : Fin m → ℕ
  /-- The input sets `A_1, …, A_k`. -/
  A : Fin k → Finset (Fin n)
  /-- The gap parameter. -/
  ε : ℝ
  /-- The outer conductance bound. -/
  p : ℝ

/-- The weight function `w(u, v) = ∑_{e_j = {u, v}} c_j` of an edge list with nonnegative values. -/
def edgeWeight {n m : ℕ} (e : Fin m → Fin n × Fin n) (c : Fin m → ℝ) (u v : Fin n) : ℝ :=
  ∑ j, if s((e j).1, (e j).2) = s(u, v) then c j else 0

namespace Instance

/-- The endpoints as a list of integers. -/
def endpointList {n m : ℕ} (e : Fin m → Fin n × Fin n) : List ℤ :=
  (List.ofFn fun j => [(((e j).1 : ℕ) : ℤ), (((e j).2 : ℕ) : ℤ)]).flatten

variable (I : Instance)

/-- The graph of the instance. -/
def graph : WGraph (Fin I.n) where
  w := edgeWeight I.e fun j => (I.wt j : ℝ)
  symm u v := by
    unfold edgeWeight
    exact Finset.sum_congr rfl fun j _ => by rw [Sym2.eq_swap (a := u) (b := v)]
  nonneg u v := Finset.sum_nonneg fun j _ => by
    split_ifs
    · exact Nat.cast_nonneg _
    · exact le_rfl

/-- The hypotheses of Theorem 1.1 with the standing assumption of p.1, the exponent `d` bounding the polynomial ratio:
no parallel edges, positive integer weights, `w_j ≤ n^d · w_{j′}`, and `Family`. -/
structure Hyp (d : ℕ) : Prop where
  edges_inj : Function.Injective fun j => s((I.e j).1, (I.e j).2)
  wt_pos : ∀ j, 0 < I.wt j
  ratio : ∀ j j', I.wt j ≤ I.n ^ d * I.wt j'
  family : Family I.graph I.k I.A I.ε I.p

open scoped Classical in
/-- The integer memory of the input. -/
noncomputable def ints : List ℤ :=
  [(I.n : ℤ), (I.m : ℤ), (I.k : ℤ)] ++ endpointList I.e ++
    List.ofFn fun v : Fin I.n =>
      if h : ∃ i, v ∈ I.A i then ((Classical.choose h : Fin I.k) : ℤ) + 1 else 0

/-- The real memory of the input. -/
noncomputable def reals : List ℝ :=
  [I.ε, I.p] ++ List.ofFn fun j => (I.wt j : ℝ)

/-- The start state on the instance. -/
noncomputable def input : State := initState I.ints I.reals

end Instance

/-- The output sets of a halted state: `v` is in the `i`-th set iff its label is `i + 1`. -/
noncomputable def outputSet {k : ℕ} (n : ℕ) (s : State) (i : Fin k) : Finset (Fin n) :=
  univ.filter fun v => label s v = (i : ℤ) + 1

/-- The start state of the fair-cut black box on `n` vertices, an edge list, capacities and `η`. -/
noncomputable def fairCutInput (n : ℕ) {m : ℕ} (e : Fin m → Fin n × Fin n) (c : Fin m → ℝ)
    (η : ℝ) : State :=
  initState ([(n : ℤ), (m : ℤ)] ++ Instance.endpointList e) ([η] ++ List.ofFn c)

/-- The source side output by the black box: the vertices with label `1`. -/
noncomputable def fairCutOutput (n : ℕ) (s : State) : Finset (Fin n) :=
  univ.filter fun v => label s v = 1

end ClusterDecomp


