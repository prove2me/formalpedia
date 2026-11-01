-- Prove2me | Definitions.Def_MinSharing_DirectedConsumptionGraph
-- name    : MinSharing_DirectedConsumptionGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:24:54.549806+00:00
-- url     : https://prove2.me/theorems/89692107-3326-469d-a582-d347d553a8fb
-- title:
--   Weighted directed consumption graph $\overrightarrow{\mathcal{CG}}_z$ and the cycle product $\pi(C)$
-- statement:
--   For a valuation matrix $v$ and an allocation $z$, the **weighted directed consumption graph** $\overrightarrow{\mathcal{CG}}_z$ is bipartite between agents and objects:
--
--   1. there is an edge $i\to o$ of weight $w_{i\to o}=|v_{i,o}|$ if $z_{i,o}>0$ and $v_{i,o}\ge0$, or $z_{i,o}<1$ and $v_{i,o}<0$;
--   2. there is an edge $o\to i$ of weight $w_{o\to i}=1/|v_{i,o}|$ if $z_{i,o}>0$ and $v_{i,o}<0$, or $z_{i,o}<1$ and $v_{i,o}>0$.
--
--   A **cycle** $C=(i_1\to o_1\to i_2\to\cdots\to o_L\to i_{L+1}=i_1)$, $L\ge1$, uses both kinds of edges alternately, and its **product** is
--   $$\pi(C)=\prod_{k=1}^{L}\bigl(w_{i_k\to o_k}\cdot w_{o_k\to i_{k+1}}\bigr).$$
--
--   Outgoing edges of an agent are the objects she can give away (goods she holds, or bads held by others that she can take over); incoming edges are the objects she can accept. A cycle with $\pi(C)<1$ is a profitable cyclic trade, which is how Lemma 2.1 characterizes fractional Pareto-optimality.
--
--   **Formalization Note** A cycle is given by agents `a 0, …, a L` with `a L = a 0` and objects `b 0, …, b (L−1)` (paper's $i_k,o_k$ are `a (k−1), b (k−1)`); agents and objects may repeat, i.e. cycles are closed walks. A closed walk with product $<1$ contains a simple cycle with product $<1$, so statements of the form "no cycle with $\pi(C)<1$" mean the same thing. The weight $1/|v_{i,o}|$ only occurs on edges where $v_{i,o}\ne0$.
-- source:
--   Sandomirskiy, Segal-Halevi, Efficient Fair Division with Minimal Sharing, arXiv:1908.01669v3, §2.3, p.8 (weighted directed consumption graph, edge conditions and weights, product of a cycle)

import Mathlib

set_option autoImplicit false

namespace MinSharing

/-- Edge `i → o` of the **weighted directed consumption graph** `→CG_z` (arXiv:1908.01669v3,
§2.3, p.8): present iff `zᵢ,ₒ > 0` and `vᵢ,ₒ ≥ 0`, or `zᵢ,ₒ < 1` and `vᵢ,ₒ < 0`. Its weight is
`w_{i→o} = |vᵢ,ₒ|`. -/
def AgentToObj {n m : ℕ} (v z : Fin n → Fin m → ℝ) (i : Fin n) (o : Fin m) : Prop :=
  (0 < z i o ∧ 0 ≤ v i o) ∨ (z i o < 1 ∧ v i o < 0)

/-- Edge `o → i` of `→CG_z` (p.8): present iff `zᵢ,ₒ > 0` and `vᵢ,ₒ < 0`, or `zᵢ,ₒ < 1` and
`vᵢ,ₒ > 0`. Its weight is `w_{o→i} = 1/|vᵢ,ₒ|` (here `vᵢ,ₒ ≠ 0` whenever the edge exists). -/
def ObjToAgent {n m : ℕ} (v z : Fin n → Fin m → ℝ) (i : Fin n) (o : Fin m) : Prop :=
  (0 < z i o ∧ v i o < 0) ∨ (z i o < 1 ∧ 0 < v i o)

/-- A **directed cycle** `C = (i₁ → o₁ → i₂ → … → o_L → i_{L+1} = i₁)` of `→CG_z` (p.8), with
`L ≥ 1`: the agents are `a 0, …, a L` with `a L = a 0`, the objects `b 0, …, b (L−1)`, and for every
`k` both edges `a k → b k` and `b k → a (k+1)` are present.

**Formalization Note** The paper's `i_k, o_k` (`k = 1, …, L`) are `a (k−1), b (k−1)`. Agents and
objects may repeat (a closed walk); a closed walk with product `< 1` contains a simple cycle with
product `< 1`, so "no cycle with `π(C) < 1`" means the same for walks and for simple cycles. -/
def IsDirectedCycle {n m : ℕ} (v z : Fin n → Fin m → ℝ) (L : ℕ) (a : Fin (L + 1) → Fin n)
    (b : Fin L → Fin m) : Prop :=
  0 < L ∧ a (Fin.last L) = a 0 ∧
    ∀ k : Fin L, AgentToObj v z (a k.castSucc) (b k) ∧ ObjToAgent v z (a k.succ) (b k)

/-- The **product of a cycle** (p.8): `π(C) = ∏_{k=1}^{L} (w_{i_k→o_k} · w_{o_k→i_{k+1}})` with
`w_{i→o} = |vᵢ,ₒ|` and `w_{o→i} = 1/|vᵢ,ₒ|`. -/
noncomputable def cycleProduct {n m : ℕ} (v : Fin n → Fin m → ℝ) (L : ℕ)
    (a : Fin (L + 1) → Fin n) (b : Fin L → Fin m) : ℝ :=
  ∏ k : Fin L, (|v (a k.castSucc) (b k)| * (1 / |v (a k.succ) (b k)|))

end MinSharing


