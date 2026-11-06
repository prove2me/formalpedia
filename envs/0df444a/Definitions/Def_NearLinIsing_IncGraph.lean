-- Prove2me | Definitions.Def_NearLinIsing_IncGraph
-- name    : NearLinIsing_IncGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:09.8472+00:00
-- url     : https://prove2.me/theorems/8886351d-500a-4003-9034-0ccb32d05b5b
-- title:
--   Graphs by incidence lists, the Ising laws and the even-subgraph law (6)
-- statement:
--   A graph is given by **indexed incidence lists**: vertices $0,\dots,n-1$, edges $0,\dots,m-1$, the endpoint pair of each edge, and for each vertex the list of its incident edges. It is **well formed** when it is simple (no loops, no two edges with the same unordered endpoint pair) and each incidence list contains every edge at that vertex exactly once. The degree of a vertex is the length of its list.
--
--   For $\sigma\in\{-1,1\}^V$ let $m_=(\sigma)$ count the edges whose endpoints have equal spins. The **zero-field ferromagnetic Ising law** is
--
--   $$\mu_{\mathrm{Ising}}(\sigma)=Z_{\mathrm{Ising}}^{-1}\,\beta^{m_=(\sigma)},$$
--
--   and with edge activities $\beta_e\ge1$ it is $\mu_{\mathrm{Ising}}(\sigma)\propto\prod_{e=uv}\beta_e^{\mathbf 1\{\sigma_u=\sigma_v\}}$. A set $F\subseteq E$ is an **even subgraph** when every vertex has even degree in $F$, and the **even-subgraph law** with weights $t_e$ is
--
--   $$\pi_2(F)=Z_2^{-1}\,\mathbf 1\{\deg_F(v)\text{ even for every }v\}\prod_{e\in F}t_e .\tag{6}$$
--
--   These are the input format and the two target laws of the sampler.
--
--   **Formalization Note** Spins are encoded as `Bool`, since the laws depend only on equality of spins. Well-formedness is a separate predicate that every theorem assumes explicitly. "$G$ contains a cycle" is written as "$G$ has a nonempty even subgraph", which is equivalent.
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, §1, p. 1; §2.3, Eq. (6), p. 8; §2.6, p. 9

import Mathlib

namespace NearLinIsing

noncomputable section

open Classical

/-- A finite graph given by **indexed incidence lists** (§2.6, p. 9): vertices `Fin n`, edges
`Fin m`, the endpoint pair `ends e` of every edge, and for every vertex `v` the list `inc v` of the
indices of the edges at `v`.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, §1 (p. 1) and §2.6 (p. 9).

**Formalization Note.** The data carries no invariant; the conditions that make it a simple graph
with correct incidence lists are the separate predicate `IncGraph.WellFormed`, which every theorem
of the mission assumes explicitly (reading R5). -/
structure IncGraph where
  /-- number of vertices -/
  n : ℕ
  /-- number of edges -/
  m : ℕ
  /-- endpoints of each edge -/
  ends : Fin m → Fin n × Fin n
  /-- incidence list of each vertex -/
  inc : Fin n → List (Fin m)

namespace IncGraph

variable (G : IncGraph)

/-- `v` is an endpoint of `e`. -/
def IsEnd (v : Fin G.n) (e : Fin G.m) : Prop := (G.ends e).1 = v ∨ (G.ends e).2 = v

/-- Well-formedness of the input (reading R5): the graph is simple (no loops, no two edges with the
same unordered endpoint pair, p. 1) and the incidence list of `v` lists every edge at `v` exactly
once (§2.6). -/
structure WellFormed : Prop where
  loopless : ∀ e, (G.ends e).1 ≠ (G.ends e).2
  simple : ∀ e e', Sym2.mk (G.ends e) = Sym2.mk (G.ends e') → e = e'
  inc_nodup : ∀ v, (G.inc v).Nodup
  mem_inc : ∀ v e, e ∈ G.inc v ↔ G.IsEnd v e

/-- The degree of `v`: the length of its incidence list. -/
def deg (v : Fin G.n) : ℕ := (G.inc v).length

/-- Maximum degree at most `Δ`. -/
def MaxDegLe (Δ : ℕ) : Prop := ∀ v, G.deg v ≤ Δ

/-- The degree of `v` in the edge set `F`. -/
def degIn (F : Finset (Fin G.m)) (v : Fin G.n) : ℕ := (F.filter (G.IsEnd v)).card

/-- `F ⊆ E` is an **even subgraph**: every vertex has even degree in `F` (§2.3, Eq. (6), p. 8). -/
def IsEven (F : Finset (Fin G.m)) : Prop := ∀ v, Even (G.degIn F v)

/-- `G` contains a cycle, written as: `G` has a nonempty even subgraph (§4, p. 18: a forest has no
nonempty even subgraph, and a cycle is one). -/
def HasCycle : Prop := ∃ F : Finset (Fin G.m), F.Nonempty ∧ G.IsEven F

/-- `m=(σ)`: the number of edges whose endpoints have equal spins (p. 1). Spins `{−1, 1}` are
encoded as `Bool`. -/
def eqCount (σ : Fin G.n → Bool) : ℕ :=
  (Finset.univ.filter fun e => σ (G.ends e).1 = σ (G.ends e).2).card

/-- The **zero-field ferromagnetic Ising law** `µ_Ising(σ) = Z⁻¹ β^{m=(σ)}` on `σ ∈ {−1,1}^V`
(p. 1). -/
def isingLaw (β : ℝ) (σ : Fin G.n → Bool) : ℝ :=
  β ^ G.eqCount σ / ∑ σ' : Fin G.n → Bool, β ^ G.eqCount σ'

/-- The Ising weight with edge activities `β_e`: `∏_{e = uv} β_e^{1{σ_u = σ_v}}` (§2.3, p. 8). -/
def isingWeightGen (β : Fin G.m → ℝ) (σ : Fin G.n → Bool) : ℝ :=
  ∏ e, if σ (G.ends e).1 = σ (G.ends e).2 then β e else 1

/-- The zero-field Ising law with edge activities `β_e ≥ 1` (§2.3, p. 8). -/
def isingLawGen (β : Fin G.m → ℝ) (σ : Fin G.n → Bool) : ℝ :=
  G.isingWeightGen β σ / ∑ σ' : Fin G.n → Bool, G.isingWeightGen β σ'

/-- The partition function `Z₂ = ∑_{F even} ∏_{e ∈ F} t_e` of (6). -/
def evenZ (t : Fin G.m → ℝ) : ℝ :=
  ∑ F : Finset (Fin G.m), if G.IsEven F then ∏ e ∈ F, t e else 0

/-- The **even-subgraph law** (6), p. 8:
`π₂(F) = Z₂⁻¹ 1{deg_F(v) even for every v} ∏_{e ∈ F} t_e`, `F ⊆ E`. -/
def evenLaw (t : Fin G.m → ℝ) (F : Finset (Fin G.m)) : ℝ :=
  if G.IsEven F then (∏ e ∈ F, t e) / G.evenZ t else 0

end IncGraph

end

end NearLinIsing


