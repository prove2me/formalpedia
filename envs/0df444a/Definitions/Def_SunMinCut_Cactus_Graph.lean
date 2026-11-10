-- Prove2me | Definitions.Def_SunMinCut_Cactus_Graph
-- name    : SunMinCut_Cactus_Graph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:22:02.698288+00:00
-- url     : https://prove2.me/theorems/cce60f18-6fca-45e6-b964-7fe0f0f74217
-- title:
--   Weighted multigraph, cut capacity, λ, minimum cuts, spanning-tree cuts, partition strength and capping
-- statement:
--   The input graph has vertices $V=\{0,\dots,n-1\}$ and $m$ stored edge records; record $e$ has an unordered endpoint pair and a real capacity $w_e$ (the published `CombOpt.MinCut.CapGraph` on `Fin n`, `Fin m`, which bundles no condition; parallel records and loops are allowed). For $S\subseteq V$, $w(\delta S)=\sum_{e\in\delta(S)}w_e$ (published `delta`, `uSum`). A **shore** is a set with $\emptyset\ne S\ne V$. $\lambda$ is the published `globalMinCut` (the minimum of $w(\delta S)$ over shores), read as a real number (`lam`); $S$ is a **minimum cut** if it is a shore with $w(\delta S)=\lambda$. A cut is the unordered bipartition $\{S,V\setminus S\}$ (`bip`), and `minCuts G` is the family of minimum cuts as bipartitions.
--
--   `Positive`: every $w_e>0$. `Connected`: the support graph ($a\sim b$ iff $a\ne b$ and some record joins them) is connected. `Aggregated`: no loops and no two records with the same endpoint pair, so the $m$ records are the $s$ positive endpoint pairs of §2. `supportCount` is $s$, the number of distinct endpoint pairs of non-loop records.
--
--   For a spanning tree $T$ on $V$ (a `SimpleGraph`, not necessarily a subgraph of $G$), `crossT T S` is the number of tree edges with exactly one end in $S$. The fundamental shore of a tree edge $f$ is the set of vertices reachable from one end of $f$ in $T-f$; $d_f$ is the capacity of the original edges crossing it, and $d_0=\min_f d_f$ over the tree edges.
--
--   For a partition $P$ of $V$ (`Finpartition`), $w(\delta P)$ is the capacity of the records joining different blocks, and the **partition strength** is $\sigma(G)=\min_{|P|\ge 2} w(\delta P)/(|P|-1)$. For $c_0$, the capped graph has capacities $v_e=\min(w_e,c_0)$, the rate graph $q_e=v_e/c_0$, and $\rho=\sigma/c_0$. `CoarseCut G c0` says $c_0$ is the capacity of an actual cut (some shore $S$ has $w(\delta S)=c_0$) and $\lambda\le c_0<9\lambda/4$ (the guarantee of Lemma 2.3).
--
--   **Formalization Note** `lam`, `sigma` and `d0` are real minima written as `untopD 0` / `sInf` over finite sets; they are nonempty exactly when $n\ge 2$ (and $T$ is a spanning tree), which every theorem assumes, so the default values are never used.
-- source:
--   Sun 2026, doi:10.5281/zenodo.23915020, §1.2 p. 3, §2 p. 7, §2.1 p. 7, §2.2 pp. 8–9

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph
import Definitions.Def_CombOpt_MinCut_CapGraph_uSum
import Definitions.Def_CombOpt_MinCut_CapGraph_delta
import Definitions.Def_CombOpt_MinCut_CapGraph_globalMinCut

open CombOpt.MinCut

namespace SunMinCut.Cactus

/-- The input graph of Sun 2026 (doi:10.5281/zenodo.23915020, §2, p. 7): `n` vertices `0, …, n-1`
and `m` stored edge records `0, …, m-1`; record `e` has the unordered endpoint pair `G.ends e`
and the real capacity `w_e = G.u e`. Parallel records and loops are allowed (a loop lies in no
cut). This is the published `CombOpt.MinCut.CapGraph`, which bundles no condition. -/
abbrev Graph (n m : ℕ) := CapGraph (Fin n) (Fin m)

variable {n m : ℕ}

/-- `w(δS) = Σ_{e ∈ δ(S)} w_e`, the capacity of the cut with shore `S`. -/
noncomputable def cutw (G : Graph n m) (S : Finset (Fin n)) : ℝ := G.uSum (G.delta S)

/-- A shore of a cut: `∅ ≠ S ≠ V`. -/
def Nontriv (S : Finset (Fin n)) : Prop := S.Nonempty ∧ S ≠ Finset.univ

/-- `λ` as a real number: the published `globalMinCut` (a value in `WithTop ℝ`, finite for
`n ≥ 2`, which every statement assumes). -/
noncomputable def lam (G : Graph n m) : ℝ := WithTop.untopD 0 G.globalMinCut

/-- `S` is the shore of a minimum cut: `S` is nontrivial and `w(δS) = λ(G)`. -/
def IsMinCut (G : Graph n m) (S : Finset (Fin n)) : Prop :=
  Nontriv S ∧ ((cutw G S : ℝ) : WithTop ℝ) = G.globalMinCut

/-- All capacities are positive. -/
def Positive (G : Graph n m) : Prop := ∀ e, 0 < G.u e

/-- The support graph: `a ~ b` iff `a ≠ b` and some record joins `a` and `b`. -/
def supportGraph (G : Graph n m) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun a b => ∃ e, G.ends e = s(a, b)

/-- `G` is connected. -/
def Connected (G : Graph n m) : Prop := (supportGraph G).Connected

/-- The input has already been aggregated (§2, p. 7): no loops and no two records with the same
endpoint pair, so the `m` records are the `s` positive endpoint pairs. -/
def Aggregated (G : Graph n m) : Prop :=
  (∀ e, ¬ (G.ends e).IsDiag) ∧ Function.Injective G.ends

open Classical in
/-- `s`, the number of distinct endpoint pairs of non-loop records (§2, p. 7). -/
noncomputable def supportCount (G : Graph n m) : ℕ :=
  ((Finset.univ.filter fun e => ¬ (G.ends e).IsDiag).image G.ends).card

/-- A cut as a nontrivial unordered bipartition `{S, V ∖ S}` (§1.2, p. 3). -/
def bip (S : Finset (Fin n)) : Finset (Finset (Fin n)) := {S, Finset.univ \ S}

/-- The family of all minimum cuts, as unordered bipartitions. -/
def minCuts (G : Graph n m) : Set (Finset (Finset (Fin n))) := bip '' {S | IsMinCut G S}

/-- An unordered vertex pair `e` crosses the shore `S`: one end in `S`, one outside. -/
def CrossesShore (S : Finset (Fin n)) (e : Sym2 (Fin n)) : Prop :=
  ∃ a ∈ e, a ∈ S ∧ ∃ b ∈ e, b ∉ S

open Classical in
/-- The number of edges of the tree `T` crossing the cut with shore `S`. -/
noncomputable def crossT (T : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℕ :=
  (T.edgeFinset.filter (CrossesShore S)).card

open Classical in
/-- The fundamental shore of the tree edge `f` of `T`: the vertices reachable from the first end
of `f` in `T - f` (§2.1, p. 7). -/
noncomputable def fundShore (T : SimpleGraph (Fin n)) (f : Sym2 (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => (T.deleteEdges {f}).Reachable (Quot.out f).1 v

/-- `d_f = w(A_f)`, the capacity of the original edges crossing the fundamental cut of `f`. -/
noncomputable def dEdge (G : Graph n m) (T : SimpleGraph (Fin n)) (f : Sym2 (Fin n)) : ℝ :=
  cutw G (fundShore T f)

/-- `d_0 = min_f d_f` over the tree edges `f` of `T` (§2.1, p. 7). For a spanning tree on
`n ≥ 2` vertices the set is finite and nonempty. -/
noncomputable def d0 (G : Graph n m) (T : SimpleGraph (Fin n)) : ℝ :=
  sInf {x | ∃ f ∈ T.edgeSet, x = dEdge G T f}

/-- A partition of `V` into blocks. -/
abbrev Partition (n : ℕ) := Finpartition (Finset.univ : Finset (Fin n))

/-- The record `e` joins two different blocks of `P`. -/
def CrossesPart (G : Graph n m) (P : Partition n) (e : Fin m) : Prop :=
  ∃ a ∈ G.ends e, ∃ b ∈ G.ends e, P.part a ≠ P.part b

open Classical in
/-- `w(δP)`, the capacity between different blocks of `P` (§2.2, p. 8). -/
noncomputable def partCut (G : Graph n m) (P : Partition n) : ℝ :=
  ∑ e ∈ Finset.univ.filter (CrossesPart G P), G.u e

/-- The partition strength `σ(G) = min_{|P| ≥ 2} w(δP)/(|P| − 1)` (§2.2, p. 8). The set is
finite, and nonempty for `n ≥ 2`. -/
noncomputable def sigma (G : Graph n m) : ℝ :=
  sInf {x | ∃ P : Partition n, 2 ≤ P.parts.card ∧ x = partCut G P / ((P.parts.card : ℝ) - 1)}

/-- The capped graph `v_e = min(w_e, c0)` (§2.2, p. 8). -/
noncomputable def capped (G : Graph n m) (c0 : ℝ) : Graph n m where
  ends := G.ends
  u e := min (G.u e) c0

/-- The normalized capped capacities `q_e = min(w_e, c0)/c0` (§2.2, p. 8). -/
noncomputable def rates (G : Graph n m) (c0 : ℝ) : Graph n m where
  ends := G.ends
  u e := min (G.u e) c0 / c0

/-- `ρ = σ/c0` (§2.2, p. 8). -/
noncomputable def rho (G : Graph n m) (c0 : ℝ) : ℝ := sigma G / c0

/-- `c0` is the capacity of an actual cut with `λ ≤ c0 < 9λ/4`, the guarantee of Lemma 2.3. -/
def CoarseCut (G : Graph n m) (c0 : ℝ) : Prop :=
  (∃ S, Nontriv S ∧ cutw G S = c0) ∧ lam G ≤ c0 ∧ c0 < 9 / 4 * lam G

end SunMinCut.Cactus


