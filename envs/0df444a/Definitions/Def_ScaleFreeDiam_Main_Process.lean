-- Prove2me | Definitions.Def_ScaleFreeDiam_Main_Process
-- name    : ScaleFreeDiam_Main_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:10:30.374285+00:00
-- url     : https://prove2.me/theorems/f1581223-87a1-4f6e-902a-4a4f2966bd20
-- title:
--   §2–§3, pp. 7–9 — the preferential-attachment process G₁^N, the graph G_mⁿ, distances, 'almost every', and the bound of Lemma 4
-- statement:
--   This file fixes the random graph model of Bollobás and Riordan, *The diameter of a scale-free random graph* (2004), §2.
--
--   **The process $G_1^N$.** Vertices are $1,2,\dots,N$. Vertex $t$ sends exactly one edge to a vertex $g_t\in\{1,\dots,t\}$. Given $g_1,\dots,g_{t-1}$, the target is chosen with
--   $$
--   \mathbb P(g_t=i\mid g_1,\dots,g_{t-1})=\frac{1+\#\{s<t:\ g_s=i\}}{2t-1},\qquad 1\le i\le t .
--   $$
--   For $i<t$ the numerator is the degree $d_{G_1^{t-1}}(i)$ of $i$ in the graph built so far (its own edge counts one and every earlier edge into $i$ counts one, a loop at $i$ counting twice); for $i=t$ it is $1$, the "outward half" of the new edge. The probability of a whole sequence $(g_1,\dots,g_N)$ is the product of these factors, and $\mathbb P_{G_1^N}(P)$ is the total weight of the sequences with property $P$. The accessor $g_j$ is available for $1\le j\le N$.
--
--   **The graph $G_1^N$** joins $t$ and $g_t$ for each $t$.
--
--   **The graph $G_m^n$** is formed from $G_1^{mn}$ by identifying the vertices $(k-1)m+1,\dots,km$ of $G_1^{mn}$ into the vertex $k$ of $G_m^n$, for $k=1,\dots,n$. A random $G_m^n\in\mathcal G_m^n$ has the induced law.
--
--   **Distances.** $\mathrm{AllWithin}(G,x)$ says that any two vertices of $G$ are joined by a walk of length at most $x$, i.e. $\operatorname{diam}(G)\le x$, a disconnected graph having infinite diameter.
--
--   **Almost every.** For fixed $m$, almost every $G_m^n\in\mathcal G_m^n$ has property $P_n$ if $\mathbb P(G_m^n \text{ has } P_n)\to1$ as $n\to\infty$.
--
--   **The bound of Lemma 4.** For a constant $C$, $\mathrm{Lemma4Bound}(C)$ states: for every $N$ and every loopless graph $S$ on $[N]$ in which each vertex is joined to at most one earlier and at most two later vertices,
--   $$
--   \mathbb P\big(S\subset G_1^N\big)\le C^{e(S)}\prod_{ij\in E(S)}\frac1{\sqrt{ij}},
--   $$
--   where $S\subset G_1^N$ means that every pair joined in $S$ is joined in $G_1^N$ (not an isomorphic copy).
--
--   These objects carry every statement of the mission: the goal (Theorem 1), the lower-bound chain of §4 and the coupling of §6.
--
--   **Formalization Note** Vertices are stored 0-based (`Fin N`, vertex `t` is the paper's `t+1`); statements read 1-based labels through the accessor `tgt g j` (the paper's $g_j$, `0` outside $1\le j\le N$) and explicit `+1`s. The paper's graphs have loops and multiple edges; distances and connectivity depend only on the underlying simple graph, so `G1graph` and `Gm` are Mathlib `SimpleGraph`s with loops and multiplicities dropped. Probabilities are finite weighted sums with the exact weights above.
-- source:
--   Bollobás and Riordan, The diameter of a scale-free random graph, Combinatorica 24 (2004), pp. 7–9, §2 (the model) and §3 ('almost every'); p. 9, §4 (g_j); p. 13, Lemma 4

import Mathlib

namespace ScaleFreeDiam.Main

open Filter Topology
open scoped Classical

/-- An outcome of the process `G₁^N`: vertex `t` (0-based; the paper's vertex `t + 1`) sends
its one edge to the vertex `g t ≤ t` (0-based; the paper's `g_{t+1} = (g t) + 1`). -/
abbrev Seq (N : ℕ) : Type := (t : Fin N) → Fin (t.val + 1)

/-- The conditional probability of the `t`-th step (0-based) of `G₁^N`, given the past:
`(1 + #{s < t : g s = g t}) / (2(t+1) − 1)`. For a target `i < t` the numerator is the
degree of `i` in `G₁^{t}` (paper's `G₁^{t-1}` in 1-based time): its own edge counts one, and
every earlier edge into `i` counts one (a loop at `i` counting twice). For the target `t`
itself the numerator is `1`, the "outward half" of the new edge. -/
noncomputable def stepWeight {N : ℕ} (g : Seq N) (t : Fin N) : ℝ :=
  (1 + ((Finset.univ.filter (fun s : Fin N => s < t ∧ (g s).val = (g t).val)).card : ℝ)) /
    (2 * (t.val : ℝ) + 1)

/-- The probability of a whole attachment sequence: the product of the step weights. -/
noncomputable def weight {N : ℕ} (g : Seq N) : ℝ :=
  ∏ t : Fin N, stepWeight g t

/-- `ℙ(P)` for the random graph process `G₁^N`. -/
noncomputable def probG1 (N : ℕ) (P : Seq N → Prop) : ℝ :=
  ∑ g : Seq N, if P g then weight g else 0

/-- The 1-based accessor: `tgt g j` is the paper's `g_j`, the vertex (in `1, …, N`) to which
vertex `j` sends its edge, for `1 ≤ j ≤ N`; it is `0` (junk) outside that range. -/
def tgt {N : ℕ} (g : Seq N) (j : ℕ) : ℕ :=
  if h : 1 ≤ j ∧ j ≤ N then (g ⟨j - 1, by omega⟩).val + 1 else 0

/-- The (simple-graph shadow of the) graph `G₁^N` on `Fin N`: `t` is joined to `g t`;
loops are dropped. -/
def G1graph {N : ℕ} (g : Seq N) : SimpleGraph (Fin N) :=
  SimpleGraph.fromEdgeSet {e | ∃ t : Fin N, e = s(t, Fin.castLE t.isLt (g t))}

/-- The (simple-graph shadow of the) graph `G_mⁿ`, formed from `G₁^{mn}` by identifying the
0-based vertices `km, …, km + m − 1` into vertex `k` (0-based; the paper's vertex `k + 1`).
Loops and multiple edges are dropped. -/
def Gm (m n : ℕ) (g : Seq (m * n)) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ t : Fin (m * n),
    e = s(⟨t.val / m, Nat.div_lt_of_lt_mul t.isLt⟩,
          ⟨(g t).val / m,
            Nat.div_lt_of_lt_mul (lt_of_le_of_lt (Nat.lt_succ_iff.mp (g t).isLt) t.isLt)⟩)}

/-- `ℙ(P)` for a random `G_mⁿ ∈ 𝒢_mⁿ`. -/
noncomputable def probGm (m n : ℕ) (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  probG1 (m * n) (fun g => P (Gm m n g))

/-- Every two vertices of `G` are joined by a walk of length at most `x` ("diam G ≤ x",
with a disconnected graph counted as having infinite diameter). -/
def AllWithin {V : Type*} (G : SimpleGraph V) (x : ℝ) : Prop :=
  ∀ u v : V, ∃ p : G.Walk u v, (p.length : ℝ) ≤ x

/-- "Almost every `G_mⁿ ∈ 𝒢_mⁿ` has property `P n`": `ℙ(G_mⁿ has P n) → 1` as `n → ∞`, `m`
fixed. -/
def AlmostEvery (m : ℕ) (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) : Prop :=
  Tendsto (fun n => probGm m n (P n)) atTop (𝓝 1)

/-- The conclusion of Lemma 4 for the constant `C`: for every `N` and every graph `S` on
`[N]` (loopless, as a `SimpleGraph`) in which each vertex is joined to at most one earlier
and at most two later vertices,
`ℙ(S ⊂ G₁^N) ≤ C^{e(S)} ∏_{ij ∈ E(S)} 1/√(ij)` with 1-based labels `i, j`. The edges of `S`
are listed as the pairs `u < v` with `S.Adj u v`. -/
def Lemma4Bound (C : ℝ) : Prop :=
  ∀ (N : ℕ) (S : SimpleGraph (Fin N)),
    (∀ v : Fin N, (Finset.univ.filter (fun u => S.Adj v u ∧ u < v)).card ≤ 1) →
    (∀ v : Fin N, (Finset.univ.filter (fun u => S.Adj v u ∧ v < u)).card ≤ 2) →
    probG1 N (fun g => S ≤ G1graph g) ≤
      C ^ ((Finset.univ : Finset (Fin N × Fin N)).filter
            (fun p => p.1 < p.2 ∧ S.Adj p.1 p.2)).card *
        ∏ p ∈ (Finset.univ : Finset (Fin N × Fin N)).filter
            (fun p => p.1 < p.2 ∧ S.Adj p.1 p.2),
          1 / Real.sqrt (((p.1.val : ℝ) + 1) * ((p.2.val : ℝ) + 1))

end ScaleFreeDiam.Main


