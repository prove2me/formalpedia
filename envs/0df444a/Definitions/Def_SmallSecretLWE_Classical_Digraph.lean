-- Prove2me | Definitions.Def_SmallSecretLWE_Classical_Digraph
-- name    : SmallSecretLWE_Classical_Digraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:26:26.282251+00:00
-- url     : https://prove2.me/theorems/a4b6b14d-88e6-41b0-9fd5-93983f3c925e
-- title:
--   Directed multigraphs: degrees, the out-degree law $\nu$, random walks, good walks, deficient colorings, $\mathrm{Single}$
-- statement:
--   A **directed multigraph** has a finite vertex set $V$, a finite set $E$ of edge occurrences, and maps $\mathrm{src},\mathrm{tgt}:E\to V$ (parallel edges allowed). $\text{out-deg}(v)$ and $\text{in-deg}(v)$ count occurrences. The **out-degree law** is $\nu(v)=\text{out-deg}(v)/|E|$ (a law when $|E|>0$), and $\Delta=|E|/|V|$ is the **average degree**.
--
--   A **walk** of length $T$ from $w_0$ is a sequence of edges $e_1,\dots,e_T$ with $\mathrm{src}(e_t)=w_{t-1}$, $w_t=\mathrm{tgt}(e_t)$: walks follow edge directions. The **random walk** $\mathrm{walk}^T_{w_0}$ takes at each step a uniformly random outgoing edge occurrence, so a walk has probability
--   $$\prod_{t=1}^{T}\frac{1}{\text{out-deg}(w_{t-1})}.$$
--   A vertex is **bad** if $\text{out-deg}(v)<3\Delta/16$; $\mathrm{Bad}(W)=\#\{0\le i<T: w_i \text{ bad}\}$, and $W$ is **good** if $\mathrm{Bad}(W)<T/4$. A coloring $\Gamma:E\to[m]$ is **$t$-deficient** if every vertex has at most $t$ outgoing and at most $t$ incoming edges of each color. For a multiset $S$ of edges, $\mathrm{Single}(S)$ is the set of colors occurring exactly once in $(\Gamma(e))_{e\in S}$; $W_1\sqcup W_2$ is the multiset union of the edges of two walks.
--
--   **Formalization Note.** `MultiDigraph V E`; a walk is `p : Fin T → E` with `IsWalk w₀ p`, its vertices `walkVtx w₀ p : Fin (T+1) → V`. `walkProb` is $0$ off walks, so from a vertex with no out-edge the walk law loses its mass (a sub-probability) instead of being undefined. Colors are `Fin m`.
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), p. 14, §4 preamble; p. 15, Definitions 4.4, 4.5; p. 16, Definition 4.7; p. 17, Definitions 4.10, 4.12

import Mathlib

set_option autoImplicit false

open scoped Classical

noncomputable section

namespace SmallSecretLWE.Classical

/-!
# Directed multigraphs: degrees, the out-degree law ν, random walks, good walks, colorings

Agrawal, Bagchi, Kumar, *Algorithms for Sparse LWE and LPN with Small Secrets*, STOC 2027
submission (manuscript sha256 8d93a268…): §4 preamble, p. 14; Definitions 4.4, 4.5, p. 15;
Definition 4.7, p. 16; Definitions 4.10, 4.12, p. 17.

* A directed multigraph is a finite vertex type `V`, a finite type `E` of edge occurrences and
  maps `src`, `tgt : E → V`. Parallel edges are allowed; a simple digraph `E ⊆ V × V` is the
  case where `e ↦ (src e, tgt e)` is injective.
* `outDeg v`, `inDeg v` count edge occurrences. `nu v = out-deg(v)/|E|` is the law `ν(v) ∝
  out-deg(v)` of Definition 4.4 (a law when `|E| > 0`). `avgDeg = |E|/|V|` is `Δ`.
* A walk of length `T` from `w₀` is a list of edges `p : Fin T → E` with `src (p i) = w_i`,
  where `w_0 = w₀` and `w_{i+1} = tgt (p i)` (`walkVtx`): walks follow edge directions.
* `walkProb w₀ p` is the probability of the edge sequence `p` under `walk^T_{w₀}` (Definition
  4.5: each step takes a uniformly random outgoing edge occurrence), i.e.
  `∏_i 1/out-deg(w_i)` for a walk and `0` otherwise. From a vertex without outgoing edges no
  step is possible and the mass is lost: `walk^T` is a sub-probability law.
* Definition 4.7: `v` is bad if `out-deg(v) < 3Δ/16`; `Bad(W) = #{0 ≤ i < T : w_i bad}`;
  `W` is good if `Bad(W) < T/4`.
* Definition 4.10: a coloring `Γ : E → [m]` (here `Fin m`) is `t`-deficient if every vertex has
  at most `t` outgoing and at most `t` incoming edge occurrences of every color.
* Definition 4.12: `Single(S)` is the set of colors occurring exactly once in the multiset `S`
  of edges; `walkEdges p` is the multiset of the edges of a walk, and `W₁ ⊔ W₂` is the sum of
  two such multisets.
-/

/-- A directed multigraph on vertices `V` with edge occurrences `E`. -/
structure MultiDigraph (V E : Type*) where
  /-- The tail of an edge. -/
  src : E → V
  /-- The head of an edge. -/
  tgt : E → V

namespace MultiDigraph

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The out-degree: the number of edge occurrences leaving `v`. -/
def outDeg (G : MultiDigraph V E) (v : V) : ℕ := (Finset.univ.filter fun e => G.src e = v).card

/-- The in-degree: the number of edge occurrences entering `v`. -/
def inDeg (G : MultiDigraph V E) (v : V) : ℕ := (Finset.univ.filter fun e => G.tgt e = v).card

/-- The out-degree law `ν(v) = out-deg(v)/|E|` (Definition 4.4). -/
def nu (G : MultiDigraph V E) (v : V) : ℝ := (G.outDeg v : ℝ) / (Fintype.card E : ℝ)

/-- The average out-degree `Δ = |E|/|V|`. -/
def avgDeg (_G : MultiDigraph V E) : ℝ := (Fintype.card E : ℝ) / (Fintype.card V : ℝ)

/-- The vertices `w_0, …, w_T` visited by the edge sequence `p` started at `w₀`:
`w_0 = w₀`, `w_{i+1} = tgt (p i)`. -/
def walkVtx (G : MultiDigraph V E) (w₀ : V) {T : ℕ} (p : Fin T → E) : Fin (T + 1) → V :=
  Fin.cons w₀ fun i => G.tgt (p i)

/-- `p` is a walk of length `T` from `w₀`: each edge leaves the current vertex. -/
def IsWalk (G : MultiDigraph V E) (w₀ : V) {T : ℕ} (p : Fin T → E) : Prop :=
  ∀ i : Fin T, G.src (p i) = G.walkVtx w₀ p i.castSucc

/-- The probability of the edge sequence `p` under `walk^T_{w₀}` (Definition 4.5). -/
def walkProb (G : MultiDigraph V E) (w₀ : V) {T : ℕ} (p : Fin T → E) : ℝ :=
  if G.IsWalk w₀ p then ∏ i, 1 / (G.outDeg (G.src (p i)) : ℝ) else 0

/-- A bad vertex: `out-deg(v) < 3Δ/16` (Definition 4.7). -/
def IsBad (G : MultiDigraph V E) (v : V) : Prop := (G.outDeg v : ℝ) < 3 * G.avgDeg / 16

/-- `Bad(W) = #{0 ≤ i < T : w_i is bad}` (Definition 4.7). -/
def badCount (G : MultiDigraph V E) (w₀ : V) {T : ℕ} (p : Fin T → E) : ℕ :=
  (Finset.univ.filter fun i : Fin T => G.IsBad (G.walkVtx w₀ p i.castSucc)).card

/-- A good walk: `Bad(W) < T/4` (Definition 4.7). -/
def IsGood (G : MultiDigraph V E) (w₀ : V) {T : ℕ} (p : Fin T → E) : Prop :=
  (G.badCount w₀ p : ℝ) < (T : ℝ) / 4

/-- `Γ` is a `t`-deficient edge coloring (Definition 4.10). -/
def IsDeficient (G : MultiDigraph V E) {m : ℕ} (Γ : E → Fin m) (t : ℕ) : Prop :=
  ∀ (v : V) (a : Fin m),
    (Finset.univ.filter fun e => G.src e = v ∧ Γ e = a).card ≤ t ∧
    (Finset.univ.filter fun e => G.tgt e = v ∧ Γ e = a).card ≤ t

end MultiDigraph

/-- The multiset of the edges of an edge sequence. -/
def walkEdges {E : Type*} {T : ℕ} (p : Fin T → E) : Multiset E :=
  Multiset.map p Finset.univ.val

/-- `Single(S)`: the colors occurring exactly once in the multiset `S` of edges
(Definition 4.12). -/
def single {E : Type*} {m : ℕ} (Γ : E → Fin m) (S : Multiset E) : Finset (Fin m) :=
  Finset.univ.filter fun a => (S.map Γ).count a = 1

end SmallSecretLWE.Classical


