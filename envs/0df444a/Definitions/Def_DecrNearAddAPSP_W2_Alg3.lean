-- Prove2me | Definitions.Def_DecrNearAddAPSP_W2_Alg3
-- name    : DecrNearAddAPSP_W2_Alg3
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:13:17.603321+00:00
-- url     : https://prove2.me/theorems/eec9c58d-ab1f-4ef2-86b4-9a9c39cd1a94
-- title:
--   Algorithm 3 (+2W₂-APASP up to depth τ): E^τ_S, auxiliary pivots, the graphs F(u) and F̂(u), their monotone ES-tree levels and d[u, v]
-- statement:
--   Algorithm 3 (p. 29) is described here as a deterministic process, given the graphs $G_t$ of a decremental instance, a sampled set $S\subseteq V$, a depth $\tau$ and a pivot selector.
--
--   1. **Pivot tree** (ES-tree from an auxiliary source $\hat s$ joined to $S$ by $0$-weight edges, depth $2\tau$): $e_t(y)=\delta_t(y,S)$ if this is at most $2\tau$, else $\infty$. A **valid pivot selector** assigns to each $y$ with $e_t(y)<\infty$ a pivot $p_t(y)\in S$ with $\delta_t(y,p_t(y))=\delta_t(y,S)$ (ties arbitrary) and no pivot otherwise.
--   2. **Pivot ES-trees** (one per $s\in S$, depth $2\tau$): $L_{s,t}(x)=\delta_t(s,x)$ if at most $2\tau$, else $\infty$.
--   3. **The bounded hierarchy-induced edge set** $E_S:=E^\tau_S$ (p. 27), read dynamically: an edge $(x,y)$ of $G_t$ belongs to $E^\tau_{S,t}$ iff at some time $r\le t$ and for some endpoint $z$ of it, $w_r(x,y)<\min\{\delta_r(z,S),\tau+1\}$ ("once an edge enters $E^\tau_S$, it remains there until deleted from $G$"). Its weight is the current $w_t$.
--   4. **Auxiliary pivots** $\tilde S=\{\tilde p(y):y\in V\}$, one new vertex per $y$. The edge $\tilde p(y)\to y$ of $Q_{\tilde S}$ has weight $e_t(y)$. The edge $u\to\tilde p(y)$ of $\{u\}\times\tilde S$ has weight $\max_{r\le t}L_{p_r(y),r}(u)$, a term being $\infty$ when $p_r(y)$ is undefined: the page updates these weights "only if the distance increases. Otherwise, we leave the previous weight" (p. 31).
--   5. $F_t(u)=E_S\cup Q_{\tilde S}\cup(\{u\}\times\tilde S)\cup E_t(u)$ on $V\cup\tilde S$, with the edges of $E_S$ and of $E_t(u)$ in both directions; $\ell_{u,t}$ are the monotone ES-tree levels from $u$ in $F(u)$ up to depth $2\tau$ (the "first" trees).
--   6. $\hat F_t(u)=E_S\cup Q_{\tilde S}\cup(\{u\}\times\tilde S)\cup(\{u\}\times V)$, where the edge $u\to v$ of $\{u\}\times V$ has weight $\ell_{v,t}(u)$, the level of $u$ in $v$'s first tree at the same time (the phases run pivot trees, then all first trees, then all second trees); $\hat\ell_{u,t}$ are the monotone ES-tree levels from $u$ in $\hat F(u)$ up to depth $2\tau$.
--   7. The estimate is
--   $$
--   d_t[u,v]=\min\{\hat\ell_{u,t}(v),\ \hat\ell_{v,t}(u)\}.
--   $$
--
--   Parallel edges are merged into one edge with the minimum weight; weight $\infty$ means no edge. This process is the subject of Lemmas 5.7 and 5.8.
--
--   **Formalization Note** The vertex set $V\cup\tilde S$ is `Fin n ⊕ Fin n` (`inl x` = $x$, `inr y` = $\tilde p(y)$). The edges of $Q_{\tilde S}$, $\{u\}\times\tilde S$ and $\{u\}\times V$ point away from the root $u$, as in the proof's paths $u\to\tilde p(y)\to y\to\cdots\to v$; their reverse copies would only add $0$-weight 2-cycles, which can hold up a monotone level without support from the root. The selector is a function of time and vertex, and the lemmas quantify over all valid ones.
-- source:
--   Koveshi, Roditty, Sapir, First Near-Additive All-Pairs Approximate Shortest Paths in Decremental Weighted Graphs, arXiv:2611.04635 (PDF sha256 6bb2b230…), pp. 27–31, §5.1 (E^τ_S, p. 27) and §5.2, Algorithm 3 (p. 29)

import Mathlib
import Definitions.Def_DecrNearAddAPSP_W2_Graphs
import Definitions.Def_DecrNearAddAPSP_W2_Dynamic
import Definitions.Def_DecrNearAddAPSP_W2_MonoES

namespace DecrNearAddAPSP.W2

/-! # Algorithm 3: `+2W₂`-APASP up to depth `τ` — the bounded hierarchy-induced edge set `E^τ_S`,
the auxiliary pivots, the graphs `F(u)` and `F̂(u)`, their monotone ES-tree levels, and `d[u, v]`

Koveshi, Roditty, Sapir, *First Near-Additive All-Pairs Approximate Shortest Paths in Decremental
Weighted Graphs*, arXiv:2611.04635 (PDF sha256 6bb2b230…), §5.1 p. 27 (PDF 29: `E^τ_S`), §5.2
pp. 28–31 (PDF 30–33), Algorithm 3 (p. 29, PDF 31).

**Formalization Note.** The run is a deterministic process given the graph sequence `G_t`, the
sampled set `S`, the depth `τ` and a pivot selector; the lemmas hold for every outcome of `S` and
every selector.
* *Pivot tree* (ES-tree from `ŝ` up to depth `2τ`): `e_t(y) = δ_t(y, S)` if `≤ 2τ`, else `∞`. A
  pivot selector picks `p_t(y) ∈ argmin_{s ∈ S} δ_t(y, s)` when `e_t(y) < ∞` and no pivot otherwise
  (ties arbitrary).
* *Pivot ES-trees* (one per `s ∈ S`, depth `2τ`): `L_{s,t}(x) = δ_t(s, x)` if `≤ 2τ`, else `∞`.
* `E_S := E^τ_S` read dynamically: `(x, y) ∈ E^τ_{S,t}` iff `(x, y)` is an edge of `G_t` and, for some
  `r ≤ t` and some endpoint `z`, `w_r(x, y) < min{δ_r(z, S), τ + 1}` (p. 27: "once an edge enters
  `E^τ_S`, it remains there until deleted from `G`"); its weight is the current `w_t`.
* The vertex set of `F(u)` and `F̂(u)` is `V ⊕ S̃`, `inl x` the vertex `x`, `inr y` the auxiliary pivot
  `p̃(y)` (one per `y ∈ V`). Edges of `E_S` and of `E_t(u)` go both ways; the `Q_{S̃}` edge goes
  `p̃(y) → y` with weight `e_t(y)`; the `{u} × S̃` edge goes `u → p̃(y)` with weight
  `max_{r ≤ t} L_{p_r(y), r}(u)` (`∞` once `p_r(y)` is undefined): the page updates these weights
  "only if the distance increases. Otherwise, we leave the previous weight" (p. 31). In `F̂(u)` the
  edges `E_t(u)` are replaced by `u → v` with weight `ℓ_{v,t}(u)`, the level of `u` in `v`'s first
  monotone ES-tree at the same time `t` (phases: pivot trees, then all first trees, then all second
  trees). Parallel edges are merged by taking the minimum weight; weight `∞` means no edge.
* `ℓ_u` and `ℓ̂_u` are the monotone ES-tree levels (`monoLevels`) from `u` up to depth `2τ` in
  `F(u)` and `F̂(u)`, and `d_t[u, v] = min{ℓ̂_{u,t}(v), ℓ̂_{v,t}(u)}`. -/

/-- The data of a run of Algorithm 3: the initial graph, the update sequence, the sampled set `S`,
the depth `τ`, and the pivot selector `piv t y` (the pivot `p_t(y)` at time `t`, if any). -/
structure Alg3 (n : ℕ) where
  /-- The initial graph `G_0`. -/
  G₀ : WGraph (Fin n)
  /-- The decremental update sequence. -/
  σ : List (Upd n)
  /-- The sampled set `S`. -/
  S : Finset (Fin n)
  /-- The depth parameter `τ`. -/
  τ : ℕ
  /-- The pivot selector: `piv t y` is `p_t(y)`, or `none` when `y` has no pivot. -/
  piv : ℕ → Fin n → Option (Fin n)

namespace Alg3

variable {n : ℕ} (A : Alg3 n)

/-- `G_t`. -/
def G (t : ℕ) : WGraph (Fin n) := graphAt A.G₀ A.σ t

/-- The pivot-tree value `e_t(y)`: `δ_t(y, S)` if it is at most `2τ`, else `∞`. -/
noncomputable def pivDist (t : ℕ) (y : Fin n) : ℕ∞ :=
  if (A.G t).distTo y A.S ≤ (2 * A.τ : ℕ) then (A.G t).distTo y A.S else ⊤

/-- The level of `x` in the ES-tree from `s ∈ S` up to depth `2τ`: `δ_t(s, x)` if `≤ 2τ`, else
`∞`. -/
noncomputable def srcLevel (t : ℕ) (s x : Fin n) : ℕ∞ :=
  if (A.G t).dist s x ≤ (2 * A.τ : ℕ) then (A.G t).dist s x else ⊤

/-- The pivot selector is valid: at every time `t`, every `y` with `e_t(y) < ∞` gets a pivot
`p_t(y) ∈ S` minimizing `δ_t(y, ·)` over `S`, and every `y` with `e_t(y) = ∞` gets none. -/
def ValidPivots : Prop :=
  ∀ t y, (A.pivDist t y ≠ ⊤ → ∃ s, A.piv t y = some s ∧ (A.G t).IsPivot A.S y s) ∧
    (A.pivDist t y = ⊤ → A.piv t y = none)

/-- The weight of the auxiliary edge `u → p̃(y)` at time `t`: `max_{r ≤ t} L_{p_r(y), r}(u)`, with
the term `∞` when `p_r(y)` is undefined. -/
noncomputable def auxW (t : ℕ) (u y : Fin n) : ℕ∞ :=
  ⨆ r ∈ Finset.range (t + 1),
    match A.piv r y with
    | some s => A.srcLevel r s u
    | none => ⊤

/-- `(x, y) ∈ E^τ_{S,t}`: an edge of `G_t` that, at some time `r ≤ t` and for some endpoint `z`,
had `w_r(x, y) < min{δ_r(z, S), τ + 1}`. -/
def InHier (t : ℕ) (e : Sym2 (Fin n)) : Prop :=
  e ∈ (A.G t).adj.edgeSet ∧
    ∃ r ≤ t, ∃ z ∈ e, ((A.G r).wt e : ℕ∞) < min ((A.G r).distTo z A.S) ((A.τ : ℕ∞) + 1)

open Classical in
/-- The weight of `x → y` (`x, y ∈ V`) in the edge set `E^τ_{S,t}`: `w_t(x, y)` if
`{x, y} ∈ E^τ_{S,t}`, else `∞`. -/
noncomputable def hierW (t : ℕ) (x y : Fin n) : ℕ∞ :=
  if A.InHier t s(x, y) then ((A.G t).wt s(x, y) : ℕ∞) else ⊤

open Classical in
/-- `F_t(u) = E_S ∪ Q_{S̃} ∪ ({u} × S̃) ∪ E_t(u)` on `V ⊕ S̃`. -/
noncomputable def F (t : ℕ) (u : Fin n) : DGraph (Fin n ⊕ Fin n)
  | .inl x, .inl y =>
      min (A.hierW t x y)
        (if (x = u ∨ y = u) ∧ (A.G t).adj.Adj x y then ((A.G t).wt s(x, y) : ℕ∞) else ⊤)
  | .inr y, .inl y' => if y = y' then A.pivDist t y else ⊤
  | .inl x, .inr y => if x = u then A.auxW t u y else ⊤
  | .inr _, .inr _ => ⊤

/-- The first-round levels `ℓ_{u,t}`: the monotone ES-tree of `F(u)` rooted at `u`, up to depth
`2τ`. -/
noncomputable def firstLevels (u : Fin n) (t : ℕ) : Fin n ⊕ Fin n → ℕ∞ :=
  monoLevels (fun t => A.F t u) (Sum.inl u) (2 * A.τ) t

open Classical in
/-- `F̂_t(u) = E_S ∪ Q_{S̃} ∪ ({u} × S̃) ∪ ({u} × V)`, the edge `u → v` of `{u} × V` with weight
`ℓ_{v,t}(u)`. -/
noncomputable def Fhat (t : ℕ) (u : Fin n) : DGraph (Fin n ⊕ Fin n)
  | .inl x, .inl y =>
      min (A.hierW t x y) (if x = u then A.firstLevels y t (Sum.inl u) else ⊤)
  | .inr y, .inl y' => if y = y' then A.pivDist t y else ⊤
  | .inl x, .inr y => if x = u then A.auxW t u y else ⊤
  | .inr _, .inr _ => ⊤

/-- The second-round levels `ℓ̂_{u,t}`: the monotone ES-tree of `F̂(u)` rooted at `u`, up to depth
`2τ`. -/
noncomputable def secondLevels (u : Fin n) (t : ℕ) : Fin n ⊕ Fin n → ℕ∞ :=
  monoLevels (fun t => A.Fhat t u) (Sum.inl u) (2 * A.τ) t

/-- The estimate `d_t[u, v] = min{ℓ̂_{u,t}(v), ℓ̂_{v,t}(u)}`. -/
noncomputable def est (t : ℕ) (u v : Fin n) : ℕ∞ :=
  min (A.secondLevels u t (Sum.inl v)) (A.secondLevels v t (Sum.inl u))

end Alg3

end DecrNearAddAPSP.W2


