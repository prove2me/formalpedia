-- Prove2me | Definitions.Def_CritContracts_Construction
-- name    : CritContracts_Construction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:44:58.136523+00:00
-- url     : https://prove2.me/theorems/a71a8a10-285a-49e1-a4ba-b74a1dba9a5b
-- title:
--   The reduction's bipartite graph instance, its cost-scaled version and the gated, normalized instance
-- statement:
--   Fix a Subset Sum instance $w_1,\dots,w_k$, $T$ with $W$, $L$, $\Delta$, $\varepsilon$ as in Appendix B.1.1. The **auxiliary instance** is the instance of form (2) on the vertices of the reduction's graph with the following edge weights $f_{uv}$ and costs.
--
--   1. **Comparators.** A comparator of offset $\theta$ on side $V$ is a vertex $v$ with $c(v)=(\tfrac12+\Delta\theta)\tfrac1{2\Delta}$ and $f_{u_0v}=\tfrac1{2\Delta}$; on side $U$ the anchor edge comes from $v_0$. The anchors cost $0$. The state vertex $p_i\in V$ is a comparator of offset $-3^{-i}$ and $q_i\in U$ one of offset $1-3^{-i}$.
--   2. **Three-edge paths.** A path of value $M$ from $s$ to $t$ has internal vertices $z$ (side of $t$) and $y$ (side of $s$), edges $f_{sz}=1024\Delta^2M$, $f_{zy}=32\Delta M$, $f_{yt}=M$, and costs $c(z)=(\tfrac12-4\Delta)(1024\Delta^2M+32\Delta M)$, $c(y)=(\tfrac12-4\Delta)(32\Delta M+M)$. For every pair $j<i$ there is a path of value $2\cdot3^{-j}$ from $q_j$ to $p_i$ and one from $p_j$ to $q_i$.
--   3. **Verification.** $c(r_0)=L/4$, $f_{r_0v_0}=\tfrac L2-\tfrac{L(W-T)}{100W^2}$, $f_{r_0p_i}=\tfrac{Lw_i}{100W^2}$; $c(r_1)=\tfrac L4-\Delta L$, $f_{r_1u_0}=\tfrac L2-\tfrac{LT}{100W^2}$, $f_{r_1q_i}=\tfrac{Lw_i}{100W^2}$.
--   4. **Amplification.** $B$ is the total edge weight introduced so far and $D=8\cdot3^kB/\varepsilon$. Add $a\in U$, $b\in V$ with $f_{ab}=D$ and $c(a)=c(b)=(\tfrac12+4\Delta)D$, and a three-edge path of value $12\Delta D$ from $r_1$ to $a$ and one from $r_0$ to $b$.
--
--   The **scaled instance** (Lemma B.9) multiplies every cost by $\beta=1/(1+\varepsilon/2)$. The **gated, normalized instance** (proof of Theorem 3.5) adds an action $g$ of agent 1 with cost $2B$, replaces the reward by
--   $$\hat f(S)=\sum_{u\in U,\ v\in V}f_{uv}\,\mathbf 1[\{u,v,g\}\subseteq S],$$
--   and divides the reward and all costs by $\sum_{u\in U,v\in V}f_{uv}$.
--
--   **Formalization Note** Every number is rational: the weights and costs are computed in $\mathbb Q$ and cast to $\mathbb R$. Each edge is listed once, in one orientation (`edge`), and the reward weight of a pair $(u,v)$, $u\in U$, $v\in V$, is `edge u v + edge v u`. `Bpar` sums every edge before the amplification step (comparator anchor edges, state paths, verification edges); `totalEdge` sums all edges. Items are $0,\dots,k-1$ (the paper's $3^{-i}$ is `tern i`). The gate is the action `none` of `Option (Node k)`.
-- source:
--   Ezra–Feldman–Molina–Schlesinger, Sources of Complexity in Multi-Agent Combinatorial Contracts, STOC 2027 submission (manuscript sha256 430be35c86352b23f05ee0e9126d1318096922c9cbe07d419ee38e38bfcba346), Appendix B.1.1, pp.33–36 (PDF pp.34–37); Lemma B.9, p.38 (PDF p.39): β; proof of Theorem 3.5, p.39 (PDF p.40): the gate and the normalization

import Mathlib
import Definitions.Def_CritContracts_Model
import Definitions.Def_CritContracts_BipInst
import Definitions.Def_CritContracts_Node
import Definitions.Def_CritContracts_SSParams

set_option autoImplicit false

namespace CritContracts

/-! The bipartite graph instance of Appendix B.1.1 (Ezra–Feldman–Molina–Schlesinger, *Sources of
Complexity in Multi-Agent Combinatorial Contracts*, STOC 2027 submission (manuscript sha256
430be35c…), pp.33–36, PDF pp.34–37), built from a Subset Sum instance `ws = [w₁, …, w_k]`, `T`.

**Formalization Note** Every number of the construction is rational; the construction is written
over `ℚ` and cast to `ℝ` in `auxInst`. Items are `0, …, k − 1` here and `1, …, k` in the paper:
the paper's `3^{−i}` for its item `i` is `tern i = 3^{−(i+1)}` for the item written `i` here.
Each edge is listed once, in one orientation, by `edge`; the reward weight of a pair `(u, v)` with
`u ∈ U`, `v ∈ V` is `edge u v + edge v u`. -/

namespace Construction

/-- The weight `wᵢ` of item `i` (0-based) as a rational. -/
def wt (ws : List ℕ) (i : Fin ws.length) : ℚ := (ws.get i : ℚ)

/-- The offset `θ` of a state vertex (p.35): `p_i` has offset `−3^{−i}` and `q_i` has offset
`1 − 3^{−i}` (paper's indexing). -/
def offset {k : ℕ} : Node k → ℚ
  | .p i => -tern i
  | .q i => 1 - tern i
  | _ => 0

/-- The value `M` of a three-edge **state path** (p.35): `2·3^{−j}` for the paths from `q_j` to
`p_i` and from `p_j` to `q_i`, `j < i`; the two final paths get their value `12ΔD` from
`ampVal`, and have value `0` here. -/
def stateVal {k : ℕ} : PathIx k → ℚ
  | .qp e => 2 * tern e.1.1
  | .pq e => 2 * tern e.1.1
  | .ra => 0
  | .rb => 0

/-- The three edges of every three-edge path `s − z − y − t` of value `val π` (p.34):
`f_{sz} = 1024Δ²M`, `f_{zy} = 32ΔM`, `f_{yt} = M`, each listed once in the orientation
`(s, z)`, `(z, y)`, `(y, t)`. -/
def gadgetEdge {k : ℕ} (Δ : ℚ) (val : PathIx k → ℚ) : Node k → Node k → ℚ
  | x, .z π => if x = π.src then 1024 * Δ ^ 2 * val π else 0
  | .z π, .y π' => if π = π' then 32 * Δ * val π else 0
  | .y π, x => if x = π.tgt then val π else 0
  | _, _ => 0

/-- The anchor edges of the comparators (p.34): `f_{u₀ p_i} = 1/(2Δ)` for the comparator `p_i ∈ V`
and `f_{v₀ q_i} = 1/(2Δ)` for the comparator `q_i ∈ U`. -/
def anchorEdge (ws : List ℕ) : Node ws.length → Node ws.length → ℚ
  | .anchor s, .p _ => if s = 0 then 1 / (2 * Delta ws) else 0
  | .anchor s, .q _ => if s = 1 then 1 / (2 * Delta ws) else 0
  | _, _ => 0

/-- The verification edges (p.36): `f_{r₀v₀} = L/2 − L(W−T)/(100W²)`, `f_{r₀p_i} = Lwᵢ/(100W²)`,
`f_{r₁u₀} = L/2 − LT/(100W²)`, `f_{r₁q_i} = Lwᵢ/(100W²)`. -/
def verEdge (ws : List ℕ) (T : ℕ) : Node ws.length → Node ws.length → ℚ
  | .ver s, .anchor s' =>
      if s = 0 ∧ s' = 1 then
        Lpar ws / 2 - Lpar ws * (totalW ws - T) / (100 * totalW ws ^ 2)
      else if s = 1 ∧ s' = 0 then
        Lpar ws / 2 - Lpar ws * T / (100 * totalW ws ^ 2)
      else 0
  | .ver s, .p i => if s = 0 then Lpar ws * wt ws i / (100 * totalW ws ^ 2) else 0
  | .ver s, .q i => if s = 1 then Lpar ws * wt ws i / (100 * totalW ws ^ 2) else 0
  | _, _ => 0

/-- Every edge introduced **before the amplification step** (pp.34–36): the comparator anchor
edges, the edges of the state paths and the verification edges. -/
def baseEdge (ws : List ℕ) (T : ℕ) (x y : Node ws.length) : ℚ :=
  anchorEdge ws x y + gadgetEdge (Delta ws) stateVal x y + verEdge ws T x y

/-- `B`, the total edge weight introduced before the final two vertices `a, b` are added (p.36). -/
def Bpar (ws : List ℕ) (T : ℕ) : ℚ := ∑ x : Node ws.length, ∑ y : Node ws.length, baseEdge ws T x y

/-- `D = 8·3^k·B/ε` (p.36). -/
def Dpar (ws : List ℕ) (T : ℕ) : ℚ := 8 * 3 ^ ws.length * Bpar ws T / epsPar ws

/-- The value `12ΔD` of the two final three-edge paths, from `r₁` to `a` and from `r₀` to `b`
(p.36); the state paths have value `0` here. -/
def ampVal (ws : List ℕ) (T : ℕ) : PathIx ws.length → ℚ
  | .ra => 12 * Delta ws * Dpar ws T
  | .rb => 12 * Delta ws * Dpar ws T
  | _ => 0

/-- The value `M` of every three-edge path: `2·3^{−j}` for a state path, `12ΔD` for a final path. -/
def pathVal (ws : List ℕ) (T : ℕ) (π : PathIx ws.length) : ℚ := stateVal π + ampVal ws T π

/-- Every edge of the construction (p.36): the pre-amplification edges, the amplification edge
`f_{ab} = D` and the edges of the two final paths of value `12ΔD`. -/
def edge (ws : List ℕ) (T : ℕ) (x y : Node ws.length) : ℚ :=
  baseEdge ws T x y + (if x = .amp 0 ∧ y = .amp 1 then Dpar ws T else 0) +
    gadgetEdge (Delta ws) (ampVal ws T) x y

/-- The vertex costs (pp.34–36): the anchors cost `0`; a comparator of offset `θ` costs
`(½ + Δθ)·1/(2Δ)`; the internal vertices of a path of value `M` cost
`c(z) = (½ − 4Δ)(1024Δ²M + 32ΔM)` and `c(y) = (½ − 4Δ)(32ΔM + M)`; `c(r₀) = L/4`,
`c(r₁) = L/4 − ΔL`; `c(a) = c(b) = (½ + 4Δ)D`. -/
def cost (ws : List ℕ) (T : ℕ) : Node ws.length → ℚ
  | .anchor _ => 0
  | .p i => (1 / 2 + Delta ws * offset (Node.p i)) * (1 / (2 * Delta ws))
  | .q i => (1 / 2 + Delta ws * offset (Node.q i)) * (1 / (2 * Delta ws))
  | .ver s => if s = 0 then Lpar ws / 4 else Lpar ws / 4 - Delta ws * Lpar ws
  | .amp _ => (1 / 2 + 4 * Delta ws) * Dpar ws T
  | .z π => (1 / 2 - 4 * Delta ws) *
      (1024 * Delta ws ^ 2 * pathVal ws T π + 32 * Delta ws * pathVal ws T π)
  | .y π => (1 / 2 - 4 * Delta ws) * (32 * Delta ws * pathVal ws T π + pathVal ws T π)

/-- The total edge weight `Σ_{u ∈ U, v ∈ V} f_uv` of the bipartite graph, by which the final
instance is normalized (pp.38–39). -/
def totalEdge (ws : List ℕ) (T : ℕ) : ℚ := ∑ x : Node ws.length, ∑ y : Node ws.length, edge ws T x y

/-- The cost scaling factor `β = 1/(1 + ε/2)` of Lemma B.9 (p.38). -/
def betaPar (ws : List ℕ) : ℚ := 1 / (1 + epsPar ws / 2)

end Construction

open Construction

/-- The **auxiliary payment instance** of Appendix B.1.1 (pp.33–36): the quadratic bipartite
reward of form (2) on the vertices `Node k`, with agent 1 owning `U` and agent 2 owning `V`, the
edge weights `f_uv` and the costs of the construction, cast from `ℚ` to `ℝ`. Its `stableUnion λ`
is the profile `S(λ)` of Lemmas B.2–B.8. -/
noncomputable def auxInst (ws : List ℕ) (T : ℕ) : BipInst (Node ws.length) where
  side := Node.side
  w u v := ((edge ws T u v + edge ws T v u : ℚ) : ℝ)
  c x := ((cost ws T x : ℚ) : ℝ)

/-- The **scaled instance** of Lemma B.9 (p.38): the auxiliary instance with every cost multiplied
by `β = 1/(1 + ε/2)` and the reward unchanged, as a two-agent contract instance. -/
noncomputable def scaledModel (ws : List ℕ) (T : ℕ) : Model (Fin 2) (Node ws.length) where
  owner := Node.side
  f := (auxInst ws T).reward
  c x := ((betaPar ws * cost ws T x : ℚ) : ℝ)

/-- The **gated, normalized instance** of the proof of Theorem 3.5 (p.39). The actions are
`Option (Node k)`: `none` is the gate action `g`, owned by agent 1 (`0`), and `some x` is vertex
`x` of the scaled instance, owned by its side. The reward is
`f̂(S) = Σ_{u ∈ U, v ∈ V} f_uv · 1[{u, v, g} ⊆ S]`, and the gate costs `2B`; the reward and every
cost (the `β`-scaled vertex costs and the gate's `2B`) are divided by `Σ_{u ∈ U, v ∈ V} f_uv`. -/
noncomputable def gatedModel (ws : List ℕ) (T : ℕ) : Model (Fin 2) (Option (Node ws.length)) where
  owner
    | none => 0
    | some x => Node.side x
  f S := (∑ u : Node ws.length, ∑ v : Node ws.length,
      if Node.side u = 0 ∧ Node.side v = 1 ∧ some u ∈ S ∧ some v ∈ S ∧ none ∈ S then
        (auxInst ws T).w u v else 0) / ((totalEdge ws T : ℚ) : ℝ)
  c
    | none => ((2 * Bpar ws T / totalEdge ws T : ℚ) : ℝ)
    | some x => ((betaPar ws * cost ws T x / totalEdge ws T : ℚ) : ℝ)

end CritContracts


