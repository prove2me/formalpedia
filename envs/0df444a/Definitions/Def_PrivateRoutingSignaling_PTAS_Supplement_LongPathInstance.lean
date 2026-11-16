-- Prove2me | Definitions.Def_PrivateRoutingSignaling_PTAS_Supplement_LongPathInstance
-- name    : PrivateRoutingSignaling_PTAS_Supplement_LongPathInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:44:25.368168+00:00
-- url     : https://prove2.me/theorems/8fc46476-f751-4cd7-b265-3b2dcd49c9d2
-- title:
--   The §5 long-path MAX-CUT construction: gadget network, $H$, $Y$, $P$, $Q_{e,0},Q_{e,1}$ and priors
-- statement:
--   Let $G=(V,E)$ be a simple graph with vertices $1,\dots,N$ and edges $e=(u,v)$, $u<v$, taken in lexicographic order.
--
--   1. The **network** (Figure 2) has two components from the source to the sink: a chain of vertex gadgets and a chain of edge gadgets. Each gadget consists of two parallel arcs, its $0$-arc and its $1$-arc; each chain is joined to the source and to the sink by one arc. For $x\in\{0,1\}^V$ the path $V_x$ uses the $x_v$-arc of each vertex gadget; for $r\in\{0,1\}^E$ the path $E_r$ uses the $r_e$-arc of each edge gadget. These are all the simple paths.
--   2. Put $r(x)_{(u,v)}=\mathbf 1[x_u\neq x_v]$. The **designated dual solution** has $Y_{V_x,E_{r(x)}}=1$ for every $x$ and all other entries zero.
--   3. In the **hard state** $H$ every $1$-arc of an edge gadget has latency $1/|E|$ and every other arc latency $0$.
--   4. In state $P$ the arc from the source into the vertex chain has constant latency $\frac12$, the arc from the source into the edge chain has latency $x$, and every other arc latency $0$.
--   5. For $e=(u,v)$, state $Q_{e,0}$ gives latency $\frac12$ to the $1$-arc of $u$ and the $0$-arc of $v$, latency $1$ to the $0$-arc of the gadget of $e$, and $0$ elsewhere; $Q_{e,1}$ does the same with the $0$-arc of $u$ and the $1$-arc of $v$.
--   6. For a gap $\delta$, $T=2^{-7}$ and $\lambda_H=\frac{T\delta}2$, the priors are $\lambda_H$ on $H$, $\frac14$ on $P$, $\frac1{4|E|}$ on each $Q_{e,b}$, and $\frac14-\lambda_H$ on a dummy state with zero latency.
--
--   The auxiliary dual objective is
--
--   $$
--   D^{\mathrm{aux}}(y)=\frac14D^P(y)+\frac1{4|E|}\sum_{e\in E}\bigl(D^{Q_{e,0}}(y)+D^{Q_{e,1}}(y)\bigr).
--   $$
--
--   This is the instance of Lemma 5.6, used behind Theorem 5.7.
--
--   **Formalization Note** Nodes are the source $0$, the sink $1$, the vertex-chain nodes $2,\dots,N+2$ and the edge-chain nodes $N+3,\dots,N+|E|+3$. Arc $0$ enters the vertex chain, arc $1$ the edge chain, arcs $2$ and $3$ leave them, arc $4+2k+b$ is the $b$-arc of vertex $k$ and arc $4+2N+2j+b$ the $b$-arc of edge $j$. States are $0=H$, $1=P$, $2+2j+b=Q_{e_j,b}$ and $2|E|+2$ the dummy. $Y$ has exponentially many entries and is an object of the analysis only, never machine input.
-- source:
--   Yu Cheng, Tianle Jiang, The Complexity of Private Signaling in Nonatomic Routing Games, STOC 2027 submission #439 (October 2026), §5.1 pp. 25–26 and Figure 2 (network, V_x, E_r, H, r(x), Y), §5.2 pp. 27–28 (P, Q_{e,0}, Q_{e,1}), §5.3 pp. 29–30 (priors, D^aux, T, λ_H, dummy state); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/439.pdf; SHA-256 766b4afa05d6c7c4c106ed83a73221ca4d951eeca5cce863930177ed26fd4e61

import Mathlib
import Definitions.Def_PrivateRoutingSignaling_PTAS_Supplement_Dual

set_option autoImplicit false
open scoped BigOperators

namespace PrivateRoutingSignaling.PTAS.Supplement

open PrivateRoutingSignaling.PTAS

namespace LongPath

variable (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]

/-- The edges `e = (u,v)`, `u < v`, of `G`, in lexicographic order (the "arbitrary order" of the
edge gadgets, §5.1, p. 25). -/
def edges : List (Fin N × Fin N) :=
  (List.finRange N).flatMap fun u =>
    (List.finRange N).filterMap fun v => if u < v ∧ G.Adj u v then some (u, v) else none

/-- `|E|`. -/
def m : ℕ := (edges N G).length

/-- Number of nodes: source `0`, sink `1`, vertex-chain nodes `2+k` (`k ≤ N`), edge-chain nodes
`3+N+j` (`j ≤ |E|`). -/
def nodes : ℕ := N + m N G + 4

/-- Number of arcs: the four terminal arcs and two parallel arcs per vertex and per edge gadget. -/
def arcs : ℕ := 2 * N + 2 * m N G + 4

def bit (b : Bool) : ℕ := if b then 1 else 0

/-- Arc numbering (Figure 2, p. 25): `0` source→first vertex gadget, `1` source→first edge
gadget, `2` last vertex gadget→sink, `3` last edge gadget→sink, `4+2k+b` the `b`-arc of the
gadget of vertex `k`, `4+2N+2j+b` the `b`-arc of the gadget of edge `j`. -/
def tailN (a : ℕ) : ℕ :=
  if a = 0 then 0 else if a = 1 then 0 else if a = 2 then 2 + N
  else if a = 3 then 3 + N + m N G
  else if a < 4 + 2 * N then 2 + (a - 4) / 2
  else 3 + N + (a - 4 - 2 * N) / 2

def headN (a : ℕ) : ℕ :=
  if a = 0 then 2 else if a = 1 then 3 + N else if a = 2 then 1
  else if a = 3 then 1
  else if a < 4 + 2 * N then 3 + (a - 4) / 2
  else 4 + N + (a - 4 - 2 * N) / 2

def node (k : ℕ) : Fin (nodes N G) := ⟨k % nodes N G, Nat.mod_lt _ (by unfold nodes; omega)⟩
def arc (k : ℕ) : Fin (arcs N G) := ⟨k % arcs N G, Nat.mod_lt _ (by unfold arcs; omega)⟩

/-- The network of §5.1 (Figure 2): a chain of vertex gadgets and a chain of edge gadgets, each
joined to the source and to the sink. -/
def network : RoutingNetwork :=
  ⟨nodes N G, arcs N G, ⟨fun a => node N G (tailN N G a.val), fun a => node N G (headN N a.val)⟩,
    node N G 0, node N G 1, nodes N G⟩

/-- The path `V_x`, `x ∈ {0,1}^V`, through the `x_v`-arcs of the vertex gadgets. -/
def vPath (x : Fin N → Bool) : List (Fin (arcs N G)) :=
  [arc N G 0] ++ List.ofFn (fun k : Fin N => arc N G (4 + 2 * k.val + bit (x k))) ++ [arc N G 2]

/-- The path `E_r`, `r ∈ {0,1}^E`, through the `r_e`-arcs of the edge gadgets. -/
def ePath (r : Fin (m N G) → Bool) : List (Fin (arcs N G)) :=
  [arc N G 1] ++ List.ofFn (fun j : Fin (m N G) => arc N G (4 + 2 * N + 2 * j.val + bit (r j))) ++
    [arc N G 3]

/-- `r(x)_{(u,v)} = 1[x_u ≠ x_v]`, the cut induced by `x`. -/
def cutVec (x : Fin N → Bool) (j : Fin (m N G)) : Bool :=
  decide (x ((edges N G).get j).1 ≠ x ((edges N G).get j).2)

/-- The designated dual solution (p. 26): `Y_{V_x, E_{r(x)}} = 1` for every `x`, all other
entries zero. It has exponentially many entries and is an analysis object only. -/
noncomputable def Y : DualMatrix (network N G) := by
  classical
  exact fun p q =>
    if ∃ x : Fin N → Bool, pathArcs (network N G) p = vPath N G x ∧
        pathArcs (network N G) q = ePath N G (cutVec N G x) then 1 else 0

/-- Hard state `H` (pp. 25–26): every 1-arc of an edge gadget has latency `1/|E|`, every other
arc latency zero. -/
noncomputable def hardLatency (a : ℕ) (_x : ℝ) : ℝ :=
  if 4 + 2 * N ≤ a ∧ a < 4 + 2 * N + 2 * m N G ∧ (a - 4 - 2 * N) % 2 = 1 then 1 / (m N G : ℝ)
  else 0

/-- State `P` (p. 27): latency `1/2` on the source arc of the vertex chain, `x` on the source arc
of the edge chain, zero elsewhere. -/
noncomputable def pLatency (a : ℕ) (x : ℝ) : ℝ :=
  if a = 0 then 1 / 2 else if a = 1 then x else 0

/-- States `Q_{e,0}` (`b = false`) and `Q_{e,1}` (`b = true`) for the edge `e = (u,v)` with index
`j` (p. 28): `Q_{e,0}` puts `1/2` on the 1-arc of `u` and the 0-arc of `v`, `Q_{e,1}` on the
0-arc of `u` and the 1-arc of `v`; both put `1` on the 0-arc of the gadget of `e`; zero elsewhere. -/
noncomputable def qLatency (j : ℕ) (b : Bool) (a : ℕ) (_x : ℝ) : ℝ :=
  if h : j < m N G then
    let u := ((edges N G).get ⟨j, h⟩).1.val
    let v := ((edges N G).get ⟨j, h⟩).2.val
    if a = 4 + 2 * u + bit (!b) ∨ a = 4 + 2 * v + bit b then 1 / 2
    else if a = 4 + 2 * N + 2 * j then 1 else 0
  else 0

/-- `T = 1/2⁷` (p. 30). -/
noncomputable def T : ℝ := 1 / 2 ^ 7

/-- `λ_H = Tδ/2` (p. 30). -/
noncomputable def priorH (δ : ℝ) : ℝ := T * δ / 2

/-- States `0 = H`, `1 = P`, `2+2j+b = Q_{e_j,b}` (`j < |E|`), and `2|E|+2` = the dummy. -/
noncomputable def latency (θ : Fin (2 * m N G + 3)) (a : Fin (arcs N G)) (x : ℝ) : ℝ :=
  if θ.val = 0 then hardLatency N G a.val x
  else if θ.val = 1 then pLatency a.val x
  else if θ.val < 2 * m N G + 2 then
    qLatency N G ((θ.val - 2) / 2) (decide ((θ.val - 2) % 2 = 1)) a.val x
  else 0

/-- Priors (p. 30): `λ_H`, `λ_P = 1/4`, `λ_{Q_{e,b}} = 1/(4|E|)`, dummy `1/4 − λ_H`. -/
noncomputable def prior (δ : ℝ) (θ : Fin (2 * m N G + 3)) : ℝ :=
  if θ.val = 0 then priorH δ
  else if θ.val = 1 then 1 / 4
  else if θ.val < 2 * m N G + 2 then 1 / (4 * (m N G : ℝ))
  else 1 / 4 - priorH δ

/-- The private signaling instance of §5.3 (p. 30), for a MAX-CUT gap `δ`. -/
noncomputable def inst (δ : ℝ) : Instance where
  network := network N G
  states := 2 * m N G + 3
  prior := prior N G δ
  latency := latency N G

def hState : Fin (2 * m N G + 3) := ⟨0, by omega⟩
def pState : Fin (2 * m N G + 3) := ⟨1, by omega⟩
def qState (j : Fin (m N G)) (b : Bool) : Fin (2 * m N G + 3) :=
  ⟨2 + 2 * j.val + bit b, by unfold bit; split <;> omega⟩

/-- `D^aux(y) = D^P(y)/4 + (1/(4|E|)) ∑_e (D^{Q_{e,0}}(y) + D^{Q_{e,1}}(y))` (p. 29). -/
noncomputable def daux (δ : ℝ) (y : DualMatrix (network N G)) : ℝ :=
  dualValue (inst N G δ) (pState N G) y / 4 +
    ∑ j : Fin (m N G), (dualValue (inst N G δ) (qState N G j false) y +
      dualValue (inst N G δ) (qState N G j true) y) / (4 * (m N G : ℝ))

end LongPath

end PrivateRoutingSignaling.PTAS.Supplement


