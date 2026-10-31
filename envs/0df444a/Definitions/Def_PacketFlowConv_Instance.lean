-- Prove2me | Definitions.Def_PacketFlowConv_Instance
-- name    : PacketFlowConv_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:00.463169+00:00
-- url     : https://prove2.me/theorems/fd30db1a-b325-4d39-a91a-d0ab58624f25
-- title:
--   §2.1, §3.1, §4 — network with transit times and capacities, commodities on simple paths with supply rates, $m_j$, $\bar u_j$, $J_e$, $\kappa_e$, $\tau^*$
-- statement:
--   An **instance** consists of a directed network $G=(V,E)$ (the published general network: each arc $e$ goes from $\mathrm{tail}(e)$ to $\mathrm{head}(e)$), a transit time $\tau_e>0$ and a capacity $\nu_e>0$ on every arc, and a finite set $J$ of commodities. Commodity $j$ has an origin $o_j$, a destination $d_j$, a fixed simple $o_j$-$d_j$ path $P_j$ (a list of arcs) and a supply rate $u_j$.
--
--   The instance is **valid** when
--
--   1. $\tau_e>0$ and $\nu_e>0$ for every arc (§2.1, p.3);
--   2. every $P_j$ is a nonempty directed $o_j$-$d_j$ path whose nodes $o_j,\mathrm{head}(e_1),\dots$ are pairwise distinct (§4, p.10: "a single fixed simple path $P_j$");
--   3. $u_j\ge0$ is integrable and bounded, has bounded support, and $m_j:=\int_0^\infty u_j(\xi)\,d\xi>0$ (§3.1, p.8; §4, p.10).
--
--   Derived quantities: the particle mass $m_j$ (so $M_j=[0,m_j]$), $\bar u_j:=\sup_{\theta\ge0}u_j(\theta)$, $J_e:=\{j: e\in P_j\}$, the grid rounding $\lceil x\rceil_\alpha=\min\{\theta\in\alpha\mathbb N_0:\theta\ge x\}$, and for an arc $e=uv$ the **rate bound** (p.12)
--   $$\kappa_e:=\max\Big\{\sum_{e'\in\delta^-_u}(\nu_{e'}+1)+\sum_{j:\,o_j=u}(\bar u_j+1),\ \nu_e+1\Big\},$$
--   in which, as the paper says, $\delta^-_u$ includes one auxiliary arc of capacity $\bar u_j$ for every commodity starting at $u$; finally $\tau^*:=\min_e\tau_e/2$.
--
--   **Formalization Note** $u_j$ is a function on $\mathbb R$ that vanishes before time $0$; a node $v$ lies on $P_j$ iff it occurs in the node list `nodes j`.
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, §2.1 p.3 (Network, Discretization), §3.1 p.8, §4 p.10, κ_e and τ* p.12

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network

open MeasureTheory

namespace PacketFlowConv

open AtomicDynRouting.ResidenceTime

/-- A flow-over-time / packet-routing **instance** (Sering–Vargas Koch–Ziemke,
arXiv:2105.13202v2, §2.1 p.3 "Network", §3.1 p.8, §4 p.10): a directed network `G = (V, E)`
(the published general `Network`, arcs `e` from `tail e` to `head e`, parallel arcs allowed),
transit times `τ e`, capacities `ν e`, and for every commodity `j ∈ J` an origin `o j`, a
destination `d j`, the fixed path `P j` (a list of arcs, §4: "each commodity only uses a single
fixed simple path `P_j`") and the supply rate `u j`.

**Formalization Note.** The supply rate `u j : [0, ∞) → [0, ∞)` of the paper is a function on `ℝ`
that vanishes before time `0` (`Valid.u_neg`); all conditions on the data are collected in
`Instance.Valid`. -/
structure Instance (V E J : Type) where
  /-- the directed (multi)graph `G = (V, E)` -/
  G : Network V E
  /-- transit times `τ_e` -/
  τ : E → ℝ
  /-- capacities `ν_e` -/
  ν : E → ℝ
  /-- origins `o_j` -/
  o : J → V
  /-- destinations `d_j` -/
  d : J → V
  /-- the fixed simple `o_j`-`d_j` path `P_j` as a list of arcs -/
  P : J → List E
  /-- supply rates `u_j` -/
  u : J → ℝ → ℝ

namespace Instance

variable {V E J : Type} (I : Instance V E J)

/-- The node sequence of `P_j`: `o_j` followed by the heads of the arcs of `P_j` in order.
A node `v` "lies on `P_j`" (the set `J_v`, p.10) iff `v ∈ I.nodes j`. -/
def nodes (j : J) : List V := I.o j :: (I.P j).map I.G.head

/-- `m_j := ∫_0^∞ u_j(ξ) dξ` (§3.1 p.8, §4 p.10), the particle set being `M_j = [0, m_j]`. -/
noncomputable def mass (j : J) : ℝ := ∫ θ in Set.Ici (0 : ℝ), I.u j θ

/-- `ū_j := sup_{θ ∈ ℝ≥0} u_j(θ)` (§4, p.10). -/
noncomputable def supRate (j : J) : ℝ := sSup (I.u j '' Set.Ici 0)

/-- The arc of `P_j` leaving node `v`, if any (for `v` an inner node or the origin of a simple
path it is the unique arc `vw ∈ P_j`). -/
def outArc (j : J) (v : V) [DecidableEq V] : Option E := (I.P j).find? (fun e => I.G.tail e = v)

/-- The last arc of `P_j` (the arc `u d_j ∈ P_j`). -/
def lastArc (j : J) : Option E := (I.P j).getLast?

/-- The arc following `e` on `P_j` (`none` if `e` is the last arc of `P_j`). -/
def nextArc [DecidableEq E] (j : J) (e : E) : Option E := (I.P j)[(I.P j).idxOf e + 1]?

/-- Validity of an instance, collecting the standing assumptions of the paper:
* §2.1, p.3: every arc has transit time `τ_e > 0` and capacity `ν_e > 0`;
* §4, p.10 / Theorems 1–2: each commodity has a **simple** `o_j`-`d_j` path `P_j` (consecutive
  arcs, pairwise distinct nodes); it is nonempty (an origin equal to its destination would leave the
  arrival times of the packet model undefined);
* §3.1, p.8 and §4, p.10: `u_j ≥ 0` is integrable and bounded with bounded support, and
  `m_j = ∫_0^∞ u_j ∈ ℝ_{>0}`.

**Formalization Note.** `u_j` vanishes on `(-∞, 0)` (the paper's `u_j` is only defined on
`[0, ∞)`), so integrability on `ℝ` is integrability on `[0, ∞)`. -/
structure Valid : Prop where
  tau_pos : ∀ e, 0 < I.τ e
  nu_pos : ∀ e, 0 < I.ν e
  path_ne : ∀ j, I.P j ≠ []
  path : ∀ j, I.G.IsPathFrom (I.o j) (I.d j) (I.P j)
  simple : ∀ j, (I.nodes j).Nodup
  u_nonneg : ∀ j θ, 0 ≤ I.u j θ
  u_neg : ∀ j θ, θ < 0 → I.u j θ = 0
  u_integrable : ∀ j, Integrable (I.u j)
  u_bdd : ∀ j, ∃ B : ℝ, ∀ θ, I.u j θ ≤ B
  u_supp : ∀ j, ∃ R : ℝ, ∀ θ, R ≤ θ → I.u j θ = 0
  mass_pos : ∀ j, 0 < I.mass j

variable [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype J] [DecidableEq J]

/-- `J_e := { j ∈ J | e ∈ P_j }` (p.10). -/
def Je (e : E) : Finset J := Finset.univ.filter (fun j => e ∈ I.P j)

/-- The rate bound `κ_e` of §5, p.12, for `e = uv`:
`κ_e := max { Σ_{e' ∈ δ⁻_u} (ν_{e'} + 1), ν_e + 1 }`, where `δ⁻_u` includes one auxiliary arc of
capacity `ū_j` for every commodity `j` with origin `u` ("we … implicitly assume that `δ⁻_v`
includes these auxiliary arcs with `ν_e := ū_j`", p.12). -/
noncomputable def kappa (e : E) : ℝ :=
  max ((∑ e' ∈ Finset.univ.filter (fun e' => I.G.head e' = I.G.tail e), (I.ν e' + 1)) +
      ∑ j ∈ Finset.univ.filter (fun j => I.o j = I.G.tail e), (I.supRate j + 1))
    (I.ν e + 1)

/-- `τ* := min_{e ∈ E} τ_e / 2` (Theorem 1, p.12). -/
noncomputable def tauStar : ℝ := (⨅ e, I.τ e) / 2

end Instance

/-- The grid rounding `⌈x⌉_α := min { θ ∈ Θ_α | θ ≥ x }` with `Θ_α = αℕ₀` (§2.1, p.3); for `α > 0`
this is `α · ⌈x/α⌉₊` (also for `x < 0`, where both are `0`). -/
noncomputable def ceilGrid (α x : ℝ) : ℝ := α * ⌈x / α⌉₊

end PacketFlowConv


