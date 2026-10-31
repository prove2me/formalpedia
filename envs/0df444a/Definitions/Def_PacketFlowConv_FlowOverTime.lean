-- Prove2me | Definitions.Def_PacketFlowConv_FlowOverTime
-- name    : PacketFlowConv_FlowOverTime
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:44.712969+00:00
-- url     : https://prove2.me/theorems/9262672b-a395-44bd-9cbe-598ab8f5902e
-- title:
--   §3.1 — multi-commodity flows over time, feasibility (2)–(4), arrival times $\ell_{j,v}$ along $P_j$, last arrival time $H$
-- statement:
--   A **multi-commodity flow over time** is a family of rates $f=(f^+_{j,e},f^-_{j,e})_{j\in J,e\in E}$ (p.8). It is **feasible** for the instance (along the fixed paths) when
--
--   1. all rates are nonnegative, bounded, locally integrable and vanish for $\theta<0$;
--   2. commodity $j$ uses only arcs of $P_j$ (§4);
--   3. flow conservation (2) holds for almost all $\theta\ge0$:
--   $$\sum_{e\in\delta^+_v}f^+_{j,e}(\theta)-\sum_{e\in\delta^-_v}f^-_{j,e}(\theta)\ \begin{cases}=0& v\notin\{o_j,d_j\},\\=u_j(\theta)&v=o_j,\\\le0&v=d_j;\end{cases}$$
--   4. every arc satisfies the arc dynamics (3)–(4).
--
--   The **arrival times** (p.9): particle $\varphi\in M_j$ enters the source at $\ell_{j,o_j}(\varphi):=\min\{\theta\ge0:\int_0^\theta u_j=\varphi\}$ and reaches the head $v$ of an arc $e=uv$ of $P_j$ at $\ell_{j,v}(\varphi):=T_e(\ell_{j,u}(\varphi))$. Finally $H:=\sup_j\sup_{\varphi\in M_j}\ell_{j,d_j}(\varphi)$ is the time the last particle leaves the network (Theorem 1, p.12).
--
--   **Formalization Note** $\ell_{j,v}$ is the arrival along the fixed path $P_j$ (as in §4–§5), not the earliest arrival over all paths of §3.2.
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, §3.1 pp.8–9, (2)–(4), Arrival times p.9; H p.12

import Mathlib
import Definitions.Def_PacketFlowConv_Instance
import Definitions.Def_PacketFlowConv_ArcDynamics

open MeasureTheory

namespace PacketFlowConv

/-- A multi-commodity flow over time `f = (f⁺_{j,e}, f⁻_{j,e})_{j ∈ J, e ∈ E}` (§3.1, p.8): the
inflow rate `fin j e` and the outflow rate `fout j e` of commodity `j` on arc `e`, as functions
of time `θ ∈ ℝ`. -/
structure FlowOverTime (E J : Type) where
  /-- inflow rates `f⁺_{j,e}` -/
  fin : J → E → ℝ → ℝ
  /-- outflow rates `f⁻_{j,e}` -/
  fout : J → E → ℝ → ℝ

namespace Instance

variable {V E J : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype J] [DecidableEq J] (I : Instance V E J) (f : FlowOverTime E J)

/-- The exit time `T_e(θ) = θ + τ_e + q_e(θ)` of arc `e` under the flow `f` (§3.1, p.9). -/
noncomputable def Te (e : E) (θ : ℝ) : ℝ :=
  exitTime (I.τ e) (I.ν e) (fun j => f.fin j e) (fun j => f.fout j e) θ

/-- Net outflow `Σ_{e ∈ δ⁺_v} f⁺_{j,e}(θ) − Σ_{e ∈ δ⁻_v} f⁻_{j,e}(θ)` of commodity `j` at node `v`,
the left side of (2), p.8. -/
noncomputable def netOut (j : J) (v : V) (θ : ℝ) : ℝ :=
  (∑ e ∈ Finset.univ.filter (fun e => I.G.tail e = v), f.fin j e θ) -
    ∑ e ∈ Finset.univ.filter (fun e => I.G.head e = v), f.fout j e θ

/-- `f` is a **feasible flow over time** of the instance (§3.1, pp.8–9) routed along the fixed
paths (§4, p.10):
* the rates are nonnegative, bounded, locally integrable and vanish before `0` (p.8);
* commodity `j` uses only the arcs of its path `P_j` (§4: "each commodity only uses a single
  fixed simple path `P_j`");
* flow conservation (2) for almost all `θ ∈ [0, ∞)`: net outflow `0` at `v ∉ {o_j, d_j}`,
  `u_j(θ)` at `o_j`, `≤ 0` at `d_j`;
* the arc dynamics (3)–(4) on every arc for almost all `θ ∈ [0, ∞)` (`ArcDynamics`). -/
structure IsFeasible : Prop where
  rates_in : ∀ e, RegularRates (fun j => f.fin j e)
  rates_out : ∀ e, RegularRates (fun j => f.fout j e)
  along : ∀ j e, e ∉ I.P j → f.fin j e = 0 ∧ f.fout j e = 0
  conservation : ∀ᵐ θ ∂(volume.restrict (Set.Ici (0 : ℝ))), ∀ j v,
    (v ≠ I.o j → v ≠ I.d j → I.netOut f j v θ = 0) ∧
    (v = I.o j → I.netOut f j v θ = I.u j θ) ∧
    (v = I.d j → I.netOut f j v θ ≤ 0)
  dynamics : ∀ e, ArcDynamics (I.τ e) (I.ν e) (fun j => f.fin j e) (fun j => f.fout j e)

/-- The time particle `φ ∈ M_j` enters the source: `ℓ_{j,o_j}(φ) := min { θ ≥ 0 | ∫_0^θ u_j = φ }`
(§3.1, "Arrival times", p.9). -/
noncomputable def ell0 (j : J) (φ : ℝ) : ℝ :=
  sInf {θ | 0 ≤ θ ∧ ∫ ξ in (0 : ℝ)..θ, I.u j ξ = φ}

/-- The arrival time of particle `φ` at the `k`-th node of `P_j` (node `0` is `o_j`):
`ℓ_{j,v}(φ) := T_e(ℓ_{j,u}(φ))` for each arc `e = uv` of `P_j` (§3.1, p.9). -/
noncomputable def ellPos (j : J) (k : ℕ) (φ : ℝ) : ℝ :=
  ((I.P j).take k).foldl (fun θ e => I.Te f e θ) (I.ell0 j φ)

/-- The arrival time `ℓ_{j,v}(φ) = ℓ^{P_j}_{j,v}(φ)` of particle `φ ∈ M_j` at node `v` of the
fixed path `P_j` (§3.1 p.9, as used in §4–§5 with "a single fixed simple path `P_j`").

**Formalization Note.** `v` is located by its (unique, the path being simple) position in the
node sequence `I.nodes j`; the value is meaningful for `v ∈ I.nodes j`. -/
noncomputable def ell (j : J) (v : V) (φ : ℝ) : ℝ :=
  I.ellPos f j ((I.nodes j).idxOf v) φ

/-- `H`, "the time when the last particle left the network" (Theorem 1, p.12):
`sup_{j ∈ J} sup_{φ ∈ M_j} ℓ_{j,d_j}(φ)`. -/
noncomputable def lastTime : ℝ :=
  ⨆ j, sSup (I.ell f j (I.d j) '' Set.Icc 0 (I.mass j))

end Instance

end PacketFlowConv


