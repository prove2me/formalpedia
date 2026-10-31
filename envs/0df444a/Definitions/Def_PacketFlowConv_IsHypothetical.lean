-- Prove2me | Definitions.Def_PacketFlowConv_IsHypothetical
-- name    : PacketFlowConv_IsHypothetical
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:27:26.753684+00:00
-- url     : https://prove2.me/theorems/248e3aac-6ac1-485b-b025-5de32795f4d3
-- title:
--   §5, p.14 and p.16 — the hypothetical flow on an arc, $k_{j,u}$, $k_{j,v}$, $q^H_e$, and the aggregated $k_u$, $k_v$, $\ell^D_v$
-- statement:
--   Fix an arc $e=uv$ and a packet routing. A **hypothetical flow** on $e$ (p.14) has the packet inflow rates $h^+_{j,e}:=g^+_{j,e}$ and outflow rates $h^-_{j,e}\ge0$ (bounded, locally integrable, zero before $0$) obeying the arc dynamics (3) and (4) on $e$. With $H^\pm_{j,e}=\int_0^\cdot h^\pm_{j,e}$ (so $H^+_{j,e}=G^+_{j,e}$) the hypothetical arrival times are
--   $$k_{j,u}(\varphi)=\min\{\theta\ge0:H^+_{j,e}(\theta)=\varphi\},\qquad k_{j,v}(\varphi)=\min\{\theta\ge0:H^-_{j,e}(\theta)=\varphi\}$$
--   for $\varphi\neq0$, with maxima of the zero sets for $\varphi=0$; $q^H_e$ is the waiting time of the hypothetical flow. For the single-commodity view of Lemma 4 (p.16): $k_u(\varphi)=\min\{\theta\ge0:H^+_e(\theta)=\varphi\}$, $k_v(\varphi)=\min\{\theta\ge0:H^-_e(\theta)=\varphi\}$ and $\ell^D_v(i)=\min\{\theta\ge0:G^-_e(\theta)=i\beta\}$.
--
--   These objects connect the packet model to the fluid dynamics on one arc in Lemmas 3 and 4.
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, §5 p.14 (Hypothetical flow over time), p.16 (proof of Lemma 4)

import Mathlib
import Definitions.Def_PacketFlowConv_Instance
import Definitions.Def_PacketFlowConv_ArcDynamics
import Definitions.Def_PacketFlowConv_Discretization

open MeasureTheory

namespace PacketFlowConv

namespace Instance

variable {V E J : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype J] [DecidableEq J] (I : Instance V E J) (D : Discretization V E J)

/-- The hypothetical flow over time on a fixed arc `e = uv` (§5, p.14): the inflow rates are the
packet inflow rates, `h⁺_{j,e} := g⁺_{j,e}`, and the outflow rates `h⁻_{j,e} = hout j` are
nonnegative, bounded, locally integrable, vanish before `0` and satisfy (3) and (4) on `e`
("`h⁻_{j,e} : ℝ≥0 → ℝ≥0` according to (3) and (4)"). -/
def IsHypothetical (e : E) (hout : J → ℝ → ℝ) : Prop :=
  RegularRates hout ∧ ArcDynamics (I.τ e) (I.ν e) (fun j => I.gPlus D j e) hout

/-- The hypothetical arrival time at `u` (p.14): `k_{j,u}(φ) := min { θ ∈ ℝ≥0 | H⁺_{j,e}(θ) = φ }`
for `φ ≠ 0` and `k_{j,u}(0) := max { θ ∈ ℝ≥0 | H⁺_{j,e}(θ) = 0 }`, where
`H⁺_{j,e} = ∫_0^· h⁺_{j,e} = G⁺_{j,e}`. -/
noncomputable def kU (j : J) (e : E) (φ : ℝ) : ℝ := kArr (I.Gplus D j e) φ

/-- The waiting time `q^H_e(θ) = z^H_e(θ + τ_e)/ν_e` of the hypothetical flow on `e` (p.14). -/
noncomputable def qH (e : E) (hout : J → ℝ → ℝ) (θ : ℝ) : ℝ :=
  wait (I.τ e) (I.ν e) (fun j => I.gPlus D j e) hout θ

/-- The aggregated single-commodity arrival time at `u` (proof of Lemma 4, p.16):
`k_u(φ) := min { θ ∈ ℝ≥0 | H⁺_e(θ) = φ }`. -/
noncomputable def kUagg (e : E) (φ : ℝ) : ℝ := sInf {θ | 0 ≤ θ ∧ I.GplusTot D e θ = φ}

/-- The aggregated refined arrival time at `v` (p.16): `ℓ^D_v(i) := min { θ ∈ ℝ≥0 | G⁻_e(θ) = iβ }`. -/
noncomputable def ellDVagg (e : E) (i : ℕ) : ℝ :=
  sInf {θ | 0 ≤ θ ∧ I.GminusTot D e θ = (i : ℝ) * D.β}

end Instance

/-- The hypothetical arrival time at `v` (p.14): `k_{j,v}(φ) := min { θ ∈ ℝ≥0 | H⁻_{j,e}(θ) = φ }`
for `φ ≠ 0` and `max { θ ∈ ℝ≥0 | H⁻_{j,e}(θ) = 0 }` for `φ = 0`, with `H⁻_{j,e} = ∫_0^· h⁻_{j,e}`. -/
noncomputable def kV {J : Type} (hout : J → ℝ → ℝ) (j : J) (φ : ℝ) : ℝ := kArr (cum (hout j)) φ

/-- The aggregated hypothetical arrival time at `v` (p.16):
`k_v(φ) := min { θ ∈ ℝ≥0 | H⁻_e(θ) = φ }`, `H⁻_e = Σ_{j ∈ J} H⁻_{j,e}`. -/
noncomputable def kVagg {J : Type} [Fintype J] (hout : J → ℝ → ℝ) (φ : ℝ) : ℝ :=
  sInf {θ | 0 ≤ θ ∧ ∑ j, cum (hout j) θ = φ}

end PacketFlowConv


