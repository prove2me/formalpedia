-- Prove2me | Definitions.Def_PacketFlowConv_ArcDynamics
-- name    : PacketFlowConv_ArcDynamics
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:25:49.990553+00:00
-- url     : https://prove2.me/theorems/9043d7b1-d94a-429b-b06e-d2503a6fe039
-- title:
--   §3.1, (3)–(4) — single-arc deterministic queueing: cumulative flows, queue $z_e$, waiting time $q_e$, exit time $T_e$
-- statement:
--   Fix one arc with transit time $\tau$ and capacity $\nu$, and commodity in- and outflow rates $f^+_j,f^-_j$. With $F^\pm_j(\theta)=\int_0^\theta f^\pm_j$, totals $f^\pm=\sum_j f^\pm_j$, $F^\pm=\sum_jF^\pm_j$ (p.8), the **queue**, **waiting time** and **exit time** are (p.9)
--   $$z(\theta)=F^+(\theta-\tau)-F^-(\theta),\qquad q(\theta)=\frac{z(\theta+\tau)}{\nu},\qquad T(\theta)=\theta+\tau+q(\theta).$$
--   The rates are **regular** if they are nonnegative, bounded, locally integrable and vanish before $0$. The rates satisfy the **arc dynamics** if for almost all $\theta\in[0,\infty)$
--
--   1. (3): $f^-(\theta)=\nu$ if $z(\theta)>0$, and $f^-(\theta)=\min\{f^+(\theta-\tau),\nu\}$ otherwise;
--   2. (4): $f^-_j(\theta)=f^-(\theta)\,f^+_j(\vartheta)/f^+(\vartheta)$ if $f^+(\vartheta)>0$ and $0$ else, where $\vartheta=\min\{\xi\le\theta: T(\xi)=\theta\}$.
--
--   The module also defines the arrival time of particle $\varphi$ in a cumulative flow $F$: $\min\{\theta\ge0:F(\theta)=\varphi\}$ for $\varphi\neq0$, and $\max\{\theta\ge0:F(\theta)=0\}$ for $\varphi=0$ (p.14).
--
--   These dynamics are shared by the flow over time and by the hypothetical flow of §5.
--
--   **Formalization Note** (3) is an if-then-else on $0<z(\theta)$, so queues stay nonnegative; (4) is required for the least element of $\{\xi\le\theta:T(\xi)=\theta\}$, which exists because the rates vanish before $0$.
-- source:
--   Sering, Vargas Koch, Ziemke, Convergence of a Packet Routing Model to Flows Over Time, arXiv:2105.13202v2, §3.1 pp.8–9, (3), (4); p.14 (arrival times k)

import Mathlib

open MeasureTheory

namespace PacketFlowConv

/-! Single-arc deterministic queueing (the arc dynamics (3)–(4) of §3.1, p.9, used for the flow
over time and for the hypothetical flow of §5, p.14). An arc has transit time `τ` and capacity
`ν`; `fin j`, `fout j` are the in- and outflow rates of commodity `j ∈ J`. -/

/-- The cumulative flow `F(θ) := ∫_0^θ f(ξ) dξ` (§3.1, p.8). -/
noncomputable def cum (f : ℝ → ℝ) (θ : ℝ) : ℝ := ∫ ξ in (0 : ℝ)..θ, f ξ

/-- The total rate `f_e(θ) := Σ_{j ∈ J} f_{j,e}(θ)` (§3.1, p.8). -/
def tot {J : Type} [Fintype J] (f : J → ℝ → ℝ) (θ : ℝ) : ℝ := ∑ j, f j θ

/-- The queue `z_e(θ) := F⁺_e(θ − τ_e) − F⁻_e(θ)` (§3.1, p.9). -/
noncomputable def queue {J : Type} [Fintype J] (τ : ℝ) (fin fout : J → ℝ → ℝ) (θ : ℝ) : ℝ :=
  cum (tot fin) (θ - τ) - cum (tot fout) θ

/-- The waiting time `q_e(θ) := z_e(θ + τ_e)/ν_e` (§3.1, p.9). -/
noncomputable def wait {J : Type} [Fintype J] (τ ν : ℝ) (fin fout : J → ℝ → ℝ) (θ : ℝ) : ℝ :=
  queue τ fin fout (θ + τ) / ν

/-- The exit time `T_e(θ) := θ + τ_e + q_e(θ)` (§3.1, p.9). -/
noncomputable def exitTime {J : Type} [Fintype J] (τ ν : ℝ) (fin fout : J → ℝ → ℝ) (θ : ℝ) : ℝ :=
  θ + τ + wait τ ν fin fout θ

/-- Regularity of a family of flow rates (§3.1, p.8): nonnegative ("the rate with which the flow
… enters and leaves", and `h⁻ : ℝ≥0 → ℝ≥0` on p.14), zero before time `0` ("we set
`f⁺_{j,e}(θ) = f⁻_{j,e}(θ) = 0` for `θ < 0`"), bounded and locally integrable. -/
structure RegularRates {J : Type} (f : J → ℝ → ℝ) : Prop where
  nonneg : ∀ j θ, 0 ≤ f j θ
  zero_neg : ∀ j θ, θ < 0 → f j θ = 0
  bdd : ∃ B : ℝ, ∀ j θ, f j θ ≤ B
  locInt : ∀ j, LocallyIntegrable (f j)

/-- The arc dynamics (3) and (4) of §3.1, p.9, for almost all `θ ∈ [0, ∞)`:
(3) `f⁻_e(θ) = ν_e` if `z_e(θ) > 0`, and `min { f⁺_e(θ − τ_e), ν_e }` otherwise;
(4) `f⁻_{j,e}(θ) = f⁻_e(θ) · f⁺_{j,e}(ϑ)/f⁺_e(ϑ)` if `f⁺_e(ϑ) > 0` and `0` else, where
`ϑ = min { ξ ≤ θ | T_e(ξ) = θ }`.

**Formalization Note.** (3) is an if-then-else on `0 < z_e(θ)`: the paper lists the cases
`z_e(θ) > 0` and `z_e(θ) = 0` of a queue volume, and this encoding keeps queues nonnegative.
(4) is required for the least element `ϑ` of `{ ξ ≤ θ | T_e(ξ) = θ }`; for rates vanishing before
`0` this set always has a least element (`T_e` is continuous with `T_e(ξ) = ξ + τ_e` for
`ξ ≤ −τ_e`). -/
def ArcDynamics {J : Type} [Fintype J] (τ ν : ℝ) (fin fout : J → ℝ → ℝ) : Prop :=
  ∀ᵐ θ ∂(volume.restrict (Set.Ici (0 : ℝ))),
    tot fout θ = (if 0 < queue τ fin fout θ then ν else min (tot fin (θ - τ)) ν) ∧
    ∀ (j : J) (ϑ : ℝ), IsLeast {ξ | ξ ≤ θ ∧ exitTime τ ν fin fout ξ = θ} ϑ →
      fout j θ = if 0 < tot fin ϑ then tot fout θ * fin j ϑ / tot fin ϑ else 0

/-- The arrival time of particle `φ` in a cumulative flow `F` (p.14):
`min { θ ∈ ℝ≥0 | F(θ) = φ }` for `φ ≠ 0`, and for particle `0` (which the paper "explicitly
include[s] into packet 1") `max { θ ∈ ℝ≥0 | F(θ) = 0 }`. -/
noncomputable def kArr (F : ℝ → ℝ) (φ : ℝ) : ℝ :=
  if φ = 0 then sSup {θ | 0 ≤ θ ∧ F θ = 0} else sInf {θ | 0 ≤ θ ∧ F θ = φ}

end PacketFlowConv


