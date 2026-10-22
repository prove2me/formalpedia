-- Prove2me | Definitions.Def_NashFlowLT_SteadyState_Model
-- name    : NashFlowLT_SteadyState_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:25:44.923402+00:00
-- url     : https://prove2.me/theorems/857617ca-9da7-4c62-8a08-7bf152b4a63a
-- title:
--   §2.1–§2.3, pp. 5–7 — fluid queuing network: queues (1)–(2), flows over time (3), exit times (4), labels (5)–(6), dynamic equilibrium, NTFR (10)–(13), (P), (D)
-- statement:
--   This file fixes the model of Cominetti, Correa and Olver: a fluid queuing network, its flows over time, earliest-arrival labels, dynamic equilibria, steady states, the potential $\Phi$, normalized thin flows with resetting, and the two linear programs (P) and (D).
--
--   **Network.** A finite directed multigraph with node set $V$ and arc set $E$; every arc $e$ has a tail and a head, so parallel arcs are allowed. Each arc $e=vw$ is a fluid queue with capacity $\nu_e$ followed by a link with delay $\tau_e$. A constant inflow rate $u_0$ enters at the source $s$ and travels to the terminal $t$. The **standing assumptions** are $\nu_e>0$, $\tau_e\ge 0$, $u_0>0$, $s\neq t$, and every node is reachable from $s$ by a path. The capacity of the cut leaving a node set $S$ is $\sum_{e\in\delta^+(S)}\nu_e$.
--
--   **Flow over time.** Inflow rates $f^+_e:[0,\infty)\to[0,\infty)$, measurable and integrable on every bounded interval, and queue lengths $z_e$ with $z_e(0)=0$, $z_e\ge 0$, evolving by the queue dynamics (1)
--   $$\dot z_e(\theta)=\begin{cases} f^+_e(\theta)-\nu_e & \text{if } z_e(\theta)>0,\\ [f^+_e(\theta)-\nu_e]_+ & \text{if } z_e(\theta)=0,\end{cases}$$
--   imposed in integrated form $z_e(\theta)=\int_0^\theta \dot z_e$. The outflow rate (2) is $f^-_e(\theta+\tau_e)=\nu_e$ if $z_e(\theta)>0$ and $\min\{f^+_e(\theta),\nu_e\}$ if $z_e(\theta)=0$, and $f^-_e=0$ before time $\tau_e$. Flow conservation (3) holds at every node $v\neq t$ for almost every $\theta\ge 0$:
--   $$\sum_{e\in\delta^+(v)} f^+_e(\theta)-\sum_{e\in\delta^-(v)} f^-_e(\theta)=\begin{cases}u_0 & v=s,\\ 0 & v\neq s,t.\end{cases}$$
--
--   **Labels.** The exit time of arc $e$ is $T_e(\theta)=\theta+z_e(\theta)/\nu_e+\tau_e$ (4); along a path $p=e_1\cdots e_k$, $T_p=T_{e_k}\circ\cdots\circ T_{e_1}$ (5); the earliest arrival label is $\ell_v(\theta)=\min_{p\in\mathcal P_v}T_p(\theta)$ (6), the minimum over all simple $sv$-paths. An arc $e=vw$ is **active** at $\theta$ ($e\in E'_\theta$) if $\ell_w(\theta)=T_e(\ell_v(\theta))$, and has a **queue** at $\theta$ ($e\in E^*_\theta$) if $z_e(\ell_v(\theta))>0$.
--
--   **Dynamic equilibrium.** With $\Theta_e=\{\theta\ge 0: e\in E'_\theta\}$ and $\Xi_e=\ell_v(\Theta_e)$, a flow over time is a dynamic equilibrium if for every arc $e$ and almost every $\xi\ge 0$, $f^+_e(\xi)>0\Rightarrow\xi\in\Xi_e$. It **attains a steady state** if there is $\theta_0\ge 0$ with $z_e(\theta)=z_e(\theta_0)$ for all arcs $e$ and all $\theta\ge\theta_0$.
--
--   **Derived quantities.** The static flow is $x_e(\theta)=F^+_e(\ell_v(\theta))=\int_0^{\ell_v(\theta)}f^+_e$, and the potential is
--   $$\Phi(\theta)=u_0\bigl(\ell_t(\theta)-\ell_s(\theta)\bigr)-\sum_{e\in E} z_e(\ell_v(\theta)),$$
--   with $v$ the tail of $e$.
--
--   **Thin flows.** For arc sets $E^*\subseteq E'$, a pair $(\ell',x')$ with $\ell',x'\ge 0$ is a normalized thin flow with resetting (NTFR) if $x'$ is a static $st$-flow of value $u_0$ (10), $\ell'_s=1$ and $\ell'_w=\min_{e=vw\in E'}\rho_e(\ell'_v,x'_e)$ for $w\neq s$ (11), where $\rho_e(\ell'_v,x'_e)=x'_e/\nu_e$ if $e\in E^*$ and $\max\{\ell'_v,x'_e/\nu_e\}$ otherwise (12), and, as in (13), $x'_e>0\Rightarrow \ell'_w=\rho_e(\ell'_v,x'_e)$ for $e\in E'$ and $x'_e=0$ for $e\notin E'$.
--
--   **Linear programs.** A point $y'$ is feasible for (P) if it is an $st$-flow of value $u_0$ with $0\le y'_e\le\nu_e$; a pair $(d,q)$ is feasible for (D) if $d_s=0$, $d_w\le d_v+\tau_e+q_e$ for every arc $e=vw$, and $q_e\ge 0$.
--
--   These objects are the common vocabulary of every statement of the mission.
--
--   **Formalization Note** Three conditions are added to the page: $s\neq t$ (implicit in "a single source–sink pair"), reachability of every node from $s$ (so the minimum in (6) is over a nonempty set), and local integrability of the inflows (needed for $F^+_e$, p. 6). The queue $z_e$ is part of the data and is pinned down by the integrated form of (1) with $z_e(0)=0$. Paths are lists of arcs visiting pairwise distinct nodes, so the set in (6) is finite and the infimum is a minimum. The second case of (10) is encoded with $v=t$; the page prints "$v=s$", a slip (compare (9)). The minimum in (11) is imposed for $w\neq s$ only, as the page writes $\ell'_s=1$ separately. All functions of time are real functions on $\mathbb R$; only $\theta\ge 0$ matters.
-- source:
--   Cominetti, Correa & Olver, Long term behavior of dynamic equilibria in fluid queuing networks, arXiv:2112.10412v1, pp. 2, 5–7, 9–11, §1, §2.1–§2.3 (eqs. (1)–(6), (9)–(13)), §3, Theorem 1 ((P), (D)), §4 (Φ)

import Mathlib

namespace NashFlowLT.SteadyState

open MeasureTheory Set Finset

/-- A fluid queuing network (§1 p. 2, §2.1 p. 5): a finite directed multigraph with arc set `E`
(arcs carry their own `tail` and `head`, so parallel arcs are allowed), capacities `nu e = ν_e`,
free-flow delays `tau e = τ_e`, a constant inflow rate `u0` entering at the source `s`, and the
terminal `t`. -/
structure Network (V E : Type) where
  tail : E → V
  head : E → V
  nu : E → ℝ
  tau : E → ℝ
  u0 : ℝ
  s : V
  t : V

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- `IsWalk N v w p`: the list of arcs `p = e₁ e₂ ⋯ e_k` is a directed walk from `v` to `w`
(`tail e₁ = v`, `head eᵢ = tail eᵢ₊₁`, `head e_k = w`); the empty list is the walk from `v` to `v`. -/
def IsWalk (N : Network V E) : V → V → List E → Prop
  | v, w, [] => v = w
  | v, w, e :: p => N.tail e = v ∧ IsWalk N (N.head e) w p

/-- The nodes visited by the arc list `p` started at `v`: `v, head e₁, …, head e_k`. -/
def walkNodes (N : Network V E) (v : V) : List E → List V
  | [] => [v]
  | e :: p => v :: walkNodes N (N.head e) p

/-- A (simple) `vw`-path: a walk from `v` to `w` visiting pairwise distinct nodes. -/
def IsPath (N : Network V E) (v w : V) (p : List E) : Prop :=
  IsWalk N v w p ∧ (walkNodes N v p).Nodup

/-- Standing assumptions of the paper: `ν_e > 0`, `τ_e ≥ 0` (p. 2), `u0 > 0` (p. 2), together with
the two added conditions `s ≠ t` and "every node is reachable from `s` by a path" (needed for the
minimum over `P_v` in (6) to be over a nonempty set). -/
def Network.Standing (N : Network V E) : Prop :=
  (∀ e, 0 < N.nu e) ∧ (∀ e, 0 ≤ N.tau e) ∧ 0 < N.u0 ∧ N.s ≠ N.t ∧
    ∀ v, ∃ p, IsPath N N.s v p

/-- Capacity `Σ_{e ∈ δ⁺(S)} ν_e` of the `st`-cut formed by the arcs leaving the node set `S`. -/
def cutCapacity (N : Network V E) (S : Finset V) : ℝ :=
  ∑ e ∈ univ.filter (fun e => N.tail e ∈ S ∧ N.head e ∉ S), N.nu e

/-- The data of a flow over time: the arc inflow rates `fin e θ = f⁺_e(θ)` and the queue lengths
`z e θ = z_e(θ)`. Only times `θ ≥ 0` matter. -/
structure FlowOverTime (V E : Type) where
  fin : E → ℝ → ℝ
  z : E → ℝ → ℝ

/-- Right-hand side of the queue dynamics (1): `f⁺_e − ν_e` if `z_e > 0`, `[f⁺_e − ν_e]₊` if
`z_e = 0`. -/
noncomputable def queueRate (N : Network V E) (F : FlowOverTime V E) (e : E) (x : ℝ) : ℝ :=
  if 0 < F.z e x then F.fin e x - N.nu e else max (F.fin e x - N.nu e) 0

/-- Arc outflow rate `f⁻_e(θ)` from (2): `f⁻_e(θ + τ_e) = ν_e` if `z_e(θ) > 0` and
`min{f⁺_e(θ), ν_e}` if `z_e(θ) = 0`; no flow leaves the arc before time `τ_e`. -/
noncomputable def outRate (N : Network V E) (F : FlowOverTime V E) (e : E) (θ : ℝ) : ℝ :=
  if θ < N.tau e then 0
  else if 0 < F.z e (θ - N.tau e) then N.nu e else min (F.fin e (θ - N.tau e)) (N.nu e)

/-- A flow over time (§2.1, p. 5): measurable, nonnegative, locally integrable inflows; queues
starting empty and evolving by (1) (in integrated form); flow conservation (3) at every node
`v ≠ t` for almost every `θ ≥ 0`, with the external inflow `u0` at `s`. -/
def IsFlowOverTime (N : Network V E) (F : FlowOverTime V E) : Prop :=
  (∀ e, Measurable (F.fin e)) ∧ (∀ e x, 0 ≤ x → 0 ≤ F.fin e x) ∧
    (∀ e (T : ℝ), IntegrableOn (F.fin e) (Icc 0 T)) ∧
    (∀ e θ, 0 ≤ θ → 0 ≤ F.z e θ ∧ F.z e θ = ∫ x in (0 : ℝ)..θ, queueRate N F e x) ∧
    ∀ v, v ≠ N.t → ∀ᵐ θ ∂(volume.restrict (Ici (0 : ℝ))),
      (∑ e ∈ univ.filter (fun e => N.tail e = v), F.fin e θ) -
          (∑ e ∈ univ.filter (fun e => N.head e = v), outRate N F e θ)
        = if v = N.s then N.u0 else 0

/-- Exit time (4): `T_e(θ) = θ + z_e(θ)/ν_e + τ_e`. -/
noncomputable def exitTime (N : Network V E) (F : FlowOverTime V E) (e : E) (θ : ℝ) : ℝ :=
  θ + F.z e θ / N.nu e + N.tau e

/-- Path exit time (5): `T_p = T_{e_k} ∘ ⋯ ∘ T_{e_1}` for `p = e₁ ⋯ e_k`. -/
noncomputable def pathTime (N : Network V E) (F : FlowOverTime V E) : List E → ℝ → ℝ
  | [], θ => θ
  | e :: p, θ => pathTime N F p (exitTime N F e θ)

/-- Earliest arrival labels (6): `ℓ_v(θ) = min_{p ∈ P_v} T_p(θ)` over all `sv`-paths. -/
noncomputable def ell (N : Network V E) (F : FlowOverTime V E) (v : V) (θ : ℝ) : ℝ :=
  sInf {r | ∃ p, IsPath N N.s v p ∧ r = pathTime N F p θ}

/-- The arc `e = vw` is active at time `θ` (`e ∈ E′_θ`): `ℓ_w(θ) = T_e(ℓ_v(θ))` (p. 6). -/
def IsActive (N : Network V E) (F : FlowOverTime V E) (e : E) (θ : ℝ) : Prop :=
  ell N F (N.head e) θ = exitTime N F e (ell N F (N.tail e) θ)

/-- The arc `e = vw` has a queue at time `θ` (`e ∈ E*_θ`): `z_e(ℓ_v(θ)) > 0` (p. 7). -/
def HasQueue (N : Network V E) (F : FlowOverTime V E) (e : E) (θ : ℝ) : Prop :=
  0 < F.z e (ell N F (N.tail e) θ)

/-- Dynamic equilibrium (p. 6): a flow over time such that for every arc `e = vw` and almost every
`ξ ≥ 0`, `f⁺_e(ξ) > 0 ⇒ ξ ∈ Ξ_e = ℓ_v(Θ_e)`, where `Θ_e` is the set of entrance times `θ ≥ 0` at
which `e` is active. -/
def IsDynamicEquilibrium (N : Network V E) (F : FlowOverTime V E) : Prop :=
  IsFlowOverTime N F ∧ ∀ e, ∀ᵐ ξ ∂(volume.restrict (Ici (0 : ℝ))),
    0 < F.fin e ξ → ξ ∈ ell N F (N.tail e) '' {θ | 0 ≤ θ ∧ IsActive N F e θ}

/-- Steady state (p. 9): from some time on, all queues are frozen to a constant. -/
def AttainsSteadyState (N : Network V E) (F : FlowOverTime V E) : Prop :=
  ∃ θ₀ : ℝ, 0 ≤ θ₀ ∧ ∀ e θ, θ₀ ≤ θ → F.z e θ = F.z e θ₀

/-- Static flow (9): `x_e(θ) = F⁺_e(ℓ_v(θ)) = ∫_0^{ℓ_v(θ)} f⁺_e`, with `v` the tail of `e`. -/
noncomputable def staticFlow (N : Network V E) (F : FlowOverTime V E) (e : E) (θ : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..(ell N F (N.tail e) θ), F.fin e x

/-- The potential of §4 (p. 11): `Φ(θ) = u0 (ℓ_t(θ) − ℓ_s(θ)) − Σ_e z_e(ℓ_v(θ))`. -/
noncomputable def Phi (N : Network V E) (F : FlowOverTime V E) (θ : ℝ) : ℝ :=
  N.u0 * (ell N F N.t θ - ell N F N.s θ) - ∑ e, F.z e (ell N F (N.tail e) θ)

/-- `y` is a static `st`-flow of value `val`: net outflow `val` at `s`, `-val` at `t`, `0` elsewhere
(the conservation system of (10)). -/
def IsStFlow (N : Network V E) (y : E → ℝ) (val : ℝ) : Prop :=
  ∀ v, (∑ e ∈ univ.filter (fun e => N.tail e = v), y e) -
      (∑ e ∈ univ.filter (fun e => N.head e = v), y e)
    = if v = N.s then val else if v = N.t then -val else 0

open Classical in
/-- (12): `ρ_e(ℓ′_v, x′_e) = x′_e/ν_e` if `e ∈ E*`, `max{ℓ′_v, x′_e/ν_e}` otherwise. -/
noncomputable def rho (N : Network V E) (Estar : Set E) (e : E) (lv xe : ℝ) : ℝ :=
  if e ∈ Estar then xe / N.nu e else max lv (xe / N.nu e)

/-- Normalized thin flow with resetting (10)–(13) for active arcs `Eact = E′` and queue arcs
`Estar = E*`: `E* ⊆ E′`, `ℓ′, x′ ≥ 0`, `x′` an `st`-flow of value `u0` (10), `ℓ′_s = 1` and
`ℓ′_w = min_{e = vw ∈ E′} ρ_e(ℓ′_v, x′_e)` for `w ≠ s` (11), and (13). -/
def IsNTFR (N : Network V E) (Eact Estar : Set E) (l' : V → ℝ) (x' : E → ℝ) : Prop :=
  Estar ⊆ Eact ∧ (∀ v, 0 ≤ l' v) ∧ (∀ e, 0 ≤ x' e) ∧ IsStFlow N x' N.u0 ∧ l' N.s = 1 ∧
    (∀ w, w ≠ N.s → IsLeast
      {r | ∃ e ∈ Eact, N.head e = w ∧ r = rho N Estar e (l' (N.tail e)) (x' e)} (l' w)) ∧
    (∀ e ∈ Eact, 0 < x' e → l' (N.head e) = rho N Estar e (l' (N.tail e)) (x' e)) ∧
    (∀ e ∉ Eact, x' e = 0)

/-- Feasibility for the min-cost flow program (P) (p. 10): `y′ ∈ F₀` (an `st`-flow of value `u0`)
and `0 ≤ y′_e ≤ ν_e`. -/
def IsPrimalFeasible (N : Network V E) (y : E → ℝ) : Prop :=
  IsStFlow N y N.u0 ∧ ∀ e, 0 ≤ y e ∧ y e ≤ N.nu e

/-- Feasibility for the dual program (D) (p. 10): `d_s = 0`, `d_w ≤ d_v + τ_e + q_e` for every arc
`e = vw`, `q_e ≥ 0`. -/
def IsDualFeasible (N : Network V E) (d : V → ℝ) (q : E → ℝ) : Prop :=
  d N.s = 0 ∧ (∀ e, d (N.head e) ≤ d (N.tail e) + N.tau e + q e) ∧ ∀ e, 0 ≤ q e

end NashFlowLT.SteadyState


