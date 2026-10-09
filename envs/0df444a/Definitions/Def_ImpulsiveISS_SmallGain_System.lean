-- Prove2me | Definitions.Def_ImpulsiveISS_SmallGain_System
-- name    : ImpulsiveISS_SmallGain_System
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:54:40.015042+00:00
-- url     : https://prove2.me/theorems/7d10e328-cf36-4fe6-83a6-218c3f9f9723
-- title:
--   §2–3 — impulsive system $(\phi_c, g)$, piecewise right-continuous inputs, Lie derivative (3.3), ISS-Lyapunov function (Definition 4)
-- statement:
--   Let $X$ and $U$ be real Banach spaces (states and input values), and write $\mathbb R_+=[0,\infty)$.
--
--   **Inputs** (p. 3). An input $u\in U_c=PC(\mathbb R_+,U)$ is a function $u:\mathbb R\to U$ whose values on $[0,\infty)$ matter only, which on $[0,\infty)$ is right-continuous, has a left limit $u^-(t)$ at every $t>0$, is continuous at all but finitely many points of every interval $(0,T]$, and is bounded, so that $\|u\|_{U_c}=\sup_{t\ge0}\|u(t)\|_U<\infty$.
--
--   **Impulsive system** (2.1), pp. 3–5. The system $\dot x=Ax+f(x,u)$ between impulses, $x(t)=g(x^-(t),u^-(t))$ at impulse times, is represented by two maps:
--   1. the transition map of its continuous part, $\phi_c(t,0,x,u)$, the state at time $t$ of the system started at $x$ at time $0$ under input $u$ with no impulses ($T=\emptyset$); by Remark 1 it does not depend on the impulse sequence;
--   2. the jump map $g:X\times U\to X$.
--
--   The standing assumptions are: $\phi_c(0,0,x,u)=x$; the cocycle property
--   $$\phi_c(t+s,0,x,u)=\phi_c\big(t,0,\phi_c(s,0,x,u),u(\cdot+s)\big),\qquad s,t\ge0,$$
--   for inputs in $U_c$ (existence and uniqueness of solutions); $t\mapsto\phi_c(t,0,x,u)$ is continuous on $[0,\infty)$ for inputs in $U_c$; and $0$ is an equilibrium of the unforced system: $\phi_c(t,0,0,0)=0$ for $t\ge0$ and $g(0,0)=0$ (p. 4).
--
--   **Lie derivative** (3.3), p. 4. For $V:X\to\mathbb R_+$, $x\in X$ and an input $u$,
--   $$\dot V_u(x)=\overline{\lim_{t\to+0}}\ \frac1t\Big(V\big(\phi_c(t,0,x,u)\big)-V(x)\Big),$$
--   the upper right Dini derivative at $0$ of $t\mapsto V(\phi_c(t,0,x,u))$, taken in the extended reals $[-\infty,+\infty]$.
--
--   **ISS-Lyapunov function** (Definition 4, global case $D=X$, pp. 4–5). A continuous $V:X\to\mathbb R_+$ is an ISS-Lyapunov function for the system with bounds $\psi_1,\psi_2\in\mathcal K_\infty$, gain $\chi\in\mathcal K_\infty$, jump rate $\alpha\in\mathcal P$ and flow rate $\varphi$ if
--   $$\psi_1(\|x\|_X)\le V(x)\le\psi_2(\|x\|_X)\quad(x\in X),\tag{3.1}$$
--   $\varphi:\mathbb R_+\to\mathbb R$ is continuous with $\varphi(r)=0\iff r=0$, and for all $x\in X$, $\xi\in U$ and $u\in U_c$ with $u(0)=\xi$,
--   $$V(x)\ge\chi(\|\xi\|_U)\ \Longrightarrow\ \dot V_u(x)\le-\varphi(V(x))\ \text{ and }\ V(g(x,\xi))\le\alpha(V(x)).\tag{3.2}$$
--
--   These objects carry every statement of the mission: Theorem 8 constructs a function of this kind for an interconnection, and Proposition 3.1 connects the max form of the jump condition to Definition 4.
--
--   **Formalization Note** The system is modelled by the pair $(\phi_c,g)$ rather than by $A$, $f$ and a $C_0$-semigroup: every hypothesis and conclusion of the paper's results touches the system only through these two maps. The initial time is fixed at $t_0=0$, as in the paper's reduction (2.2). Comparison functions are maps $\mathbb R_{\ge0}\to\mathbb R_{\ge0}$ from the referenced definition `SmallGainISS.Lyapunov.Gains` (`IsK`, `IsKInf`, `IsPosDef`), and norms enter them as `‖x‖₊`. The Dini derivative is the referenced `diniUpperRight`, valued in `EReal`, so an infinite upper limit is never replaced by a junk real value. Inputs are functions on all of $\mathbb R$; only their values on $[0,\infty)$ enter.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, pp. 3–5, §2 (system (2.1), inputs U_c, f(0,0)=g(0,0)=0), Definition 1, Definition 4, (3.1)–(3.3), Remark 1

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative

open scoped NNReal
open Filter Topology

namespace ImpulsiveISS.SmallGain

open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

/-! Dashkovskiy and Mironchenko, *Input-to-state stability of nonlinear impulsive systems*,
arXiv:1212.5481v1: the impulsive system (2.1) through its continuous-part transition map `φ_c` and
its jump map `g` (pp. 3–5, Remark 1), piecewise right-continuous inputs (p. 3), the Lie derivative
(3.3) (p. 4) and ISS-Lyapunov functions (Definition 4, pp. 4–5).

Conventions: `ℝ₊` is `ℝ≥0`; the initial time is `t₀ = 0`; inputs are functions `ℝ → U` of which
only the values on `[0, ∞)` matter. -/

section System

variable {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]

/-- An input `u ∈ U_c = PC([0, ∞), U)` (p. 3): on `[0, ∞)` it is right-continuous, has a left limit
at every `t > 0`, is continuous at all but finitely many points of every `(0, T]`, and is bounded
(so that `‖u‖_{U_c} = sup_{t ≥ 0} ‖u(t)‖` is finite). Values at negative times are ignored. -/
def IsPCInput (u : ℝ → U) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt u (Set.Ici t) t) ∧
  (∀ t : ℝ, 0 < t → ∃ l : U, Tendsto u (𝓝[<] t) (𝓝 l)) ∧
  (∀ T : ℝ, {t : ℝ | t ∈ Set.Ioc 0 T ∧ ¬ ContinuousAt u t}.Finite) ∧
  (∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤ M)

variable (X U) in
/-- An impulsive system (2.1) on the state space `X` with input values in `U`, given by
`flow t x u = φ_c(t, 0, x, u)`, the state at time `t` of the continuous part (no impulses,
`T = ∅`) started at `x` at time `0` under the input `u` (p. 5, Remark 1), and the jump map
`jump = g : X × U → X`. -/
structure ImpulsiveSystem where
  /-- `φ_c(t, 0, x, u)`. -/
  flow : ℝ → X → (ℝ → U) → X
  /-- The jump map `g`. -/
  jump : X → U → X

/-- The standing assumptions on an impulsive system (pp. 3–4): the flow starts at its initial
state, has the cocycle property for piecewise-continuous inputs (existence and uniqueness of
solutions, the case `T = ∅` of (2.2)), is continuous in time on `[0, ∞)`, and `0` is an
equilibrium of the unforced system, `f(0,0) = g(0,0) = 0`. -/
def IsImpulsiveSystem (S : ImpulsiveSystem X U) : Prop :=
  (∀ x u, S.flow 0 x u = x) ∧
  (∀ x u, IsPCInput u → ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
    S.flow (t + s) x u = S.flow t (S.flow s x u) (fun r => u (r + s))) ∧
  (∀ x u, IsPCInput u → ContinuousOn (fun t => S.flow t x u) (Set.Ici 0)) ∧
  (∀ t : ℝ, 0 ≤ t → S.flow t 0 (fun _ => 0) = 0) ∧
  S.jump 0 0 = 0

/-- The Lie derivative (3.3), p. 4:
`V̇_u(x) = limsup_{t → +0} (V(φ_c(t, 0, x, u)) − V(x)) / t`, the upper right Dini derivative at
`0` of `t ↦ V(φ_c(t, 0, x, u))`, valued in the extended reals. -/
noncomputable def lieDeriv (S : ImpulsiveSystem X U) (V : X → ℝ≥0) (x : X) (u : ℝ → U) : EReal :=
  diniUpperRight (fun t => (V (S.flow t x u) : ℝ)) 0

/-- `V` is an ISS-Lyapunov function for `S` (Definition 4, pp. 4–5, the global case `D = X`) with
bounds `ψ₁, ψ₂ ∈ 𝒦∞`, gain `χ ∈ 𝒦∞`, jump rate `α ∈ 𝒫` and flow rate `φ`: `V` is continuous,
`ψ₁(‖x‖) ≤ V(x) ≤ ψ₂(‖x‖)` (3.1), `φ : ℝ₊ → ℝ` is continuous with `φ(r) = 0 ⟺ r = 0`, and for
all `x ∈ X`, `ξ ∈ U` and inputs `u ∈ U_c` with `u(0) = ξ`, `V(x) ≥ χ(‖ξ‖)` implies
`V̇_u(x) ≤ −φ(V(x))` and `V(g(x, ξ)) ≤ α(V(x))` (3.2). -/
def IsISSLyapunovWith (S : ImpulsiveSystem X U) (V : X → ℝ≥0) (ψ₁ ψ₂ χ α : ℝ≥0 → ℝ≥0)
    (φ : ℝ≥0 → ℝ) : Prop :=
  Continuous V ∧ IsKInf ψ₁ ∧ IsKInf ψ₂ ∧ (∀ x, ψ₁ ‖x‖₊ ≤ V x ∧ V x ≤ ψ₂ ‖x‖₊) ∧
  IsKInf χ ∧ IsPosDef α ∧ Continuous φ ∧ (∀ r, φ r = 0 ↔ r = 0) ∧
  ∀ x ξ u, IsPCInput u → u 0 = ξ → χ ‖ξ‖₊ ≤ V x →
    lieDeriv S V x u ≤ ((-(φ (V x)) : ℝ) : EReal) ∧ V (S.jump x ξ) ≤ α (V x)

/-- `V` is an ISS-Lyapunov function for `S` (Definition 4, global case). -/
def IsISSLyapunov (S : ImpulsiveSystem X U) (V : X → ℝ≥0) : Prop :=
  ∃ (ψ₁ ψ₂ χ α : ℝ≥0 → ℝ≥0) (φ : ℝ≥0 → ℝ), IsISSLyapunovWith S V ψ₁ ψ₂ χ α φ

end System

end ImpulsiveISS.SmallGain


