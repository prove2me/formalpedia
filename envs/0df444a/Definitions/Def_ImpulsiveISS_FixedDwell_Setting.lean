-- Prove2me | Definitions.Def_ImpulsiveISS_FixedDwell_Setting
-- name    : ImpulsiveISS_FixedDwell_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T17:44:20.822912+00:00
-- url     : https://prove2.me/theorems/e97f1fa5-fef5-4438-b10a-41e4920d238c
-- title:
--   §2–3, pp. 3–9 — impulsive system (φ_c, g), PC inputs, trajectory, classes L and KL, ISS, Lie derivative, max-form ISS-Lyapunov function, S_θ, condition (3.7), F and α̃
-- statement:
--   This file fixes the objects of Sections 2–3 of Dashkovskiy and Mironchenko that Theorem 1 and its proof use.
--
--   **Impulsive system** ((2.1), p. 3). Let $X$ (states) and $U$ (input values) be Banach spaces. The system
--   $$\dot x(t)=Ax(t)+f(x(t),u(t)),\quad t\notin T,\qquad x(t)=g(x^-(t),u^-(t)),\quad t\in T,$$
--   is described by two maps: the transition map $\phi_c(t,0,x,u)$ of its continuous part (the state at time $t$ when the state at time $0$ was $x$, the input $u$ was applied and there were no impulses; Remark 1, p. 5), and the jump map $g:X\times U\to X$. Its standing assumptions are: $\phi_c(0,0,x,u)=x$; the cocycle property $\phi_c(t+s,0,x,u)=\phi_c(t,0,\phi_c(s,0,x,u),u(\cdot+s))$ for $s,t\ge0$ and admissible $u$ (existence and uniqueness of solutions); continuity of $t\mapsto\phi_c(t,0,x,u)$ on $[0,\infty)$; and $x\equiv0$ is an equilibrium: $\phi_c(t,0,0,0)=0$ and $g(0,0)=0$ (p. 4).
--
--   **Admissible inputs** (p. 3). $U_c=PC([0,\infty),U)$: functions that are right-continuous on $[0,\infty)$, have a left limit at every $t>0$, have finitely many discontinuities in every $[0,T]$, and are bounded; $\|u\|_{U_c}=\sup_{t\ge0}\|u(t)\|$.
--
--   **Impulse times and trajectory** (p. 3). An impulse-time sequence $t_1<t_2<\cdots$ is strictly increasing, positive and tends to $\infty$. $N(t,s)$ is the number of impulse times in $(s,t]$. The trajectory $x(t)=\phi(t,0,x_0,u)$ flows by $\phi_c$ between impulses, with the input shifted to the start of the piece, and at $t_k$ jumps to $g(x^-(t_k),u^-(t_k))$, where $u^-$ is the left limit of the input.
--
--   **Comparison functions** (Definition 1, p. 4). $\mathcal L$: continuous, strictly decreasing functions $\mathbb R_+\to\mathbb R_+$ tending to $0$; $\mathcal{KL}$: continuous $\beta:\mathbb R_+^2\to\mathbb R_+$ with $\beta(\cdot,t)\in\mathcal K$ for each $t\ge0$ and $\beta(r,\cdot)\in\mathcal L$ for each $r>0$. ($\mathcal P,\mathcal K,\mathcal K_\infty$ come from the referenced definition `SmallGainISS.Lyapunov.Gains`.)
--
--   **ISS** (Definition 2, p. 4). For a given impulse sequence, the system is ISS if there are $\beta\in\mathcal{KL}$ and $\gamma\in\mathcal K_\infty$ with
--   $$\|x(t)\|\le\beta(\|x_0\|,t)+\gamma(\|u\|_{U_c})\qquad\text{for all }x_0\in X,\ u\in U_c,\ t\ge0.$$
--
--   **Lie derivative** ((3.3), p. 4). $\dot V_u(x)=\limsup_{t\to+0}\frac1t\big(V(\phi_c(t,0,x,u))-V(x)\big)$, an extended real number.
--
--   **ISS-Lyapunov function in max form** (Proposition 3.1, p. 5). A continuous $V:X\to\mathbb R_+$ with $\psi_1(\|x\|)\le V(x)\le\psi_2(\|x\|)$ (3.1), $\psi_1,\psi_2,\gamma\in\mathcal K_\infty$, $\alpha\in\mathcal P$ and a flow rate $\varphi$, such that
--   1. (3.5) for all $\xi\in U$ and $u\in U_c$ with $u(0)=\xi$: $V(x)\ge\gamma(\|\xi\|)\Rightarrow\dot V_u(x)\le-\varphi(V(x))$;
--   2. (3.6) for all $x\in X$, $\xi\in U$: $V(g(x,\xi))\le\max\{\alpha(V(x)),\gamma(\|\xi\|)\}$.
--
--   **Dwell-time objects** (pp. 6–9). $S_\theta$ is the set of impulse sequences with $t_{i+1}-t_i\ge\theta$ for all $i$. The nonlinear fixed dwell-time condition (3.7) reads $\int_a^{\alpha(a)}\frac{ds}{\varphi(s)}\le\theta-\delta$ for all $a>0$. The proof of Theorem 1 uses $F(q)=\int_r^q\frac{ds}{\varphi(s)}$ for a fixed $r>0$ and $\tilde\alpha(x)=\max\{\max_{0\le s\le\gamma(x)}\alpha(s),\gamma(x)\}$.
--
--   These objects carry Theorem 1 and every milestone of its proof.
--
--   **Formalization Note** The semigroup generator $A$ and $f$ are not modelled: every statement of the paper uses them only through $\phi_c$, which is a field `flow` of the structure `System`, with the jump map `jump`. The initial time is $t_0=0$, the paper's own reduction (2.2). Impulse times are `τ : ℕ → ℝ` with `τ i` the paper's $t_{i+1}$, and the first impulse is strictly after $t_0$ (a jump at $t_0$ would need $x^-(t_0)$). $N(t,s)$ is `Nat.card` of the impulse indices in $(s,t]$, finite because `τ i → ∞`. ISS replaces $\|u\|_{U_c}$ by an arbitrary bound $M\ge\|u(t)\|$, $t\ge0$ (equivalent because $\gamma$ is increasing; no supremum is taken). The Lie derivative is the referenced `diniUpperRight` at $0$, valued in `EReal`. $F$ is an oriented interval integral, used only at positive arguments, where $1/\varphi$ is continuous on the segment. The inner maximum of $\tilde\alpha$ is `sSup` of the image of $[0,\gamma(x)]$ under the continuous $\alpha$, a nonempty compact set. The definitions duplicate those of the sibling missions 2 and 3 of this series by design (drafts cannot import drafts).
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, pp. 3–9: (2.1), (2.2), Definitions 1, 2, 4, (3.3), Remark 1, Proposition 3.1 (3.1), (3.5), (3.6), S_θ and (3.7) on p. 6, F on p. 7, α̃ on p. 9

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative

open scoped NNReal
open Filter Topology

namespace ImpulsiveISS.FixedDwell

/-!
Dashkovskiy and Mironchenko, *Input-to-state stability of nonlinear impulsive systems*,
arXiv:1212.5481v1: the impulsive system (2.1) (p. 3), the comparison classes `𝓛`, `𝒦𝓛`
(Definition 1, p. 4), ISS for a given impulse-time sequence (Definition 2, p. 4), the Lie
derivative (3.3) (p. 4), ISS-Lyapunov functions in the max form of Proposition 3.1 (p. 5), the
class `S_θ` and the dwell-time condition (3.7) (p. 6), and the function
`F(q) = ∫_r^q ds/φ(s)` of the proof of Theorem 1 (p. 7).

Conventions. The system is modelled by the transition map `φ_c` of its continuous part (Remark 1,
p. 5) and its jump map `g`; the semigroup generator `A` and `f` enter every statement of the paper
only through `φ_c`. The initial time is `t₀ = 0` (the reduction (2.2), p. 3). `ℝ₊` is `ℝ≥0`;
`𝒦`, `𝒦∞`, `𝒫` are `IsK`, `IsKInf`, `IsPosDef` from `SmallGainISS.Lyapunov`. Impulse times
`t₁ < t₂ < ⋯` are `τ 0 < τ 1 < ⋯` (0-based: `τ i` is the paper's `t_{i+1}`).
-/

open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

/-- Class `𝓛` (Definition 1, p. 4): continuous, strictly decreasing, tending to `0` at `∞`. -/
def IsL (γ : ℝ≥0 → ℝ≥0) : Prop :=
  Continuous γ ∧ StrictAnti γ ∧ Tendsto γ atTop (𝓝 0)

/-- Class `𝒦𝓛` (Definition 1, p. 4): `β` jointly continuous, `β(·, t) ∈ 𝒦` for every `t ≥ 0`,
`β(r, ·) ∈ 𝓛` for every `r > 0`. -/
def IsKL (β : ℝ≥0 → ℝ≥0 → ℝ≥0) : Prop :=
  Continuous (Function.uncurry β) ∧ (∀ t, IsK (fun r => β r t)) ∧ ∀ r, 0 < r → IsL (β r)

/-- The impulsive system (2.1), p. 3, through its continuous-part transition map and its jump map
(Remark 1, p. 5). `flow t x u` is `φ_c(t, 0, x, u)`: the state at time `t` of the continuous
part started at `x` at time `0`, under the input `u`, with no impulses (`T = ∅`). `jump x ξ` is
`g(x, ξ)`. -/
structure System (X U : Type*) where
  /-- `φ_c(t, 0, x, u)`. -/
  flow : ℝ → X → (ℝ → U) → X
  /-- The jump map `g : X × U → X`. -/
  jump : X → U → X

/-- The input shifted by `s`: `r ↦ u(r + s)`. -/
def shift {U : Type*} (u : ℝ → U) (s : ℝ) : ℝ → U := fun r => u (r + s)

/-- Admissible inputs `U_c = PC([t₀, ∞), U)` (p. 3), with `t₀ = 0`: piecewise right-continuous
functions on `[0, ∞)` with values in `U`, bounded (so that `‖u‖_{U_c} = sup_{t ≥ 0} ‖u(t)‖` is
finite). "Piecewise" is encoded as: right-continuous at every `t ≥ 0`, a left limit at every
`t > 0`, and only finitely many discontinuities (of the restriction to `[0, ∞)`) in every
`[0, T]`. Values at negative times are irrelevant. -/
def IsPCInput {U : Type*} [NormedAddCommGroup U] (u : ℝ → U) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ContinuousWithinAt u (Set.Ici t) t) ∧
  (∀ t : ℝ, 0 < t → ∃ v : U, Tendsto u (𝓝[<] t) (𝓝 v)) ∧
  (∀ T : ℝ, Set.Finite {t : ℝ | t ∈ Set.Icc 0 T ∧ ¬ ContinuousWithinAt u (Set.Ici 0) t}) ∧
  (∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → ‖u t‖ ≤ M)

/-- The standing assumptions on the system (pp. 3–4): the continuous part starts at its initial
state, has the cocycle (semigroup) property of a uniquely solvable time-invariant evolution (the
`T = ∅` case of (2.2)), is continuous in time (the mild solution is continuous between impulses),
and `x ≡ 0` is an equilibrium: `φ_c(t, 0, 0, 0) = 0` and `g(0, 0) = 0` (`f(0,0) = g(0,0) = 0`,
p. 4). -/
def IsImpulsiveSystem {X U : Type*} [NormedAddCommGroup X] [NormedAddCommGroup U]
    (S : System X U) : Prop :=
  (∀ (x : X) (u : ℝ → U), S.flow 0 x u = x) ∧
  (∀ (x : X) (u : ℝ → U), IsPCInput u → ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
    S.flow (t + s) x u = S.flow t (S.flow s x u) (shift u s)) ∧
  (∀ (x : X) (u : ℝ → U), IsPCInput u → ContinuousOn (fun t => S.flow t x u) (Set.Ici 0)) ∧
  (∀ t : ℝ, 0 ≤ t → S.flow t 0 (fun _ => 0) = 0) ∧ S.jump 0 0 = 0

/-- A sequence of impulse times `t₁ < t₂ < ⋯` (p. 3): strictly increasing, without finite
accumulation points (`τ i → ∞`), after the initial time `t₀ = 0`. `τ i` is the paper's
`t_{i+1}`. The first impulse is taken strictly after `t₀` (a jump at `t₀` would use the left limit
`x⁻(t₀)` before the initial time). -/
def IsImpulseSeq (τ : ℕ → ℝ) : Prop :=
  StrictMono τ ∧ 0 < τ 0 ∧ Tendsto τ atTop atTop

/-- `N(t, s)`: the number of impulse times in `(s, t]` (p. 11). It is finite for an impulse
sequence, because `τ i → ∞`. -/
noncomputable def N (τ : ℕ → ℝ) (t s : ℝ) : ℕ :=
  Nat.card {k : ℕ // s < τ k ∧ τ k ≤ t}

/-- The start of the `k`-th impulse-free piece of the trajectory: `0` for `k = 0`, `τ (k-1)`
(the paper's `t_k`) for `k ≥ 1`. -/
def epoch (τ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => τ k

/-- The state at the start of the `k`-th piece: `x₀` for `k = 0`; for `k ≥ 0`, the state just
after the jump at `τ k`, i.e. `g(x⁻(τ k), u⁻(τ k))` with `x⁻(τ k)` the state reached by the flow
over `[epoch k, τ k)` and `u⁻(τ k)` the left limit of the input (2.1). -/
noncomputable def post {X U : Type*} [TopologicalSpace U] (S : System X U) (τ : ℕ → ℝ) (x₀ : X)
    (u : ℝ → U) : ℕ → X
  | 0 => x₀
  | k + 1 =>
      S.jump (S.flow (τ k - epoch τ k) (post S τ x₀ u k) (shift u (epoch τ k)))
        (Function.leftLim u (τ k))

/-- The trajectory `x(t) = φ(t, 0, x₀, u)` of (2.1) for the impulse times `τ` (p. 3): on the
`k`-th piece, `k = N(t, 0)` the number of impulses in `(0, t]`, the continuous part flows from
`post k` with the input shifted to the piece's start. Meaningful for `t ≥ 0`. -/
noncomputable def traj {X U : Type*} [TopologicalSpace U] (S : System X U) (τ : ℕ → ℝ) (x₀ : X)
    (u : ℝ → U) (t : ℝ) : X :=
  S.flow (t - epoch τ (N τ t 0)) (post S τ x₀ u (N τ t 0)) (shift u (epoch τ (N τ t 0)))

/-- ISS for a given impulse-time sequence (Definition 2, p. 4, with `t₀ = 0`): there are
`β ∈ 𝒦𝓛` and `γ ∈ 𝒦∞` with `‖x(t)‖ ≤ β(‖x₀‖, t) + γ(‖u‖_{U_c})` for all `x₀`, all admissible `u`
and all `t ≥ 0`. `‖u‖_{U_c}` is replaced by an arbitrary bound `M ≥ ‖u(t)‖` (`t ≥ 0`), which is
equivalent because `γ` is increasing. -/
def IsISS {X U : Type*} [NormedAddCommGroup X] [NormedAddCommGroup U] (S : System X U)
    (τ : ℕ → ℝ) : Prop :=
  ∃ (β : ℝ≥0 → ℝ≥0 → ℝ≥0) (γ : ℝ≥0 → ℝ≥0), IsKL β ∧ IsKInf γ ∧
    ∀ (x₀ : X) (u : ℝ → U), IsPCInput u → ∀ M : ℝ≥0, (∀ t : ℝ, 0 ≤ t → ‖u t‖₊ ≤ M) →
      ∀ t : ℝ, 0 ≤ t → ‖traj S τ x₀ u t‖₊ ≤ β ‖x₀‖₊ t.toNNReal + γ M

/-- The Lie derivative (3.3), p. 4: `V̇_u(x) = limsup_{t → +0} (V(φ_c(t, 0, x, u)) − V(x))/t`, the
upper right Dini derivative at `0` of `t ↦ V(φ_c(t, 0, x, u))`, valued in `EReal`. -/
noncomputable def lieDeriv {X U : Type*} (S : System X U) (V : X → ℝ≥0) (x : X) (u : ℝ → U) :
    EReal :=
  diniUpperRight (fun t => (V (S.flow t x u) : ℝ)) 0

/-- `V` is an ISS-Lyapunov function in the max form of Proposition 3.1 (p. 5), with flow rate `φ`:
`V` is continuous; (3.1) `ψ₁(‖x‖) ≤ V(x) ≤ ψ₂(‖x‖)` with `ψ₁, ψ₂ ∈ 𝒦∞`; `γ ∈ 𝒦∞`, `α ∈ 𝒫`;
(3.5) for all `ξ ∈ U` and all admissible `u` with `u(0) = ξ`,
`V(x) ≥ γ(‖ξ‖) ⇒ V̇_u(x) ≤ −φ(V(x))`; (3.6) for all `x, ξ`,
`V(g(x, ξ)) ≤ max{α(V(x)), γ(‖ξ‖)}`. -/
def IsISSLyapunovMax {X U : Type*} [NormedAddCommGroup X] [NormedAddCommGroup U]
    (S : System X U) (V : X → ℝ≥0) (ψ₁ ψ₂ γ α φ : ℝ≥0 → ℝ≥0) : Prop :=
  Continuous V ∧ IsKInf ψ₁ ∧ IsKInf ψ₂ ∧ (∀ x : X, ψ₁ ‖x‖₊ ≤ V x ∧ V x ≤ ψ₂ ‖x‖₊) ∧
  IsKInf γ ∧ IsPosDef α ∧
  (∀ (x : X) (ξ : U) (u : ℝ → U), IsPCInput u → u 0 = ξ → γ ‖ξ‖₊ ≤ V x →
    lieDeriv S V x u ≤ ((-(φ (V x) : ℝ) : ℝ) : EReal)) ∧
  (∀ (x : X) (ξ : U), V (S.jump x ξ) ≤ max (α (V x)) (γ ‖ξ‖₊))

/-- The class `S_θ` (p. 6): impulse-time sequences whose consecutive impulse times are at least
`θ` apart, `t_{i+1} − t_i ≥ θ` for all `i`. -/
def InSTheta (θ : ℝ) (τ : ℕ → ℝ) : Prop :=
  IsImpulseSeq τ ∧ ∀ i : ℕ, θ ≤ τ (i + 1) - τ i

/-- `F(q) = ∫_r^q ds/φ(s)` (proof of Theorem 1, p. 7), an oriented interval integral. It is used
only at `r > 0`, `q > 0`, where `1/φ` is continuous on the segment between `r` and `q`. -/
noncomputable def Fint (φ : ℝ≥0 → ℝ≥0) (r q : ℝ) : ℝ :=
  ∫ s in r..q, 1 / (φ s.toNNReal : ℝ)

/-- The nonlinear fixed dwell-time condition (3.7), p. 6: for all `a > 0`,
`∫_a^{α(a)} ds/φ(s) ≤ θ − δ` (an oriented integral, negative when `α(a) < a`). -/
def DwellCondition (α φ : ℝ≥0 → ℝ≥0) (θ δ : ℝ) : Prop :=
  ∀ a : ℝ≥0, 0 < a → Fint φ (a : ℝ) (α a : ℝ) ≤ θ - δ

/-- `α̃(r) = max{max_{0 ≤ s ≤ γ(r)} α(s), γ(r)}` (proof of Theorem 1, p. 9). The inner maximum is
the supremum of the image of the compact interval `[0, γ(r)]` under `α`, a nonempty bounded set
when `α` is continuous. -/
noncomputable def alphaTilde (α γ : ℝ≥0 → ℝ≥0) (r : ℝ≥0) : ℝ≥0 :=
  max (sSup (α '' Set.Icc 0 (γ r))) (γ r)

end ImpulsiveISS.FixedDwell


