-- Prove2me | Definitions.Def_NonsmoothQN_LineSearch_Basic
-- name    : NonsmoothQN_LineSearch_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:08.695208+00:00
-- url     : https://prove2.me/theorems/f55de6df-4879-4764-84b9-8a48318a1b85
-- title:
--   Assumption 4.1, (4.2)–(4.3), Algorithm 4.6, (4.8), pp. 145–148 — line-search objective, Armijo–Wolfe steps, bisection line search
-- statement:
--   This file fixes the objects of §4 of Lewis and Overton's analysis of an inexact line search for nonsmooth optimization.
--
--   **The line search objective.** Let $\bar x$ be an iterate and $\bar p$ a search direction of an optimization algorithm for $f$. The line search works with the univariate function $h(t) = f(\bar x + t\bar p) - f(\bar x)$, $t \ge 0$; only $h$ enters. We take $h:\mathbb R\to\mathbb R$; only its values on $[0,\infty)$ matter.
--
--   **Assumption 4.1.** The function $h$ is absolutely continuous on every bounded interval $[a,b]\subset[0,\infty)$, bounded below on $[0,\infty)$, and satisfies
--   $$h(0)=0 \quad\text{and}\quad s=\limsup_{t\downarrow 0}\frac{h(t)}{t}<0 .$$
--
--   **Armijo and Wolfe conditions.** Given constants $c_1<c_2$ in $(0,1)$, the Armijo condition $A(t)$ and the Wolfe condition $W(t)$ are
--   $$A(t):\ h(t)<c_1 s t, \qquad W(t):\ h \text{ is differentiable at } t \text{ with } h'(t)>c_2 s .$$
--   An **Armijo–Wolfe step** is a number $t>0$ satisfying both (equations (4.2)–(4.3)).
--
--   **Algorithm 4.6 (line search).** Start with $\alpha=0$, $\beta=+\infty$, $t=1$ and repeat: if $A(t)$ fails, set $\beta\leftarrow t$; else if $W(t)$ fails, set $\alpha\leftarrow t$; else stop. After an update, set $t\leftarrow(\alpha+\beta)/2$ if $\beta<+\infty$ and $t\leftarrow 2\alpha$ otherwise. Each execution of the loop is a **trial**. The state $(\alpha_n,\beta_n,t_n)$ before trial $n=0,1,2,\dots$ is given explicitly, so trial $0$ tests $t_0=1$. The line search **terminates** if some trial step satisfies both $A$ and $W$.
--
--   **Condition (4.8).** For every $\bar t>0$, $h$ is differentiable on an interval $(t',\bar t)$ and $\lim_{t\uparrow\bar t}h'(t)$ exists in $[-\infty,+\infty]$.
--
--   **Weak lower semismoothness** (p. 148, restricted form). $h$ is locally Lipschitz around $\bar t$ and, for $d=\pm1$ and every sequence $\tau_k\downarrow0$ such that $h$ is differentiable at $\bar t+\tau_k d$,
--   $$\liminf_{\tau\downarrow0}\frac{h(\bar t+\tau d)-h(\bar t)}{\tau}\ \ge\ \limsup_k h'(\bar t+\tau_k d)\,d .$$
--
--   These objects are shared by every statement of the mission: the existence of Armijo–Wolfe steps, the convergence of the line search, and its complexity on convex functions.
--
--   **Formalization Note.** The $\limsup$ of Assumption 4.1 is computed in the extended reals and required to equal the real number $s$. The upper bound $\beta$ lives in $\mathbb R\cup\{+\infty\}$ (`WithTop ℝ`, with $\top=+\infty$). Stopping is encoded by freezing the state: the step map returns the state unchanged once both tests pass, and `Terminates` says that some trial passes both. `deriv h t` is Mathlib's derivative, which is $0$ where $h$ is not differentiable, so every use carries differentiability explicitly: $W$ includes it, and (4.8) is read as differentiability on a left neighbourhood plus the existence of the limit, which is what the paper's proof uses (p. 148: "the function $h$ is differentiable on some nonempty open interval $(t',\tilde t)$"). In the weak lower semismoothness condition, the paper takes $\{g_k\}$ to be arbitrary subgradients of $h$ at $\bar t+\tau_k d$; here the $g_k$ are restricted to derivatives at points of differentiability (which are subgradients), the case used in the paper's argument. This is a weaker hypothesis, so the corresponding theorem is stronger than the paper's claim.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, pp. 145–148, Assumption 4.1, (4.2)–(4.3), Algorithm 4.6, (4.8), weak lower semismoothness (§4.1)

import Mathlib

namespace NonsmoothQN.LineSearch

open Filter Topology MeasureTheory Set

/-- Assumption 4.1 (Lewis–Overton, p. 145). The line search objective `h : ℝ₊ → ℝ` is absolutely
continuous on every bounded interval and bounded below, `h(0) = 0`, and
`s = limsup_{t ↓ 0} h(t)/t < 0`. Only the values of `h` on `[0, ∞)` enter. The `limsup` is taken
in `EReal`, so it is never a junk value; the assumption says it is the real number `s`. -/
structure Assumption41 (h : ℝ → ℝ) (s : ℝ) : Prop where
  absCont : ∀ a b : ℝ, 0 ≤ a → a ≤ b → AbsolutelyContinuousOnInterval h a b
  bddBelow : BddBelow (h '' Set.Ici 0)
  zero : h 0 = 0
  limsup_eq : Filter.limsup (fun t : ℝ => ((h t / t : ℝ) : EReal)) (𝓝[>] 0) = (s : EReal)
  neg : s < 0

/-- The Armijo condition (4.2): `A(t) : h(t) < c₁ s t`. -/
def ArmijoA (h : ℝ → ℝ) (c₁ s t : ℝ) : Prop :=
  h t < c₁ * s * t

/-- The Wolfe condition (4.3): `W(t) : h` is differentiable at `t` with `h'(t) > c₂ s`. -/
def WolfeW (h : ℝ → ℝ) (c₂ s t : ℝ) : Prop :=
  DifferentiableAt ℝ h t ∧ c₂ * s < deriv h t

/-- An Armijo–Wolfe step (p. 146): a number `t > 0` satisfying `A(t)` and `W(t)`. -/
def IsAWStep (h : ℝ → ℝ) (c₁ c₂ s t : ℝ) : Prop :=
  0 < t ∧ ArmijoA h c₁ s t ∧ WolfeW h c₂ s t

/-- The state `(α, β, t)` of Algorithm 4.6: lower bound `α`, upper bound `β ∈ ℝ ∪ {+∞}`
(`⊤` is `+∞`), and the current trial step `t`. -/
structure LSState where
  α : ℝ
  β : WithTop ℝ
  t : ℝ

/-- The initial state of Algorithm 4.6: `α ← 0`, `β ← +∞`, `t ← 1`. -/
def LSState.init : LSState := ⟨0, ⊤, 1⟩

/-- The next trial of Algorithm 4.6 from the bracket `(α, β)`:
`t ← (α + β)/2` if `β < +∞`, else `t ← 2α`. -/
noncomputable def nextTrial (α : ℝ) (β : WithTop ℝ) : ℝ :=
  if hβ : β = ⊤ then 2 * α else (α + β.untop hβ) / 2

/-- One execution of the repeat loop of Algorithm 4.6 (one *trial*). If `A(t)` fails, `β ← t`;
else if `W(t)` fails, `α ← t`; in both cases the next trial is `nextTrial α β`. Otherwise the
algorithm stops, which is encoded by returning the state unchanged (it is frozen from then on). -/
noncomputable def lsStep (h : ℝ → ℝ) (c₁ c₂ s : ℝ) (σ : LSState) : LSState := by
  classical
  exact
    if ¬ ArmijoA h c₁ s σ.t then
      ⟨σ.α, (σ.t : WithTop ℝ), nextTrial σ.α (σ.t : WithTop ℝ)⟩
    else if ¬ WolfeW h c₂ s σ.t then
      ⟨σ.t, σ.β, nextTrial σ.t σ.β⟩
    else σ

/-- The state of Algorithm 4.6 before trial `n` (`n = 0, 1, 2, …`); trial `n` tests the step
`(lsRun h c₁ c₂ s n).t`, so trial `0` tests `t = 1`. -/
noncomputable def lsRun (h : ℝ → ℝ) (c₁ c₂ s : ℝ) (n : ℕ) : LSState :=
  (lsStep h c₁ c₂ s)^[n] LSState.init

/-- Algorithm 4.6 terminates: some trial step passes both `A` and `W` (it stops at the first). -/
def Terminates (h : ℝ → ℝ) (c₁ c₂ s : ℝ) : Prop :=
  ∃ n : ℕ, ArmijoA h c₁ s (lsRun h c₁ c₂ s n).t ∧ WolfeW h c₂ s (lsRun h c₁ c₂ s n).t

/-- Condition (4.8): for every `t̄ > 0`, `lim_{t ↑ t̄} h'(t)` exists in `[−∞, +∞]`. Read, as the
proof on p. 148 uses it, as: `h` is differentiable on a left neighbourhood of `t̄`, and the
derivative has a limit in `EReal` as `t ↑ t̄`. -/
def Cond48 (h : ℝ → ℝ) : Prop :=
  ∀ tbar : ℝ, 0 < tbar →
    (∀ᶠ t in 𝓝[<] tbar, DifferentiableAt ℝ h t) ∧
      ∃ L : EReal, Tendsto (fun t => ((deriv h t : ℝ) : EReal)) (𝓝[<] tbar) (𝓝 L)

/-- Weak lower semismoothness of `h` at `t̄` (p. 148), with the subgradients `g_k` restricted to
derivatives `h'(t̄ + τ_k d)` at points where `h` is differentiable: `h` is locally Lipschitz
around `t̄`, and for `d = ±1` and every sequence `τ_k ↓ 0` with `h` differentiable at
`t̄ + τ_k d`,
`liminf_{τ ↓ 0} (h(t̄ + τ d) − h(t̄))/τ ≥ limsup_k h'(t̄ + τ_k d) d`. -/
def WeaklyLowerSemismoothDeriv (h : ℝ → ℝ) (tbar : ℝ) : Prop :=
  (∃ K : NNReal, ∃ U ∈ 𝓝 tbar, LipschitzOnWith K h U) ∧
    ∀ d : ℝ, (d = 1 ∨ d = -1) → ∀ τ : ℕ → ℝ, (∀ k, 0 < τ k) → Antitone τ →
      Tendsto τ atTop (𝓝 0) → (∀ k, DifferentiableAt ℝ h (tbar + τ k * d)) →
        Filter.limsup (fun k => ((deriv h (tbar + τ k * d) * d : ℝ) : EReal)) atTop ≤
          Filter.liminf (fun τ' : ℝ => (((h (tbar + τ' * d) - h tbar) / τ' : ℝ) : EReal))
            (𝓝[>] 0)

end NonsmoothQN.LineSearch


