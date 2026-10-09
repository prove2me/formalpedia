-- Prove2me | Definitions.Def_NesterovODE_Restart_Setting
-- name    : NesterovODE_Restart_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T04:37:11.060471+00:00
-- url     : https://prove2.me/theorems/86556758-4522-49bd-a4fb-9822e3f0568c
-- title:
--   §1.3, p. 5, and §5.1, p. 22 — the class S_µ,L, the ODE (3), the speed restarting time T and the speed restarted trajectory of (29)
-- statement:
--   Work in $\mathbb R^n$ with the Euclidean norm. A function $f:\mathbb R^n\to\mathbb R$ belongs to $\mathcal F_L$ if it is convex, continuously differentiable, and its gradient is $L$-Lipschitz: $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$. It belongs to $\mathcal S_\mu$ if it is continuously differentiable and $x\mapsto f(x)-\mu\|x\|^2/2$ is convex. The class $\mathcal S_{\mu,L}$ is $\mathcal F_L\cap\mathcal S_\mu$.
--
--   A pair $(X,\dot X)$ solves the ODE (3) from $x_0$ if $X(0)=x_0$, $\dot X(0)=0$, $X$ is continuously differentiable on $[0,\infty)$ (one-sided at $0$), twice differentiable on $(0,\infty)$, and
--
--   $$\ddot X(t)+\frac3t\dot X(t)+\nabla f(X(t))=0,\qquad t>0.$$
--
--   Along such a solution, $\tfrac12\,\mathrm d\|\dot X(u)\|^2/\mathrm du=\langle\dot X(u),\ddot X(u)\rangle=\langle\dot X(u),-\tfrac3u\dot X(u)-\nabla f(X(u))\rangle$. The **speed restarting time** is
--
--   $$T=T(x_0;f)=\sup\Bigl\{t>0:\ \forall u\in(0,t),\ \frac{\mathrm d\|\dot X(u)\|^2}{\mathrm du}>0\Bigr\},$$
--
--   the first time the speed $\|\dot X\|$ decreases.
--
--   A curve $X^{\mathrm{sr}}$ is a **speed restarted trajectory** from $x_0$ (a solution of (29)) if $X^{\mathrm{sr}}(0)=x_0$ and there are restart times $\tau_0=0\le\tau_1\le\cdots$ and solutions $X_i$ of (3) started at $X^{\mathrm{sr}}(\tau_i)$ such that, for each $i$:
--
--   1. if $\nabla f(X^{\mathrm{sr}}(\tau_i))\ne0$, then $\tau_{i+1}=\tau_i+T(X^{\mathrm{sr}}(\tau_i);f)$ and $X^{\mathrm{sr}}(\tau_i+u)=X_i(u)$ for $0\le u\le\tau_{i+1}-\tau_i$;
--   2. if $\nabla f(X^{\mathrm{sr}}(\tau_i))=0$, then $X^{\mathrm{sr}}(t)=X^{\mathrm{sr}}(\tau_i)$ for every $t\ge\tau_i$.
--
--   This is the paper's description of the solution of (29): the friction coefficient $3/t_{\mathrm{sr}}$ is reset whenever the speed stops increasing, and between restarts the trajectory follows (3) from the current point. The restart times are $\tau_i=T_1+\dots+T_i$ in the paper's notation.
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` and $\nabla f$ is Mathlib's `gradient`. $\mathcal S_\mu$ is the paper's literal definition. The velocity is a second function $V$; values at negative times are unconstrained. The speed derivative is written as the inner product $\langle V(u),-\tfrac3uV(u)-\nabla f(X(u))\rangle$ (half of $\mathrm d\|\dot X\|^2/\mathrm du$, which has the same sign), so no `deriv` junk value can enter. `restartTime` is Lean's `sSup`, which is $0$ on an empty or unbounded set; every statement of the mission that bounds $T$ is phrased on the set itself. Clause 2 is the convention that a trajectory reaching a minimizer stays there (the solution of (3) from a stationary point is constant); the paper excludes $x_0=x^\star$ in its lemmas and leaves this case implicit.
-- source:
--   Su, Boyd, Candès, A Differential Equation for Modeling Nesterov's Accelerated Gradient Method, arXiv:1503.01243v2, p. 5 (§1.3, classes F_L, S_µ, S_µ,L), p. 2 (3), p. 21 (§5 standing assumption), p. 22 (§5.1, speed restarting time T, (29) and the three bullet observations)

import Mathlib
import Definitions.Def_NesterovODE_StrongCvx_Setting
import Definitions.Def_NesterovODE_WellPosed_Setting

namespace NesterovODE.Restart

open scoped RealInnerProductSpace

/-- Half the speed derivative `(1/2) d‖Ẋ(u)‖²/du = ⟨Ẋ(u), Ẍ(u)⟩` along a solution of (3),
with `Ẍ(u)` replaced by its value `-(3/u) Ẋ(u) - ∇f(X(u))` from the ODE. -/
noncomputable def halfSpeedDeriv {n : ℕ} (f : NesterovODE.WellPosed.E n → ℝ) (X V : ℝ → NesterovODE.WellPosed.E n) (u : ℝ) : ℝ :=
  ⟪V u, -(3 / u) • V u - gradient f (X u)⟫

/-- The set `{t > 0 : ∀ u ∈ (0, t), d‖Ẋ(u)‖²/du > 0}` whose supremum is the speed
restarting time (p. 22), for a solution `(X, V)` of (3). -/
def restartSet {n : ℕ} (f : NesterovODE.WellPosed.E n → ℝ) (X V : ℝ → NesterovODE.WellPosed.E n) : Set ℝ :=
  {t | 0 < t ∧ ∀ u ∈ Set.Ioo 0 t, 0 < halfSpeedDeriv f X V u}

/-- The speed restarting time `T = sup {t > 0 : ∀ u ∈ (0, t), d‖Ẋ(u)‖²/du > 0}` (p. 22).
Lean's `sSup` returns `0` on an empty or unbounded set; statements about `T` are phrased
so that this value is never used (Lemmas 13, 25 bound `restartSet` directly). -/
noncomputable def restartTime {n : ℕ} (f : NesterovODE.WellPosed.E n → ℝ) (X V : ℝ → NesterovODE.WellPosed.E n) : ℝ :=
  sSup (restartSet f X V)

/-- `Xsr` is a solution of the speed restarted ODE (29) from `x₀` (p. 22): there are restart
times `τ 0 = 0 ≤ τ 1 ≤ …` and solutions `(Y i, W i)` of (3) started at `Xsr (τ i)` such that
* if `∇f(Xsr(τ i)) ≠ 0`, the next restart is `τ (i+1) = τ i + T(Xsr(τ i); f)` and `Xsr` follows
  `Y i` on `[τ i, τ (i+1)]`;
* if `∇f(Xsr(τ i)) = 0` (a minimizer has been reached), `Xsr` stays at `Xsr(τ i)` from then on
  (the solution of (3) from a stationary point is constant). -/
def IsSpeedRestarted {n : ℕ} (f : NesterovODE.WellPosed.E n → ℝ) (x₀ : NesterovODE.WellPosed.E n) (Xsr : ℝ → NesterovODE.WellPosed.E n) : Prop :=
  Xsr 0 = x₀ ∧
  ∃ (τ : ℕ → ℝ) (Y W : ℕ → ℝ → NesterovODE.WellPosed.E n), τ 0 = 0 ∧
    ∀ i : ℕ, NesterovODE.StrongCvx.IsSolution f 3 (Xsr (τ i)) (Y i) (W i) ∧
      (gradient f (Xsr (τ i)) ≠ 0 →
        τ (i + 1) = τ i + restartTime f (Y i) (W i) ∧
        ∀ u ∈ Set.Icc 0 (τ (i + 1) - τ i), Xsr (τ i + u) = Y i u) ∧
      (gradient f (Xsr (τ i)) = 0 →
        τ (i + 1) = τ i ∧ ∀ t, τ i ≤ t → Xsr t = Xsr (τ i))

end NesterovODE.Restart


