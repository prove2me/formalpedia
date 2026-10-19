-- Prove2me | Definitions.Def_InterpOptStop_SAA_StoppingModel
-- name    : InterpOptStop_SAA_StoppingModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:26.640978+00:00
-- url     : https://prove2.me/theorems/0c8d4ff5-a370-4bbc-8c5a-90a13547a3e5
-- title:
--   §3.1–§3.2, pp. 5–6 — finite-horizon optimal stopping: first-stop reward (1)–(2), value J^π, sample-average value Ĵ^π (3)–(4)
-- statement:
--   This file sets up the finite-horizon optimal stopping problem of Ciocan and Mišić (§3.1–§3.2) for a **stationary** policy.
--
--   The state of the system is a vector $\mathbf x\in\mathbb R^n$, and the process runs for $T$ periods $t=1,\dots,T$; a path is $(\mathbf x(1),\dots,\mathbf x(T))$. The action space is $A=\{\mathbf{stop},\mathbf{go}\}$. A stationary policy is a map $\pi:\mathbb R^n\to A$. Rewards are discounted by a factor $\beta$ per period, and $g(t,\mathbf x)$ is the reward collected when the system is stopped in period $t$ in state $\mathbf x$.
--
--   1. **Stopping time and reward.** On a path, the stopping time of $\pi$ is the first period at which it prescribes $\mathbf{stop}$,
--   $$\tau_\pi=\min\{t\in[T] : \pi(\mathbf x(t))=\mathbf{stop}\},$$
--   with $\tau_\pi=+\infty$ if there is no such period. The discounted reward of the path is $\beta^{\tau_\pi-1}g(\tau_\pi,\mathbf x(\tau_\pi))$, and it is $0$ when $\tau_\pi=+\infty$.
--   2. **True value.** If the path has law $\mu$, then $J^\pi(\bar{\mathbf x})=\mathbb E_\mu\big[\beta^{\tau_\pi-1}g(\tau_\pi,\mathbf x(\tau_\pi))\big]$. The starting state $\bar{\mathbf x}$ is a property of $\mu$ ($\mathbf x(1)=\bar{\mathbf x}$ almost surely), stated as a hypothesis wherever it is used.
--   3. **Sample-average value.** Given trajectories $\mathbf x(1,\cdot),\mathbf x(2,\cdot),\dots$, the sample-average value over the first $\Omega$ of them is
--   $$\hat J^\pi(\bar{\mathbf x})=\frac1\Omega\sum_{\omega=1}^{\Omega}\beta^{\tau_{\pi,\omega}-1}g\big(\tau_{\pi,\omega},\mathbf x(\omega,\tau_{\pi,\omega})\big).$$
--
--   These are the objective (2) of the stopping problem and the objective (4) of its sample average approximation (SAA). The SAA convergence theorems of the paper compare the two.
--
--   **Formalization Note** Periods are 0-indexed: `k : Fin T` is the paper's period $t=k+1$, so $\beta^{\tau-1}$ is `β ^ k`. A path is a function `Fin T → (Fin n → ℝ)`. The stopping index is the least element of the finite set of stopping indices (`Finset.min'`), and the reward is `0` when that set is empty. `J` is the Bochner integral against `μ`. `Jhat ys m` averages over `ys 0, …, ys (m-1)`, so the paper's sample size $\Omega$ is `m`; at `m = 0` it is `0/0 = 0`. Policies take only the state as input because the tree policies of the paper are stationary (p. 8).
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, §3.1 displays (1)–(2) and J^π, pp. 5–6; §3.2 displays (3)–(4) and Ĵ^π, p. 6

import Mathlib

namespace InterpOptStop.SAA

open MeasureTheory

/-- The action space `A = {stop, go}` of the optimal stopping problem (§3.1, p. 5). -/
inductive Act
  | stop
  | go
  deriving DecidableEq, Inhabited

/-- The discounted reward of the stationary policy `π : 𝒳 → A` on one path
`x : Fin T → (Fin n → ℝ)` (time index `k : Fin T` is the paper's period `t = k + 1`).
If `π` prescribes `stop` at some period, `τ` is the first such index and the reward is
`β ^ τ * g τ (x τ)` (the paper's `β^{τ−1} g(τ, x(τ))`, displays (1)–(2) and (3)–(4));
if `π` never stops, the reward is `0` (the convention stated after (4), p. 6). -/
noncomputable def reward {n T : ℕ} (β : ℝ) (g : Fin T → (Fin n → ℝ) → ℝ)
    (π : (Fin n → ℝ) → Act) (x : Fin T → Fin n → ℝ) : ℝ :=
  if h : (Finset.univ.filter fun k : Fin T => π (x k) = Act.stop).Nonempty then
    β ^ (((Finset.univ.filter fun k : Fin T => π (x k) = Act.stop).min' h : Fin T) : ℕ) *
      g ((Finset.univ.filter fun k : Fin T => π (x k) = Act.stop).min' h)
        (x ((Finset.univ.filter fun k : Fin T => π (x k) = Act.stop).min' h))
  else 0

/-- `J^π(x̄)` (§3.1, p. 6): the expected discounted reward of `π` when the path has law `μ`
(the process is started at `x̄`, which is a hypothesis on `μ`). -/
noncomputable def J {n T : ℕ} (μ : Measure (Fin T → Fin n → ℝ)) (β : ℝ)
    (g : Fin T → (Fin n → ℝ) → ℝ) (π : (Fin n → ℝ) → Act) : ℝ :=
  ∫ x, reward β g π x ∂μ

/-- `Ĵ^π(x̄)` (§3.2, p. 6): the sample average of the discounted reward of `π` over the
first `m` trajectories `ys 0, …, ys (m - 1)` (the paper's `ω = 1, …, Ω` with `Ω = m`). -/
noncomputable def Jhat {n T : ℕ} (ys : ℕ → Fin T → Fin n → ℝ) (m : ℕ) (β : ℝ)
    (g : Fin T → (Fin n → ℝ) → ℝ) (π : (Fin n → ℝ) → Act) : ℝ :=
  (∑ k ∈ Finset.range m, reward β g π (ys k)) / m

end InterpOptStop.SAA


