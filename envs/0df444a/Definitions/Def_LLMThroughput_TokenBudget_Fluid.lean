-- Prove2me | Definitions.Def_LLMThroughput_TokenBudget_Fluid
-- name    : LLMThroughput_TokenBudget_Fluid
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:49.517157+00:00
-- url     : https://prove2.me/theorems/fc790908-5d51-410a-a2d6-26cf8c0c52ff
-- title:
--   The LLM fluid model (45)–(49), regular points (Definition 12) and work-conserving fluid model solutions (52), Definition 13 (pp. 39–40)
-- statement:
--   This file defines the fluid model of the LLM server (App. B.2). A candidate solution consists of eight real functions of time $t$:
--
--   - $B_f$, the cumulative phase-$f$ tokens processed;
--   - $F_f$, the cumulative requests that completed phase $f$;
--   - $W_f$, the phase-$f$ workload;
--   - $Z_f$, the number of requests in phase $f$;
--
--   for the two phases $f\in\{p,d\}$ (prefill and decode).
--
--   Fix an arrival rate $\lambda$, mean sizes $m_p, m_d$ and a maximal token rate $\kappa$ (in the paper $\kappa=b_{\max}/t_{b_{\max}}$). The functions form a **fluid model solution** if for all $t\ge 0$:
--   $$
--   \begin{aligned}
--   Z_p(t) &= Z_p(0)+\lambda t-F_p(t), \qquad Z_d(t)=Z_d(0)+F_p(t)-F_d(t),\\
--   B_f(0)&=0,\qquad 0\le B_f(t)-B_f(s)\le (t-s)\kappa\quad (0\le s\le t),\\
--   F_f(t)&=\frac{1}{m_f}B_f(t),\qquad W_f(t)=m_f Z_f(t),
--   \end{aligned}
--   $$
--   for $f\in\{p,d\}$ (eqs. (45)–(49)). A time $t>0$ is **regular** if all eight functions are differentiable at $t$ (Definition 12). A **work-conserving fluid model solution** also satisfies eq. (52): for every regular $t>0$,
--   $$
--   W_p(t)+W_d(t)>0 \implies \dot B_p(t)+\dot B_d(t)=\kappa .
--   $$
--
--   These are the objects of Proposition 15 (stability of the fluid model).
--
--   **Formalization Note** The functions are defined on all of $\mathbb R$, and the equations are imposed on $[0,\infty)$ only. In eq. (48) the printed $B_f(f)$ is read as $B_f(t)$. The derivative in eq. (52) is Lean's `deriv`, which is the true derivative at a regular point.
-- source:
--   Dai, Deng, Li & Peng, Throughput-Optimal Scheduling Algorithms for LLM Inference and AI Agents, arXiv:2504.07347v3, pp. 39–40, App. B.2, eqs. (45)–(50), (52), Definitions 12–13

import Mathlib

namespace LLMThroughput.TokenBudget

/-- The eight functions (50) of a candidate fluid model solution, p. 39:
`B_f, F_f, W_f, Z_f` for the phases `f ∈ {p, d}`. -/
structure FluidPath where
  Bp : ℝ → ℝ
  Bd : ℝ → ℝ
  Fp : ℝ → ℝ
  Fd : ℝ → ℝ
  Wp : ℝ → ℝ
  Wd : ℝ → ℝ
  Zp : ℝ → ℝ
  Zd : ℝ → ℝ

/-- Fluid model equations (45)–(49), p. 39, on `t ∈ ℝ₊ = [0, ∞)`, with arrival rate `lam`, mean
sizes `mp, md`, and maximal token rate `κ` (= `b_max/t_{b_max}`). In (48), `B_f(f)` is read as
`B_f(t)`. -/
def IsFluidSolution (lam mp md κ : ℝ) (s : FluidPath) : Prop :=
  (∀ t, 0 ≤ t → s.Zp t = s.Zp 0 + lam * t - s.Fp t) ∧                          -- (45)
  (∀ t, 0 ≤ t → s.Zd t = s.Zd 0 + s.Fp t - s.Fd t) ∧                            -- (46)
  s.Bp 0 = 0 ∧ s.Bd 0 = 0 ∧                                                     -- (47)
  (∀ u t, 0 ≤ u → u ≤ t → 0 ≤ s.Bp t - s.Bp u ∧ s.Bp t - s.Bp u ≤ (t - u) * κ) ∧
  (∀ u t, 0 ≤ u → u ≤ t → 0 ≤ s.Bd t - s.Bd u ∧ s.Bd t - s.Bd u ≤ (t - u) * κ) ∧
  (∀ t, 0 ≤ t → s.Fp t = s.Bp t / mp ∧ s.Fd t = s.Bd t / md) ∧                  -- (48)
  (∀ t, 0 ≤ t → s.Wp t = mp * s.Zp t ∧ s.Wd t = md * s.Zd t)                     -- (49)

/-- Definition 12, p. 39: `t > 0` is a regular point if every component of (50) is
differentiable at `t`. -/
def IsRegular (s : FluidPath) (t : ℝ) : Prop :=
  0 < t ∧ DifferentiableAt ℝ s.Bp t ∧ DifferentiableAt ℝ s.Bd t ∧ DifferentiableAt ℝ s.Fp t ∧
    DifferentiableAt ℝ s.Fd t ∧ DifferentiableAt ℝ s.Wp t ∧ DifferentiableAt ℝ s.Wd t ∧
    DifferentiableAt ℝ s.Zp t ∧ DifferentiableAt ℝ s.Zd t

/-- Definition 13, p. 40: a work-conserving fluid model solution satisfies (45)–(49) and (52):
at every regular `t > 0`, `W_p(t) + W_d(t) > 0` implies `Ḃ_p(t) + Ḃ_d(t) = κ`. -/
def IsWCFluidSolution (lam mp md κ : ℝ) (s : FluidPath) : Prop :=
  IsFluidSolution lam mp md κ s ∧
  ∀ t, IsRegular s t → 0 < s.Wp t + s.Wd t → deriv s.Bp t + deriv s.Bd t = κ

end LLMThroughput.TokenBudget


