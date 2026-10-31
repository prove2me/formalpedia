-- Prove2me | Definitions.Def_MonoIncExtrap_Algorithm1
-- name    : MonoIncExtrap_Algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:32.370109+00:00
-- url     : https://prove2.me/theorems/df3aa689-2756-4d7d-875c-bb671aa8002b
-- title:
--   Algorithm 1: input, line search, runs, the sets (8)–(10), the constants (11)–(13) and the sequences (40)–(47)
-- statement:
--   Algorithm 1 takes $\epsilon>0$, $\gamma_0>0$, $\delta\in(0,1)$, $0<\nu\le1/2$, $\eta\in[0,\nu/(1+\nu))$, $x^0=x^1\in\mathrm{dom}\,B$ and the parameter $\mu$. For $t=1,2,\dots$ it computes
--   $$
--   x^{t+1}=(I+\gamma_tB)^{-1}\bigl(x^t+\alpha_t(x^t-x^{t-1})-\gamma_t(F(x^t)+\beta_t(F(x^t)-F(x^{t-1})))\bigr),
--   $$
--   where
--   $$
--   \gamma_t=\min\{\gamma_0,\delta^{-1}\gamma_{t-1}\}\delta^{n_t},\quad\beta_t=\frac{\gamma_{t-1}}{\gamma_t}\Bigl(1+\frac{2\mu\gamma_{t-1}}{1-\eta}\Bigr)^{-1},\quad\alpha_t=\frac{\eta\gamma_t\beta_t}{\gamma_{t-1}},
--   $$
--   and $n_t$ is the smallest nonnegative integer such that
--   $$
--   \|F(x^{t+1})-F(x^t)-\eta\gamma_t^{-1}(x^{t+1}-x^t)\|\le\nu(1-\eta)\gamma_t^{-1}\|x^{t+1}-x^t\|.
--   $$
--   It terminates and outputs $x^{t+1}$ when
--   $$
--   \|\gamma_t^{-1}(x^t-x^{t+1}+\alpha_t(x^t-x^{t-1}))+F(x^{t+1})-F(x^t)-\beta_t(F(x^t)-F(x^{t-1}))\|\le\epsilon.
--   $$
--
--   This module defines one step of the method, the run predicates `IsPrefix` (the first $t$ iterations) and `Stops` (termination at iteration `last`), the operation count $\sum_t(n_t+1)$, the standing assumptions of §2, the quantity $\xi=\nu(1-\eta)-\eta$, the sets $\mathcal S$ and $\widehat{\mathcal S}$, the constants $M$, $T$, $N$, and the sequences $\Delta^t$, $\tilde\Delta^t$, $v^t$, $\tilde\gamma_t$, $\theta_t$, $R_k$ of the proofs.
--
--   **Formalization Note** A run is relational: `IsPrefix I x γ n t` constrains $x_0,\dots,x_{t+1}$, $\gamma_0,\dots,\gamma_t$, $n_1,\dots,n_t$ and nothing after. Minimality of $n_t$ is part of it (`IsLeast`). `Input` holds $\mu$, which the paper's input line omits although (5) uses it. $\lceil\cdot\rceil_+$ is `Nat.ceil`, with the positive part taken after the division by $\log\delta<0$. Sequences such as $\Delta^t$ use $t-1$ in `ℕ` and are only meaningful for $t\ge1$, the paper's range. At $r_0=0$ the paper's logarithm in (12) is $-\infty$ and Lean's is $0$; both give $T=3$.
-- source:
--   Lu & Mei, Primal-dual extrapolation methods for monotone inclusions under local Lipschitz continuity, arXiv:2206.00973v3, arXiv:2206.00973v3, Algorithm 1, p.4; (8)–(13), pp.5–6; (40)–(43), (47), pp.14–15; (53), (55), pp.16–17

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_MonoIncExtrap_Setting

open InnerProductSpace ThreeOpSplitting.Convergence

namespace MonoIncExtrap

/-! # Algorithm 1: the primal-dual extrapolation method for `μ > 0`

Z. Lu and S. Mei, arXiv:2206.00973v3, Algorithm 1, p.4, with the sets (8)–(10) and constants
(11)–(13), pp.5–6, and the sequences (40)–(43), (47), pp.14–15.

**Formalization Note.** An algorithm run is relational. `Alg1.IsPrefix I x γ n t` says that
`x 0, …, x (t+1)`, `γ 0, …, γ t`, `n 1, …, n t` are what Algorithm 1 generates in its iterations
`1, …, t`; nothing is said about later indices. Iteration indices are the paper's: `x 0 = x 1` is
the initial point, `γ 0` the input, and iteration `t` produces `x (t+1)`. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **The input of Algorithm 1**: the operator `F`, a resolvent family `J` of `B`, the monotonicity
parameter `μ`, the tolerance `ε` and the parameters `γ0, δ, ν, η`, and `x⁰ = x¹ = x0`.
arXiv:2206.00973v3, Algorithm 1, p.4.

**Formalization Note.** The paper's input line does not list `μ`, but (5) uses it, and Algorithm 2
passes it. `B` enters only through `J`. -/
structure Alg1.Input (H : Type*) where
  F : H → H
  J : ℝ → H → H
  μ : ℝ
  ε : ℝ
  γ0 : ℝ
  δ : ℝ
  ν : ℝ
  η : ℝ
  x0 : H

namespace Alg1

/-- `β_t(g)` of (55), and `β_t` of (5) at `g = γ_t`, with `gp = γ_{t−1}`:
`(γ_{t−1}/g)(1 + 2μγ_{t−1}/(1 − η))⁻¹`. arXiv:2206.00973v3, (5), p.4, and (55), p.17. -/
noncomputable def Input.beta (I : Input H) (gp g : ℝ) : ℝ :=
  gp / g * (1 + 2 * I.μ * gp / (1 - I.η))⁻¹

/-- `α_t(g) = η g β_t(g)/γ_{t−1}`, with `gp = γ_{t−1}`. arXiv:2206.00973v3, (5), p.4, and (55),
p.17. -/
noncomputable def Input.alpha (I : Input H) (gp g : ℝ) : ℝ :=
  I.η * g * I.beta gp g / gp

/-- The trial step size `min{γ0, δ⁻¹γ_{t−1}} δ^m` of (5), with `gp = γ_{t−1}`.
arXiv:2206.00973v3, (5), p.4. -/
noncomputable def Input.step (I : Input H) (gp : ℝ) (m : ℕ) : ℝ :=
  min I.γ0 (I.δ⁻¹ * gp) * I.δ ^ m

/-- The point `x^{t+1}(g)` of (53), and the update (4) at `g = γ_t`, with `xp = x^{t−1}`,
`xc = x^t`, `gp = γ_{t−1}`:
`(I + gB)⁻¹(x^t + α_t(g)(x^t − x^{t−1}) − g(F(x^t) + β_t(g)(F(x^t) − F(x^{t−1}))))`.
arXiv:2206.00973v3, (4), p.4, and (53), p.16. -/
noncomputable def Input.trial (I : Input H) (xp xc : H) (gp g : ℝ) : H :=
  I.J g (xc + I.alpha gp g • (xc - xp) - g • (I.F xc + I.beta gp g • (I.F xc - I.F xp)))

/-- The line search test (6), with `xc = x^t`, `y = x^{t+1}`, `g = γ_t`:
`‖F(x^{t+1}) − F(x^t) − ηγ_t⁻¹(x^{t+1} − x^t)‖ ≤ ν(1 − η)γ_t⁻¹‖x^{t+1} − x^t‖`.
arXiv:2206.00973v3, (6), p.4. -/
def Input.LineSearch (I : Input H) (xc y : H) (g : ℝ) : Prop :=
  ‖I.F y - I.F xc - (I.η * g⁻¹) • (y - xc)‖ ≤ I.ν * (1 - I.η) * g⁻¹ * ‖y - xc‖

/-- The integer `m` passes the line search of iteration `t`: test (6) holds at the trial step size
`min{γ0, δ⁻¹γ_{t−1}} δ^m` and the point it produces. arXiv:2206.00973v3, Algorithm 1, step 2,
p.4. -/
def Input.Accepts (I : Input H) (xp xc : H) (gp : ℝ) (m : ℕ) : Prop :=
  I.LineSearch xc (I.trial xp xc gp (I.step gp m)) (I.step gp m)

/-- The vector in the termination test (7), with `xp = x^{t−1}`, `xc = x^t`, `y = x^{t+1}`,
`gp = γ_{t−1}`, `g = γ_t`:
`γ_t⁻¹(x^t − x^{t+1} + α_t(x^t − x^{t−1})) + F(x^{t+1}) − F(x^t) − β_t(F(x^t) − F(x^{t−1}))`.
arXiv:2206.00973v3, (7), p.4. -/
noncomputable def Input.stopVec (I : Input H) (xp xc y : H) (gp g : ℝ) : H :=
  g⁻¹ • (xc - y + I.alpha gp g • (xc - xp)) + I.F y - I.F xc
    - I.beta gp g • (I.F xc - I.F xp)

/-- The termination test (7). arXiv:2206.00973v3, (7), p.4. -/
def Input.StopTest (I : Input H) (xp xc y : H) (gp g : ℝ) : Prop :=
  ‖I.stopVec xp xc y gp g‖ ≤ I.ε

/-- **The first `t` iterations of Algorithm 1.** arXiv:2206.00973v3, Algorithm 1, p.4.
Initialization `x⁰ = x¹ = x0`, `γ_0 = γ0`; for each iteration `s + 1 ≤ t`, `n (s+1)` is the
smallest nonnegative integer passing the line search, `γ (s+1)` is given by (5), and `x (s+2)` by
(4); and the termination test (7) failed at every iteration before `t`.

**Formalization Note.** Iteration `s + 1` is indexed from `s` to avoid natural-number subtraction;
`IsPrefix I x γ n 0` is the initialization alone. -/
structure IsPrefix (I : Input H) (x : ℕ → H) (γ : ℕ → ℝ) (n : ℕ → ℕ) (t : ℕ) : Prop where
  x_zero : x 0 = I.x0
  x_one : x 1 = I.x0
  γ_zero : γ 0 = I.γ0
  least : ∀ s < t, IsLeast {m | I.Accepts (x s) (x (s + 1)) (γ s) m} (n (s + 1))
  γ_succ : ∀ s < t, γ (s + 1) = I.step (γ s) (n (s + 1))
  x_succ : ∀ s < t, x (s + 2) = I.trial (x s) (x (s + 1)) (γ s) (γ (s + 1))
  no_stop : ∀ s, s + 1 < t → ¬ I.StopTest (x s) (x (s + 1)) (x (s + 2)) (γ s) (γ (s + 1))

/-- The termination test (7) holds at iteration `t`, for `t ≥ 1`. -/
def StoppedAt (I : Input H) (x : ℕ → H) (γ : ℕ → ℝ) (t : ℕ) : Prop :=
  I.StopTest (x (t - 1)) (x t) (x (t + 1)) (γ (t - 1)) (γ t)

/-- **A terminated run of Algorithm 1**: the method performs iterations `1, …, last` and stops at
iteration `last ≥ 1`, with output `x (last + 1)`. arXiv:2206.00973v3, Algorithm 1, step 3, p.4. -/
def Stops (I : Input H) (x : ℕ → H) (γ : ℕ → ℝ) (n : ℕ → ℕ) (last : ℕ) : Prop :=
  1 ≤ last ∧ IsPrefix I x γ n last ∧ StoppedAt I x γ last

/-- **Operation count of a run.** Iterations `1, …, last` perform `Σ_{t=1}^{last} (n_t + 1)`
evaluations of `F` and of the resolvent of `B`. arXiv:2206.00973v3, Remark 1(iii), p.5, and the
proof of Theorem 2, p.19. -/
def opCount (n : ℕ → ℕ) (last : ℕ) : ℕ :=
  ∑ t ∈ Finset.Icc 1 last, (n t + 1)

/-- **The standing assumptions of §2.** arXiv:2206.00973v3, Algorithm 1 input line, p.4, and §2,
p.5: the parameter ranges of Algorithm 1, `x⁰ ∈ dom B`, Assumption 1 with `μ > 0`, `J` a resolvent
family of `B`, and `xstar` a solution of (1). -/
structure Standing (B : H → Set H) (I : Input H) (xstar : H) : Prop where
  ε_pos : 0 < I.ε
  γ0_pos : 0 < I.γ0
  δ_pos : 0 < I.δ
  δ_lt_one : I.δ < 1
  ν_pos : 0 < I.ν
  ν_le : I.ν ≤ 1 / 2
  η_nonneg : 0 ≤ I.η
  η_lt : I.η < I.ν / (1 + I.ν)
  x0_mem : I.x0 ∈ dom B
  μ_pos : 0 < I.μ
  assumption : Assumption1 I.F B I.μ
  resolvent : IsResolventFamily I.J B
  solution : IsSolution I.F B xstar

/-- `ξ = ν(1 − η) − η`. arXiv:2206.00973v3, (9), p.5. -/
def xi (ν η : ℝ) : ℝ := ν * (1 - η) - η

/-- `min{L⁻¹δξ, γ0}`, the lower bound on step sizes in (12), (18), (19), (75) of
arXiv:2206.00973v3. -/
noncomputable def minStep (L δ ξ γ0 : ℝ) : ℝ := min (L⁻¹ * δ * ξ) γ0

/-- The ceiling `⌈log(ξ/(γ0 L))/log δ⌉₊` of (11), (13), (19), (75) of arXiv:2206.00973v3.

**Formalization Note.** The paper's `⌈ω⌉₊` is `(⌈ω⌉)₊`, which is `Nat.ceil ω`. The positive part is
applied after the division: `log δ < 0`, and the quotient may have either sign. -/
noncomputable def ceilLog (L δ ξ γ0 : ℝ) : ℕ :=
  ⌈Real.log (ξ / (γ0 * L)) / Real.log δ⌉₊

/-- `S = {x ∈ dom B : ‖x − c‖ ≤ r/√(1 − 2ν²)}`. arXiv:2206.00973v3, (8), p.5, with `c = x∗`,
`r = r0`, and (73), p.21, with `c = z∗ᵏ`, `r = ‖zᵏ − z∗ᵏ‖`. -/
noncomputable def setS (B : H → Set H) (c : H) (r ν : ℝ) : Set H :=
  ballIn B c (r / Real.sqrt (1 - 2 * ν ^ 2))

/-- `Ŝ = {x ∈ dom B : ‖x − c‖ ≤ (5 + 9γ0 L) r/(3√(1 − 2ν²))}`. arXiv:2206.00973v3, (10), p.5, with
`c = x∗`, `r = r0`, `L = L_S`, and (74), p.21, with `c = z∗ᵏ`, `r = ‖zᵏ − z∗ᵏ‖`, `L = L_Q`. -/
noncomputable def setShat (B : H → Set H) (c : H) (r ν γ0 L : ℝ) : Set H :=
  ballIn B c ((5 + 9 * γ0 * L) * r / (3 * Real.sqrt (1 - 2 * ν ^ 2)))

/-- `r0 = ‖x⁰ − x∗‖`. arXiv:2206.00973v3, (8), p.5. -/
noncomputable def Input.r0 (I : Input H) (xstar : H) : ℝ := ‖I.x0 - xstar‖

/-- **Valid Lipschitz constants of Lemma 1**: `L_S, L_Ŝ > 0`, `F` is `L_S`-Lipschitz on `S`, and
`F` is `L_Ŝ`-Lipschitz on the set `Ŝ` built from `L_S`. arXiv:2206.00973v3, Lemma 1, p.5.

**Formalization Note.** `Ŝ` depends on `L_S`, so the two constants are a dependent pair. -/
def ValidS (B : H → Set H) (I : Input H) (xstar : H) (LS LShat : ℝ) : Prop :=
  0 < LS ∧ 0 < LShat ∧ IsLipschitzOn I.F (setS B xstar (I.r0 xstar) I.ν) LS ∧
    IsLipschitzOn I.F (setShat B xstar (I.r0 xstar) I.ν I.γ0 LS) LShat

/-- `M = ⌈log(ξ/(γ0 L_Ŝ))/log δ⌉₊`. arXiv:2206.00973v3, (11), p.5. -/
noncomputable def Input.Mconst (I : Input H) (LShat : ℝ) : ℕ :=
  ceilLog LShat I.δ (xi I.ν I.η) I.γ0

/-- `T = 3 + ⌈2 log(r0(8 + 12γ0 L_S)/(3ε√(1 − 2ν²) min{L_Ŝ⁻¹δξ, γ0}))
/ log(1 + (2μ/(1 − η)) min{L_Ŝ⁻¹δξ, γ0})⌉₊`. arXiv:2206.00973v3, (12), p.6.

**Formalization Note.** The `3` is outside the ceiling. At `r0 = 0` the paper's logarithm is `−∞`
and Lean's `Real.log 0 = 0`; both give `⌈·⌉₊ = 0`, so `T = 3` in both. -/
noncomputable def Input.Tconst (I : Input H) (r0 LS LShat : ℝ) : ℕ :=
  3 + ⌈2 * Real.log (r0 * (8 + 12 * I.γ0 * LS) /
        (3 * I.ε * Real.sqrt (1 - 2 * I.ν ^ 2) * minStep LShat I.δ (xi I.ν I.η) I.γ0)) /
      Real.log (1 + 2 * I.μ / (1 - I.η) * minStep LShat I.δ (xi I.ν I.η) I.γ0)⌉₊

/-- `N = 2T + ⌈log(ξ/(γ0 L_Ŝ))/log δ⌉₊`. arXiv:2206.00973v3, (13), p.6. -/
noncomputable def Input.Nconst (I : Input H) (r0 LS LShat : ℝ) : ℕ :=
  2 * I.Tconst r0 LS LShat + ceilLog LShat I.δ (xi I.ν I.η) I.γ0

/-- `Δ^t = F(x^t) − F(x^{t−1})`, for `t ≥ 1`. arXiv:2206.00973v3, (40), p.14. -/
def Delta (I : Input H) (x : ℕ → H) (t : ℕ) : H := I.F (x t) - I.F (x (t - 1))

/-- `Δ̃^t = Δ^t − ηγ_{t−1}⁻¹(x^t − x^{t−1})`, for `t ≥ 1`. arXiv:2206.00973v3, (41), p.14. -/
noncomputable def DeltaTilde (I : Input H) (x : ℕ → H) (γ : ℕ → ℝ) (t : ℕ) : H :=
  Delta I x t - (I.η * (γ (t - 1))⁻¹) • (x t - x (t - 1))

/-- `β_t` as a sequence, for `t ≥ 1`. arXiv:2206.00973v3, (5), p.4. -/
noncomputable def betaSeq (I : Input H) (γ : ℕ → ℝ) (t : ℕ) : ℝ := I.beta (γ (t - 1)) (γ t)

/-- `α_t` as a sequence, for `t ≥ 1`. arXiv:2206.00973v3, (5), p.4. -/
noncomputable def alphaSeq (I : Input H) (γ : ℕ → ℝ) (t : ℕ) : ℝ := I.alpha (γ (t - 1)) (γ t)

/-- `v^t = γ_t⁻¹(x^t − x^{t+1} + α_t(x^t − x^{t−1}) + γ_tΔ^{t+1} − γ_tβ_tΔ^t)`, for `t ≥ 1`.
arXiv:2206.00973v3, (42), p.14. -/
noncomputable def vSeq (I : Input H) (x : ℕ → H) (γ : ℕ → ℝ) (t : ℕ) : H :=
  (γ t)⁻¹ • (x t - x (t + 1) + alphaSeq I γ t • (x t - x (t - 1)) + γ t • Delta I x (t + 1)
    - (γ t * betaSeq I γ t) • Delta I x t)

/-- `γ̃_t = γ_t/(1 − η)`. arXiv:2206.00973v3, (43), p.14. -/
noncomputable def gammaTilde (I : Input H) (γ : ℕ → ℝ) (t : ℕ) : ℝ := γ t / (1 - I.η)

/-- `θ_t = ∏_{i=1}^{t−1}(1 + 2μγ_i/(1 − η))`, for `t ≥ 1`, with `θ_1 = 1` the empty product.
arXiv:2206.00973v3, (43) and footnote 10, p.14. -/
noncomputable def theta (I : Input H) (γ : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 (t - 1), (1 + 2 * I.μ * γ i / (1 - I.η))

/-- `R_k = Σ_{t=1}^k (γ̃_tβ_tθ_t⟨Δ̃^t, x^{t+1} − x^t⟩ + ½θ_t‖x^{t+1} − x^t‖²)`.
arXiv:2206.00973v3, (47), p.15. -/
noncomputable def Rk (I : Input H) (x : ℕ → H) (γ : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 k,
    (gammaTilde I γ t * betaSeq I γ t * theta I γ t * ⟪DeltaTilde I x γ t, x (t + 1) - x t⟫_ℝ
      + 1 / 2 * theta I γ t * ‖x (t + 1) - x t‖ ^ 2)

end Alg1

end MonoIncExtrap


