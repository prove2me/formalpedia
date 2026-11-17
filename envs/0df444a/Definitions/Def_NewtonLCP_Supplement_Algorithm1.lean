-- Prove2me | Definitions.Def_NewtonLCP_Supplement_Algorithm1
-- name    : NewtonLCP_Supplement_Algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:15:17.52602+00:00
-- url     : https://prove2.me/theorems/0522aa88-a553-43ab-9bda-ed22c1dec35a
-- title:
--   Algorithm 1 — Newton's method for LCP path following, with a solve counter
-- statement:
--   Let $M\in\mathbb R^{n\times n}$, a step size $\delta$, an initial point $(x^0,s^0,\mu^0)$ and an accuracy target $\mu_1>0$ be given. **Algorithm 1** sets $(x,s,\mu)\leftarrow(x^0,s^0,\mu^0)$ and, while $\mu>\mu_1$, performs
--
--   1. $\mu\leftarrow \mu/(1+\delta)$;
--   2. compute the Newton step $(\Delta x,\Delta s)$ of (10) at the current $(x,s)$ for the **new** value of $\mu$:
--   $$\frac{\Delta x}{x}=H_{x,\mu}\,\mathrm{err}(x,s,\mu),\qquad \Delta s=M\Delta x,\qquad H_{x,\mu}=\Big(I_n+\tfrac1\mu XMX\Big)^{-1};$$
--   3. $(x,s)\leftarrow(x+\Delta x,s+\Delta s)$.
--
--   It then returns $(x_{\mathrm{out}},s_{\mathrm{out}},\mu_{\mathrm{out}})=(x,s,\mu)$. The algorithm performs no feasibility or neighbourhood tests. Each iteration solves one linear system, and the definition also returns the number of iterations, i.e. the number of linear-system solves.
--
--   Algorithm 1 is the path-following method analysed in Theorems 4.2 and 5.1.
--
--   **Formalization Note** The Newton step is the published one of `NewtonLCP.NewtonStep`. The `while` loop is a recursion on the published fuel $\lceil\log(\mu^0/\mu_1)/\log(1+\delta)\rceil_+ +1$, which is never exhausted when $\mu^0,\mu_1,\delta>0$; an exhausted fuel would return the current state, with $\mu$ still above $\mu_1$. The input requirements of the pseudocode ($M\in P_\star$, $\beta,\delta\in(0,1/2)$, a start in $N^2(\beta)$) are hypotheses of the theorems.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Algorithm 1, p.12; display (10), p.13

import Mathlib
import Definitions.Def_NewtonLCP_NewtonStep
import Definitions.Def_NewtonLCP_FixedKappaNewton

open Matrix

namespace NewtonLCP.Supplement

/-!
# Algorithm 1 (Newton's method for LCP path following), with a solve counter

Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8),
Algorithm 1, p.12 (with the Newton step (10), p.13).

From `(x, s, µ) = (x⁰, s⁰, µ⁰)`: while `µ > µ₁`, set `µ ← µ/(1+δ)` (line 3), compute the Newton
step `(∆x, ∆s)` of (10) at the current `(x, s)` for the **new** `µ` (line 4) and set
`(x, s) ← (x + ∆x, s + ∆s)` (line 5). Return `(x, s, µ)` (line 6). The algorithm performs no
feasibility or neighbourhood tests.

**Formalization Note.**
* The Newton step is the published `newtonDx`/`newtonDs` of `NewtonLCP.NewtonStep`
  (`∆x = x ∘ H_{x,µ} err(x, s, µ)`, `∆s = M∆x`, with Mathlib's junk inverse `0` for a singular
  matrix; for `M ∈ P⋆`, `x > 0`, `µ > 0` the matrix is nonsingular by Corollary 2.5).
* The fourth component of the result counts linear-system solves: one per execution of line 4,
  i.e. one per loop iteration. The algorithm never reads the counter.
* The `while` loop is a recursion on the published fuel `fkFuel µ⁰ µ₁ δ =
  ⌈log(µ⁰/µ₁)/log(1+δ)⌉₊ + 1`. For `µ⁰, µ₁ > 0` and `δ > 0`, after `k` iterations
  `µ = µ⁰/(1+δ)ᵏ`, so the loop condition fails before the fuel runs out and the fuel changes
  nothing. An exhausted fuel returns the current state (its `µ` is then still `> µ₁`).
* The input requirements of the pseudocode (`M ∈ P⋆`, `β, δ ∈ (0, 1/2)`, a start in `N²(β)`) are
  hypotheses of the theorems, not tests of the algorithm; `β` is not used by the algorithm.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Classical in
/-- The `while` loop of Algorithm 1 (lines 2–5), run with `fuel` rounds from `(x, s, µ)`; `c` is
the number of Newton solves so far. Returns `(x, s, µ, solves)`. -/
noncomputable def alg1Loop (M : Matrix ι ι ℝ) (mu1 δ : ℝ) :
    ℕ → (ι → ℝ) → (ι → ℝ) → ℝ → ℕ → (ι → ℝ) × (ι → ℝ) × ℝ × ℕ
  | 0, x, s, mu, c => (x, s, mu, c)
  | fuel + 1, x, s, mu, c =>
    if mu1 < mu then
      alg1Loop M mu1 δ fuel (x + newtonDx M x s (mu / (1 + δ)))
        (s + newtonDs M x s (mu / (1 + δ))) (mu / (1 + δ)) (c + 1)
    else (x, s, mu, c)

/-- Algorithm 1 on input `M`, step size `δ`, initial point `(x⁰, s⁰, µ⁰)` and accuracy target
`µ₁`: the returned `(x_out, s_out, µ_out)` and the number of linear-system solves. -/
noncomputable def algorithm1 (M : Matrix ι ι ℝ) (δ : ℝ) (x0 s0 : ι → ℝ) (mu0 mu1 : ℝ) :
    (ι → ℝ) × (ι → ℝ) × ℝ × ℕ :=
  alg1Loop M mu1 δ (fkFuel mu0 mu1 δ) x0 s0 mu0 0

end NewtonLCP.Supplement


