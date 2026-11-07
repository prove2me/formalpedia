-- Prove2me | Definitions.Def_PNormReg_Refinement
-- name    : PNormReg_Refinement
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:40:10.648508+00:00
-- url     : https://prove2.me/theorems/5199c0d6-a790-4fd0-a20d-c5262812e97c
-- title:
--   Algorithm 2: iterative refinement, as a relation over solver outputs
-- statement:
--   Algorithm 2 keeps a point $x$ and a gap bound $\nu$, starting from a feasible $x^{(0)}$ and $\nu_0\ge f(x^{(0)})-f^\star$. Its iteration cap is
--
--   $$T=(\lceil32p\kappa\rceil+1)(1+\lceil\log_2\max\{1,\nu_0/\epsilon\}\rceil).$$
--
--   At each iteration, if $\nu\le\epsilon$ it returns $x$. Otherwise a residual solver returns a direction $\Delta$. If $\mathrm{res}_p(\Delta)\ge\nu/(32p\kappa)$ then $x\leftarrow x-\Delta/p$, and otherwise $\nu\leftarrow\nu/2$. After $T$ iterations it returns $x$.
--
--   A residual call at $(x,\nu)$ is successful if $C\Delta=0$ and $\mathrm{res}_p(\Delta)\ge\mathrm{res}^\star_p/\kappa$ whenever $f(x)-f^\star>\nu/2$, which is (15).
--
--   **Formalization Note** The solver is not a program here. The directions are a free sequence, so a statement about the run covers every solver. A call happens at iteration $t<T$ exactly when $\epsilon<\nu_t$; once $\nu\le\epsilon$ the state stays, so the point after $T$ iterations is the returned one in both return lines.
-- source:
--   Adil, Bullins, O'Carroll, Sidford, Solving p-norm regression in matrix multiplication time, STOC 2027 submission (manuscript sha256 e335b2fa…), Algorithm 2, p.18; (15), p.19

import Mathlib
import Definitions.Def_PNormReg_Regression

open Matrix

namespace PNormReg

/-!
# Algorithm 2: iterative refinement, as a relation over solver outputs

Adil, Bullins, O'Carroll, Sidford, *Solving p-norm regression in matrix multiplication time*,
STOC 2027 submission (manuscript sha256 e335b2fa…), Algorithm 2, p.18, and (15), p.19.

**Formalization Note.** The residual solver is not a program here: the sequence `dirs` lists the
directions it returned, and each one is free. `refineState` is the loop's state after `t` iterations:
once `ν ≤ ϵ` the algorithm has returned and the state stays. The returned point is the `x` at `t = T`,
for both `return` lines. A residual call happens at `t < T` exactly when `ϵ < ν`. `res_p` is taken at
the current `x`.
-/

variable {n d m : ℕ}

/-- The pair `(x, ν)` maintained by Algorithm 2. -/
structure RefineState (d : ℕ) where
  x : Fin d → ℝ
  nu : ℝ

/-- The iteration cap of line 1: `T = (⌈32pκ⌉ + 1)(1 + ⌈log₂ max{1, ν₀/ϵ}⌉)`. -/
noncomputable def refineCap (p κ ν₀ ε : ℝ) : ℕ :=
  (⌈32 * p * κ⌉₊ + 1) * (1 + ⌈Real.logb 2 (max 1 (ν₀ / ε))⌉₊)

/-- Lines 6–8: accept `∆` if `res_p(∆) ≥ ν/(32pκ)`, and otherwise halve `ν`. -/
noncomputable def refineStep (G : GenRegression n d m) (p κ : ℝ) (Δ : Fin d → ℝ)
    (s : RefineState d) : RefineState d :=
  if s.nu / (32 * p * κ) ≤ G.res p s.x Δ then ⟨s.x - (1 / p) • Δ, s.nu⟩ else ⟨s.x, s.nu / 2⟩

/-- The state after `t` iterations of Algorithm 2 with solver outputs `dirs`. -/
noncomputable def refineState (G : GenRegression n d m) (p κ ε : ℝ) (x₀ : Fin d → ℝ) (ν₀ : ℝ)
    (dirs : ℕ → Fin d → ℝ) : ℕ → RefineState d
  | 0 => ⟨x₀, ν₀⟩
  | t + 1 =>
      if (refineState G p κ ε x₀ ν₀ dirs t).nu ≤ ε then refineState G p κ ε x₀ ν₀ dirs t
      else refineStep G p κ (dirs t) (refineState G p κ ε x₀ ν₀ dirs t)

/-- The number of residual calls among the first `T` iterations. -/
noncomputable def callCount (G : GenRegression n d m) (p κ ε : ℝ) (x₀ : Fin d → ℝ) (ν₀ : ℝ)
    (dirs : ℕ → Fin d → ℝ) (T : ℕ) : ℕ :=
  ((Finset.range T).filter fun t => ε < (refineState G p κ ε x₀ ν₀ dirs t).nu).card

/-- A successful residual call at `(x, ν)` (p.19): `C∆ = 0`, and (15), that is,
`res_p(∆) ≥ res⋆_p/κ` whenever `f(x) − f⋆ > ν/2`. -/
def CallSucceeds (G : GenRegression n d m) (p κ : ℝ) (x : Fin d → ℝ) (ν : ℝ) (Δ : Fin d → ℝ) :
    Prop :=
  G.C *ᵥ Δ = 0 ∧ (ν / 2 < G.obj p x - G.fStar p → G.resStar p x / κ ≤ G.res p x Δ)

end PNormReg


