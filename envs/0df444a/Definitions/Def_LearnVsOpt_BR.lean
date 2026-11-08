-- Prove2me | Definitions.Def_LearnVsOpt_BR
-- name    : LearnVsOpt_BR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:01:58.213059+00:00
-- url     : https://prove2.me/theorems/219d006f-205b-48a0-af40-907a161a0a3a
-- title:
--   The learner's budgeted best response $\mathrm{BR}_L$
-- statement:
--   For predicted utilities $u$ and costs $c$ in $\mathbb R^{n_L}$ and a budget rate $\rho_L$, the learner's best response is the set of maximizers of its linear program:
--   $$
--   \mathrm{BR}_L(u,c)=\operatorname*{argmax}_{y\in\Delta_{n_L}}\ u^\top y\quad\text{such that}\quad c^\top y\le\rho_L .
--   $$
--   For a mixed strategy $x\in\Delta_{n_O}$ of the optimizer, $\mathrm{BR}_L(x)=\mathrm{BR}_L(x^\top U_L,x^\top C_L)$.
--
--   This is the object every benchmark and every guarantee of the paper refers to.
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, (1), p.6

import Mathlib
import Definitions.Def_LearnVsOpt_Game

open scoped Matrix

namespace LearnVsOpt

variable {nO nL : ℕ}

/-- **The learner's budgeted best response** (Fikioris, Sivan & Tardos, arXiv:2611.05580, (1), p.6):
`BR_L(u, c) = argmax_{y ∈ Δ_{n_L}} u⊤y such that c⊤y ≤ ρ_L`, as a set of maximizers. -/
def BR (ρL : ℝ) (u c : Fin nL → ℝ) : Set (Fin nL → ℝ) :=
  {y | y ∈ stdSimplex ℝ (Fin nL) ∧ c ⬝ᵥ y ≤ ρL ∧
    ∀ y' ∈ stdSimplex ℝ (Fin nL), c ⬝ᵥ y' ≤ ρL → u ⬝ᵥ y' ≤ u ⬝ᵥ y}

/-- `BR_L(x) = BR_L(x⊤U_L, x⊤C_L)` (§2, p.6), the best responses to a mixed strategy `x` of the
optimizer. -/
def Game.BRx (G : Game nO nL) (ρL : ℝ) (x : Fin nO → ℝ) : Set (Fin nL → ℝ) :=
  BR ρL (x ᵥ* G.UL) (x ᵥ* G.CL)

end LearnVsOpt


