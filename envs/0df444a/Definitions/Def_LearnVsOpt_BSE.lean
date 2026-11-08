-- Prove2me | Definitions.Def_LearnVsOpt_BSE
-- name    : LearnVsOpt_BSE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:02:47.753198+00:00
-- url     : https://prove2.me/theorems/66512f09-449e-4a45-8bab-8045f76b859e
-- title:
--   Budgeted Stackelberg values: (2), the two-phase (26), and the Lagrangian (27)
-- statement:
--   Three values of a game for the optimizer. With $y\in\mathrm{BR}_L(x)$ the learner's best response:
--
--   1. The **Budgeted Stackelberg value** of an unbudgeted optimizer,
--   $$
--   \mathrm{BSE}=\max_{x\in\Delta_{n_O},\,y\in\Delta_{n_L}} x^\top U_O y\quad\text{such that } y\in\mathrm{BR}_L(x).
--   $$
--   2. The two-phase value of an optimizer with budget rate $\rho_O$, which the paper also calls BSE and which is written $\mathrm{BSE}_2$ here,
--   $$
--   \mathrm{BSE}_2=\max_{x_1,x_2,y_1,y_2,\,q\in[0,1]} q\,x_1^\top U_O y_1+(1-q)\,x_2^\top U_O y_2
--   $$
--   such that $q\,x_1^\top C_O y_1+(1-q)\,x_2^\top C_O y_2\le\rho_O$, $y_1\in\mathrm{BR}_L(x_1)$ and $y_2\in\mathrm{BR}_L(x_2)$.
--   3. The value of the Lagrangian relaxation at multiplier $\mu$,
--   $$
--   \mathrm{BSE}_\mu=\max_{x,y} x^\top U_O y-\mu\,x^\top C_O y+\mu\rho_O\quad\text{such that } y\in\mathrm{BR}_L(x).
--   $$
--
--   These are the benchmarks of the non-manipulability guarantees.
--
--   **Formalization Note** Each is the `sSup` of its set of values. Under the null actions each set is nonempty and bounded above, so the `sSup` is a genuine supremum.
-- source:
--   Fikioris, Sivan & Tardos, Learning vs. Optimizing Players in Budgeted Games, arXiv:2611.05580, (2), p.6; (26), p.22; (27), p.23

import Mathlib
import Definitions.Def_LearnVsOpt_BR

open scoped Matrix

namespace LearnVsOpt

variable {nO nL : ℕ}

/-- **Budgeted Stackelberg value of an unbudgeted optimizer** (Fikioris, Sivan & Tardos,
arXiv:2611.05580, (2), p.6): `BSE = max x⊤U_O y` over `x ∈ Δ_{n_O}`, `y ∈ Δ_{n_L}` with
`y ∈ BR_L(x⊤U_L, x⊤C_L)`.

**Formalization Note.** Written as `sSup` of the set of values. Under the learner's null action the
set is nonempty and lies in `[0, 1]`. -/
noncomputable def Game.BSE (G : Game nO nL) (ρL : ℝ) : ℝ :=
  sSup {v | ∃ x ∈ stdSimplex ℝ (Fin nO), ∃ y ∈ G.BRx ρL x, v = x ⬝ᵥ (G.UO *ᵥ y)}

/-- **Budgeted Stackelberg value of a budgeted optimizer** (arXiv:2611.05580, (26), p.22): the
two-phase value `max q·x₁⊤U_O y₁ + (1 − q)·x₂⊤U_O y₂` over `x₁, x₂ ∈ Δ_{n_O}`, `y₁, y₂ ∈ Δ_{n_L}`,
`q ∈ [0, 1]`, such that `q·x₁⊤C_O y₁ + (1 − q)·x₂⊤C_O y₂ ≤ ρ_O`, `y₁ ∈ BR_L(x₁)`, `y₂ ∈ BR_L(x₂)`.
The paper calls this value `BSE` too; here it is `BSE₂`.

**Formalization Note.** Written as `sSup` of the set of values. -/
noncomputable def Game.BSE₂ (G : Game nO nL) (ρL ρO : ℝ) : ℝ :=
  sSup {v | ∃ x₁ ∈ stdSimplex ℝ (Fin nO), ∃ x₂ ∈ stdSimplex ℝ (Fin nO),
    ∃ y₁ ∈ G.BRx ρL x₁, ∃ y₂ ∈ G.BRx ρL x₂, ∃ q ∈ Set.Icc (0 : ℝ) 1,
      q * (x₁ ⬝ᵥ (G.CO *ᵥ y₁)) + (1 - q) * (x₂ ⬝ᵥ (G.CO *ᵥ y₂)) ≤ ρO ∧
      v = q * (x₁ ⬝ᵥ (G.UO *ᵥ y₁)) + (1 - q) * (x₂ ⬝ᵥ (G.UO *ᵥ y₂))}

/-- **The Lagrangian value** (arXiv:2611.05580, (27), p.23): `BSE_μ = max x⊤U_O y − μ x⊤C_O y + μρ_O`
over `x ∈ Δ_{n_O}`, `y ∈ Δ_{n_L}` with `y ∈ BR_L(x)`.

**Formalization Note.** Written as `sSup` of the set of values. -/
noncomputable def Game.BSEmu (G : Game nO nL) (ρL ρO μ : ℝ) : ℝ :=
  sSup {v | ∃ x ∈ stdSimplex ℝ (Fin nO), ∃ y ∈ G.BRx ρL x,
    v = x ⬝ᵥ (G.UO *ᵥ y) - μ * (x ⬝ᵥ (G.CO *ᵥ y)) + μ * ρO}

end LearnVsOpt


