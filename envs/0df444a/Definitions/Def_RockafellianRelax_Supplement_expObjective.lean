-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_expObjective
-- name    : RockafellianRelax_Supplement_expObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:11:14.046854+00:00
-- url     : https://prove2.me/theorems/a7a04d53-d564-4f0b-a7f6-20a5c6591d16
-- title:
--   Objective of the finite expectation problem (2.1)
-- statement:
--   Let $f_0, f_1, \dots, f_s : \mathbb R^n \to \overline{\mathbb R}$ and $q \in \mathbb R^s$. The **expectation objective** is
--
--   $$
--   x \mapsto f_0(x) + \sum_{i=1}^s q_i f_i(x),
--   $$
--
--   with the convention $0\cdot\infty = 0$. With $q = p \in \Delta = \{q \in [0,\infty)^s \mid \sum_i q_i = 1\}$ it is the objective $\varphi$ of the actual problem (2.1).
--
--   Every objective, Rockafellian and approximating function of §4 is built from it.
--
--   **Formalization Note** The sum is computed in `EReal`. It is used only with $q \ge 0$ and no value $f_i(x) = -\infty$, so no $\infty - \infty$ occurs. The scenarios are `Fin s`, and $f_0$ is a separate argument.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, display (2.1), p.5

import Mathlib

namespace RockafellianRelax.Supplement

/-- **Objective of the finite expectation problem (2.1)**, `f₀(x) + ∑ᵢ qᵢ fᵢ(x)`.
Royset, Chen & Eckstrand, arXiv:2204.04762v4, (2.1), p.5: "minimize_{x∈ℝⁿ} f₀(x) + ∑_{i=1}^s p_i f_i(x)".

**Formalization Note.** The computation is in `EReal`, where `0 * ⊤ = 0` as in the paper (footnote 1,
p.4). The function is evaluated only at `q ≥ 0` with no `fᵢ x = ⊥`, so no term is `⊥` and no
`∞ − ∞` occurs. The scenarios `i = 1, …, s` are `Fin s`, and `f₀` is a separate argument. -/
noncomputable def expObjective {n s : ℕ} (f0 : (Fin n → ℝ) → EReal)
    (fi : Fin s → (Fin n → ℝ) → EReal) (q : Fin s → ℝ) (x : Fin n → ℝ) : EReal :=
  f0 x + ∑ i, (q i : EReal) * fi i x

end RockafellianRelax.Supplement


