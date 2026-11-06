-- Prove2me | Definitions.Def_IAFTRL_refArm
-- name    : IAFTRL_refArm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:44:53.68359+00:00
-- url     : https://prove2.me/theorems/f159baec-a956-4e9f-b15d-c4554809d373
-- title:
--   Reference action $r_t$
-- statement:
--   Given the cumulative estimate $S=\sum_{s<t}\hat\theta_s$, the **reference action** $r_t$ is a minimizer of the cumulative estimated loss,
--   $$
--   r_t\in\operatorname*{arg\,min}_{a\in\mathcal A}\hat L_{t-1,a},\qquad \hat L_{t-1,a}=a^\top S,
--   $$
--   with ties broken by the fixed ordering of the actions: $r_t$ is the minimizer of least index.
--
--   **Formalization Note** The reference action is returned as a vector of $\mathbb R^d$. The set of minimizers is nonempty whenever $K\ge1$; the value $0$ for $K=0$ is never used.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Section 2.1, p.17, Eq. (2.2)

import Mathlib

namespace IAFTRL

open Matrix

/-- **The reference action `r_t`.** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Section 2.1, p.17, Eq. (2.2): "`r_t ∈ argmin_{a∈𝒜}
L̂_{t−1,a}` … where we use a fixed ordering to break ties."

`refArm arms S` is the action `arms j` of least index `j` (in the order of `Fin K`) among the
minimizers of `j ↦ ⟨arms j, S⟩ = L̂_{t−1,j}`, with `S = Σ_{s<t} θ̂_s`.

**Formalization Note.** The reference action is returned as a vector of `ℝ^d` (it is an action
`r_t ∈ 𝒜`). The set of minimizers is nonempty exactly when `K ≥ 1`; the value `0` for `K = 0` is
never used. -/
noncomputable def refArm {d K : ℕ} (arms : Fin K → Fin d → ℝ) (S : Fin d → ℝ) : Fin d → ℝ :=
  if h : (Finset.univ.filter fun j : Fin K => ∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S).Nonempty then
    arms ((Finset.univ.filter fun j : Fin K => ∀ i, arms j ⬝ᵥ S ≤ arms i ⬝ᵥ S).min' h)
  else 0

end IAFTRL


