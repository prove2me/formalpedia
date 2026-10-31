-- Prove2me | Definitions.Def_MaskedLinx_IsOptimalSolution
-- name    : MaskedLinx_IsOptimalSolution
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:41:00.052881+00:00
-- url     : https://prove2.me/theorems/e23959b6-2991-48c1-9802-e04a5de4ba36
-- title:
--   Optimal solution of the scaled linx relaxation (2)
-- statement:
--   Let $C$ be a real square matrix indexed by a finite set $N$, $s$ a natural number and $\gamma$ a scaling parameter. A vector $\hat x\in\mathbb R^N$ is an optimal solution of the scaled linx relaxation (2) at $\gamma$ if
--
--   $$\hat x\in P(n,s)\quad\text{and}\quad f(C,s;\gamma;y)\le f(C,s;\gamma;\hat x)\ \text{ for every } y\in P(n,s),$$
--
--   that is, $\hat x$ attains the maximum defining $\mathrm{linx}(C,s;\gamma)$. With $\gamma=1$ it is an optimal solution of the linx relaxation (1).
--
--   **Formalization Note** The objective is the extended-real `linxObjective`, with $\mathrm{ldet}=-\infty$ off the positive definite matrices.
-- source:
--   Chen, Fampa, Lee, Masking Anstreicher's linx bound for improved entropy bounds, arXiv:2106.02980v1, displays (1) and (2), p.2

import Mathlib
import Definitions.Def_MaskedLinx_feasibleSet
import Definitions.Def_MaskedLinx_linxObjective

namespace MaskedLinx

/-- **An optimal solution of the scaled linx relaxation (2) at scaling `γ`.**
Chen, Fampa, Lee, *Masking Anstreicher's linx bound for improved entropy bounds*,
arXiv:2106.02980v1, display (2), p.2 (and display (1) for `γ = 1`).

`IsOptimalSolution C s γ x` says that `x ∈ P(n,s)` and `f(C,s;γ;y) ≤ f(C,s;γ;x)` for every
`y ∈ P(n,s)`, i.e. `x` attains the maximum in (2). With `γ = 1` it is an optimal solution of (1).

**Formalization Note.** The objective is the `EReal`-valued `linxObjective` (`ldet = −∞` off the
positive-definite matrices). -/
def IsOptimalSolution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (s : ℕ) (γ : ℝ) (x : ι → ℝ) : Prop :=
  x ∈ feasibleSet ι s ∧ ∀ y ∈ feasibleSet ι s, linxObjective C s γ y ≤ linxObjective C s γ x

end MaskedLinx


