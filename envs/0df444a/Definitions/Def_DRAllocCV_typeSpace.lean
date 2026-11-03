-- Prove2me | Definitions.Def_DRAllocCV_typeSpace
-- name    : DRAllocCV_typeSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:12:12.963195+00:00
-- url     : https://prove2.me/theorems/4cc09179-8952-40f2-a6ba-6f5ad5b93be5
-- title:
--   Type space $\mathcal T=\prod_{i}[\underline t_i,\overline t_i]$
-- statement:
--   A principal allocates a single good to one of $I\ge 2$ agents $i\in\mathcal I=\{1,\dots,I\}$. Agent $i$'s **type** $t_i$ is the value he would generate for the principal; it lies in the interval $\mathcal T_i=[\underline t_i,\overline t_i]$ with $0\le\underline t_i<\overline t_i<\infty$. The **type space** is the box
--
--   $$
--   \mathcal T=\prod_{i\in\mathcal I}\mathcal T_i=\prod_{i\in\mathcal I}[\underline t_i,\overline t_i]\subseteq\mathbb R^I .
--   $$
--
--   Every distribution, mechanism and payoff of the mission lives on this box.
--
--   **Formalization Note** Agents are the elements of a finite type $\iota$ and type profiles are functions $\iota\to\mathbb R$. The standing assumptions $I\ge2$ and $0\le\underline t_i<\overline t_i$ are hypotheses of the theorems, not part of the definition.
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §2, p.5

import Mathlib

namespace DRAllocCV

/-- The **type space** `𝒯 = ∏_{i ∈ ℐ} 𝒯ᵢ` with `𝒯ᵢ = [t̲ᵢ, t̄ᵢ]` (Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §2, p.5).
Agent `i`'s type `tᵢ` lies in the interval `[tlo i, thi i]`; a type profile is a vector
`t : ι → ℝ`.

**Formalization Note.** Agents are the elements of a finite type `ι`; the box is
`Set.univ.pi (fun i => Set.Icc (tlo i) (thi i))` inside `ι → ℝ`. The paper's standing
assumptions `I ≥ 2` and `0 ≤ t̲ᵢ < t̄ᵢ` are hypotheses of every theorem, not part of this
definition. -/
def typeSpace {ι : Type*} (tlo thi : ι → ℝ) : Set (ι → ℝ) :=
  Set.univ.pi fun i => Set.Icc (tlo i) (thi i)

end DRAllocCV


