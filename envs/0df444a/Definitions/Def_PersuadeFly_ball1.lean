-- Prove2me | Definitions.Def_PersuadeFly_ball1
-- name    : PersuadeFly_ball1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:57.613597+00:00
-- url     : https://prove2.me/theorems/c05507df-cfbe-4287-9a45-34d227a0c099
-- title:
--   The $\ell_1$-ball $\mathsf B_1(\mu,\epsilon)$ in the simplex
-- statement:
--   The closed $\ell_1$-ball of radius $\epsilon$ at $\mu$, inside the simplex:
--   $$
--   \mathsf B_1(\mu,\epsilon)=\{\mu'\in\Delta(\Omega):\|\mu'-\mu\|_1\le\epsilon\}.
--   $$
--
--   **Formalization Note** The ball is intersected with $\Delta(\Omega)$, as printed. It is defined for every real $\epsilon$; the paper uses $\epsilon\ge0$ and $\mu\in\Delta(\Omega)$.
-- source:
--   Zu, Iyer, Xu, Learning to Persuade on the Fly: Robustness Against Ignorance, arXiv:2102.10156v2, §3, p.21

import Mathlib
import Definitions.Def_PersuadeFly_l1Dist

namespace PersuadeFly

/-- **The `ℓ₁`-ball `B₁(μ, ϵ)` in the simplex.** Zu, Iyer, Xu, *Learning to Persuade on the Fly: Robustness Against Ignorance*, arXiv:2102.10156v2, §3, p.21:
`B₁(μ, ϵ) = {μ' ∈ Δ(Ω) : ‖μ' − μ‖₁ ≤ ϵ}`.

**Formalization Note** As printed, the ball is intersected with `Δ(Ω)`. It is defined for every real
`ϵ` and every `μ`; the paper uses it at `μ ∈ Δ(Ω)`, `ϵ ≥ 0`. -/
def ball1 {Ω : Type} [Fintype Ω] (μ : Ω → ℝ) (ϵ : ℝ) : Set (Ω → ℝ) :=
  {μ' | μ' ∈ stdSimplex ℝ Ω ∧ l1Dist μ' μ ≤ ϵ}

end PersuadeFly


