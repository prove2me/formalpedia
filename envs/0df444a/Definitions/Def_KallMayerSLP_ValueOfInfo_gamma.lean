-- Prove2me | Definitions.Def_KallMayerSLP_ValueOfInfo_gamma
-- name    : KallMayerSLP_ValueOfInfo_gamma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:15.764886+00:00
-- url     : https://prove2.me/theorems/5d99d776-adde-4468-8768-ff602dc5bde5
-- title:
--   Wait-and-see value $\gamma(\xi)$
-- statement:
--   For a realization $\xi$, the optimal value of the linear program in which the first-stage decision is taken after $\xi$ is known:
--
--   $$
--   \gamma(\xi)=\min_{x,y}\{c^{\mathsf T}x+q(\xi)^{\mathsf T}y : Ax=b,\ T(\xi)x+W(\xi)y=h(\xi),\ x\ge0,\ y\ge0\}.
--   $$
--
--   **Formalization Note** The minimum is the infimum in $[-\infty,+\infty]$: $+\infty$ if the LP is infeasible, $-\infty$ if it is unbounded; a feasible bounded LP attains it.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, §2.3, p.244 (PDF 253)

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_TwoStageSLP

open Matrix

namespace KallMayerSLP.ValueOfInfo

/-- **The wait-and-see value `γ(ξ)`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, p.244 (PDF 253):
`γ(ξ) := min_{x,y} {cᵀx + qᵀ(ξ)y}` s.t. `Ax = b`, `T(ξ)x + W(ξ)y = h(ξ)`, `x, y ≥ 0`, "the family of
LP's for `ξ ∈ Ξ`".

**Formalization Note.** The book's `min` is the infimum in `EReal` over the feasible pairs `(x, y)`:
`+∞` if the LP is infeasible, `−∞` if it is unbounded below; a feasible bounded LP attains it. -/
noncomputable def gamma {r n₁ m₁ n₂ m₂ : ℕ} (P : TwoStageSLP r n₁ m₁ n₂ m₂)
    (ξ : Fin r → ℝ) : EReal :=
  sInf ((fun p : (Fin n₁ → ℝ) × (Fin n₂ → ℝ) => ((P.c ⬝ᵥ p.1 + P.q ξ ⬝ᵥ p.2 : ℝ) : EReal)) ''
    {p | P.A *ᵥ p.1 = P.b ∧ P.T ξ *ᵥ p.1 + P.W ξ *ᵥ p.2 = P.h ξ ∧ 0 ≤ p.1 ∧ 0 ≤ p.2})

end KallMayerSLP.ValueOfInfo


