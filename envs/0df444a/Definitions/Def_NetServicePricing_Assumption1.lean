-- Prove2me | Definitions.Def_NetServicePricing_Assumption1
-- name    : NetServicePricing_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:36:09.731531+00:00
-- url     : https://prove2.me/theorems/48e7e4f0-23cb-482d-9e77-2d6ef7d09d20
-- title:
--   Assumption 1: spectral conditions on the network, the habit coefficient and the discount factor
-- statement:
--   Let $M$ be a network with eigenvalues $\lambda_1\ge\dots\ge\lambda_n$, let $\mu$ be the habit coefficient and $\delta\in(0,1)$ the discount factor. **Assumption 1** requires
--
--   1. $-1-\lambda_n<\mu<1-\lambda_1$;
--   2. $\delta\ge 2-\dfrac{1}{\lambda_1+\mu}$.
--
--   Part 1 keeps the discounted revenue bounded; part 2 guarantees that no consumer stops using the service after the price increase. The paper imposes the assumption throughout.
--
--   **Formalization Note** Both parts are stated for every real eigenvalue $\lambda$ of $M$: $-1<\lambda+\mu<1$ and $(2-\delta)(\lambda+\mu)\le1$. This is equivalent to the ordered form at the extreme eigenvalues. Part 2 is written in multiplied form: as $2-\delta>0$ it is equivalent to the printed inequality when $\lambda_1+\mu>0$, and when $\lambda_1+\mu=0$ (only for $M=0$, $\mu=0$) the printed $1/0$ is undefined and the condition is read as satisfied, instead of using Lean's $1/0=0$, which would exclude that network.
-- source:
--   Alizamir, Chen, Kim, Manshadi, Impact of Network Structure on New Service Pricing, SSRN 3236225, Assumption 1, p.11

import Mathlib

namespace NetServicePricing

/-- **Assumption 1.**
Alizamir, Chen, Kim, Manshadi, *Impact of Network Structure on New Service Pricing*, SSRN 3236225, Assumption 1, p.11: "Let λ1 ≥ ... ≥ λn be the ordered eigenvalues of adjacency matrix M,
and δ ∈ (0,1) be the firm's discount factor. We assume: 1. −1 − λn < µ < 1 − λ1.
2. δ ≥ 2 − 1/(λ1+µ)."

Part 1: every eigenvalue `λ` of `M` satisfies `−1 < λ + μ < 1`. Part 2: every eigenvalue `λ`
of `M` satisfies `(2 − δ)(λ + μ) ≤ 1`.

**Formalization Note** An eigenvalue is a real `λ` with `Module.End.HasEigenvalue (toLin' M) λ`.
Stating the bounds for every eigenvalue is equivalent to the ordered form for the extreme
eigenvalues `λ₁` and `λₙ`, so no ordering is needed. Part 2 is in multiplied form: since
`2 − δ > 0` for `δ < 1`, `(2 − δ)(λ₁ + μ) ≤ 1` is equivalent to `δ ≥ 2 − 1/(λ₁ + μ)` when
`λ₁ + μ > 0`; when `λ₁ + μ = 0` (only `M = 0`, `μ = 0`, since a zero-diagonal nonnegative matrix
has `λ₁ ≥ 0`) the printed `1/0` is undefined and the condition is read as satisfied. The constraint
`δ ∈ (0,1)` is carried separately by every statement. -/
def Assumption1 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (μ δ : ℝ) : Prop :=
  (∀ l : ℝ, Module.End.HasEigenvalue (Matrix.toLin' M) l → -1 < l + μ ∧ l + μ < 1) ∧
  (∀ l : ℝ, Module.End.HasEigenvalue (Matrix.toLin' M) l → (2 - δ) * (l + μ) ≤ 1)

end NetServicePricing


