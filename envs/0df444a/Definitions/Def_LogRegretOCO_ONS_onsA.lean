-- Prove2me | Definitions.Def_LogRegretOCO_ONS_onsA
-- name    : LogRegretOCO_ONS_onsA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:58:33.168586+00:00
-- url     : https://prove2.me/theorems/cf426edb-1ad6-48dd-81f2-b1dfd5b43cea
-- title:
--   Online Newton Step matrix $A_t = \sum_{i\le t} \nabla_i\nabla_i^\top + \varepsilon I_n$
-- statement:
--   Given $\varepsilon \in \mathbb R$, losses $f_1, f_2, \dots$ and points $x_1, x_2, \dots$, with $\nabla_i = \nabla f_i(x_i)$, the **Online Newton Step matrix** of round $t \ge 0$ is
--   $$
--   A_t = \sum_{i=1}^{t} \nabla_i \nabla_i^\top + \varepsilon I_n .
--   $$
--   It accumulates the outer products of the observed gradients and plays the role of the Hessian in the Newton-type update; $A_0 = \varepsilon I_n$. For $\varepsilon > 0$ it is positive definite.
--
--   **Formalization Note** $\nabla_i \nabla_i^\top$ is `Matrix.vecMulVec`; the sum runs over $i \in \{1, \dots, t\}$.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Machine Learning 69 (2007) 169–192, doi:10.1007/s10994-007-5016-8, Fig. 2, p. 176 (PDF p. 8)

import Mathlib
import Definitions.Def_LogRegretOCO_ONS_onsGrad

namespace LogRegretOCO.ONS

/-- **The ONS matrix `A_t = Σ_{i=1}^t ∇_i∇_iᵀ + εI_n`.**
Hazan, Agarwal, Kale, *Logarithmic regret algorithms for online convex optimization*,
Machine Learning 69 (2007) 169–192, Fig. 2, p. 176: "A_t = Σ_{i=1}^t ∇_i∇_iᵀ + εI_n", with `∇_i = ∇f_i(x_i)`.

**Formalization Note.** `Matrix.vecMulVec u u` is the outer product `u uᵀ`; the sum runs over
`i ∈ {1, …, t}` (`Finset.Icc 1 t`), so `onsA ε f x 0 = εI_n` (the `V_0 = εI_n` of the proof of
Lemma 11, p. 191). -/
noncomputable def onsA {n : ℕ} (ε : ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ i ∈ Finset.Icc 1 t,
      Matrix.vecMulVec (WithLp.ofLp (onsGrad f x i)) (WithLp.ofLp (onsGrad f x i)) +
    ε • (1 : Matrix (Fin n) (Fin n) ℝ)

end LogRegretOCO.ONS


