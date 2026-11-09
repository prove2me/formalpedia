-- Prove2me | Definitions.Def_SelectiveDPT_matSqrt
-- name    : SelectiveDPT_matSqrt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:48:53.173641+00:00
-- url     : https://prove2.me/theorems/978fc148-ff2e-4a9a-bbad-9c43b2624af0
-- title:
--   Matrix square root $\Gamma^{1/2}$ and inverse square root $\Gamma^{-1/2}$
-- statement:
--   For a positive-definite matrix $\Gamma = \sum_j \lambda_j v_j v_j^\dagger$,
--   $$\Gamma^{1/2} = \sum_j \sqrt{\lambda_j}\, v_j v_j^\dagger, \qquad \Gamma^{-1/2} = \sum_j \lambda_j^{-1/2}\, v_j v_j^\dagger .$$
--   They appear in the per-query progress rate of the multiplicative adversary method.
--
--   **Formalization Note** Defined by the continuous functional calculus with $t \mapsto \sqrt t$ and $t \mapsto 1/\sqrt t$; the values on matrices that are not positive definite are never used.
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Proposition 2.12, p.16 (Γ^{1/2}, Γ^{-1/2})

import Mathlib

namespace SelectiveDPT

/-- The square root `Γ^{1/2}` of a positive-definite matrix (arXiv:2609.26678, Proposition 2.12,
p.16), by the continuous functional calculus with `Real.sqrt`. -/
noncomputable def matSqrt {n : Type*} [Fintype n] [DecidableEq n] (Γ : Matrix n n ℂ) :
    Matrix n n ℂ :=
  cfc Real.sqrt Γ

/-- The inverse square root `Γ^{−1/2}` of a positive-definite matrix (arXiv:2609.26678,
Proposition 2.12, p.16), by the continuous functional calculus with `t ↦ 1/√t`; for
positive-definite `Γ` it is the inverse of `matSqrt Γ`. -/
noncomputable def matInvSqrt {n : Type*} [Fintype n] [DecidableEq n] (Γ : Matrix n n ℂ) :
    Matrix n n ℂ :=
  cfc (fun t : ℝ => (Real.sqrt t)⁻¹) Γ

end SelectiveDPT


