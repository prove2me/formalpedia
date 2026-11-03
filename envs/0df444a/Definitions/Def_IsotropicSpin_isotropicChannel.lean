-- Prove2me | Definitions.Def_IsotropicSpin_isotropicChannel
-- name    : IsotropicSpin_isotropicChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:24:18.039369+00:00
-- url     : https://prove2.me/theorems/d7079a16-3c6d-446e-a6b7-0a4942b82b6d
-- title:
--   Isotropic spin channel $\Lambda_s(\rho)=\frac{1}{s(s+1)}\sum_k S_k\rho S_k$
-- statement:
--   For a spin $s>0$ and spin operators $S=(S_1,S_2,S_3)$ acting on a finite-dimensional space, the **isotropic spin channel** of eq. (6) is
--
--   $$
--   \Lambda_s(\rho)=\frac{1}{s(s+1)}\sum_{k=1}^{3} S_k\,\rho\,S_k .
--   $$
--
--   The paper's two channels are $\Lambda_{1/2}$, built from $S_k=\tfrac12\sigma_k$ (coefficient $4/3$), and $\Lambda_1$, built from the matrices (13) (coefficient $1/2$). Both are completely positive, trace preserving and unital (bistochastic), and covariant under rotations (7).
--
--   **Formalization Note** The map is written on all square matrices $X$, not only on density matrices; it is linear in $X$, so this is the linear extension of (6). The coefficient $1/(s(s+1))$ is computed in $\mathbb R$ and cast to $\mathbb C$; $s$ and $S$ are parameters, instantiated as `isotropicChannel (1/2) spinHalf` and `isotropicChannel 1 spinOne`.
-- source:
--   Alicki, Isotropic quantum spin channels and additivity questions, arXiv:quant-ph/0402080v1, eq. (6), p.1

import Mathlib

namespace IsotropicSpin

/-- **The isotropic spin channel** `Λ_s`, Alicki, arXiv:quant-ph/0402080v1, eq. (6), p. 1:
`Λ_s(ρ) = (1/(s(s+1))) Σ_{k=1}^{3} S_k ρ S_k`, for a spin `s` and spin operators
`S = (S₁, S₂, S₃)` acting on a finite-dimensional space indexed by `n`.

The paper's channels are `Λ_{1/2} = isotropicChannel (1/2) spinHalf` (coefficient `4/3`) and
`Λ₁ = isotropicChannel 1 spinOne` (coefficient `1/2`).

**Formalization Note** The map is written on all square matrices `X`, not only on density
matrices; it is linear in `X`, so this is the unique linear extension of (6). The coefficient
`1/(s(s+1))` is computed in `ℝ` and cast to `ℂ`. -/
noncomputable def isotropicChannel {n : Type*} [Fintype n] (s : ℝ) (S : Fin 3 → Matrix n n ℂ)
    (X : Matrix n n ℂ) : Matrix n n ℂ :=
  (((s * (s + 1))⁻¹ : ℝ) : ℂ) • ∑ k, S k * X * S k

end IsotropicSpin


