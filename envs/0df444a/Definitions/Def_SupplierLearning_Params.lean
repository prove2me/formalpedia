-- Prove2me | Definitions.Def_SupplierLearning_Params
-- name    : SupplierLearning_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:42:38.052811+00:00
-- url     : https://prove2.me/theorems/a41efb24-ebba-401d-af05-dea75baa6809
-- title:
--   Parameters of the two-period procurement model
-- statement:
--   The parameters of the model: market sizes $a_1,a_2$ (the market-clearing price in period $t$ is $P_t=a_t-q_t$), discount factor $\delta$, type prior $\nu=\mathbb P\{\theta=\ell\}$, learning probability $\rho=\mathbb P\{\Lambda=1\}$, unit costs $c^\ell,c^h$ and learning rates $r^\ell,r^h$.
--
--   **Formalization Note** This is plain data; the assumptions on it are `Params.Standing`.
-- source:
--   Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, pp.5–7, Table 1

import Mathlib

namespace SupplierLearning

/-- **Parameters of the two-period procurement model.**
Gao, Nikoofal, Zhang, The Strategic Role of Supplier Learning, MSOM (2023), doi:10.1287/msom.2021.0285, §2, pp.5–7, Table 1 (PDF p.5–7).

**Formalization Note.** `a₁ a₂` are the market sizes `a_t`, `δ` the discount factor, `ν = P{θ = ℓ}`, `ρ = P{Λ = 1}`, `cl ch` the unit costs `c^ℓ c^h` and `rl rh` the learning rates `r^ℓ r^h`. Constraints on them live in `Params.Standing`. -/
structure Params where
  a₁ : ℝ
  a₂ : ℝ
  δ : ℝ
  ν : ℝ
  ρ : ℝ
  cl : ℝ
  ch : ℝ
  rl : ℝ
  rh : ℝ

end SupplierLearning


