-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_coeff
-- name    : ShallowShadows_ShadowNorm_coeff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:06.22001+00:00
-- url     : https://prove2.me/theorems/bfe72de4-1f3b-4307-bf32-13c338ac0271
-- title:
--   Pauli coefficients $\beta_\lambda = 2^{-n}\operatorname{tr}(P^\lambda O)$
-- statement:
--   Every $2^n\times 2^n$ matrix $O$ has a unique Pauli decomposition $O = \sum_\lambda \beta_\lambda P^\lambda$, with coefficients
--
--   $$
--   \beta_\lambda = 2^{-n} \operatorname{tr}(P^\lambda O).
--   $$
--
--   For a Hermitian $O$ (an observable) the coefficients are real.
--
--   **Formalization Note** The coefficient is complex-valued; every statement of the mission assumes $O$ Hermitian.
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, Theorem 7, p. 7; Eq. (12), p. 5

import Mathlib
import Definitions.Def_ShallowShadows_ShadowNorm_pauli

open ClassicalShadow.Linear

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, Theorem 7, p. 7 ("any
observable `O` with Pauli decomposition `O = Σ_λ β_λ P^λ`") and Eq. (12), p. 5: the Pauli
coefficient `β_λ = 2^{-n} tr(P^λ O)`.

**Formalization Note.** The Pauli strings form an orthogonal basis of the `2ⁿ × 2ⁿ` matrices with
`tr(P^λ P^λ') = 2ⁿ δ_{λλ'}`, so the decomposition `O = Σ_λ β_λ P^λ` is unique and its coefficients
are these. The value is complex; it is real when `O` is Hermitian, which every statement of the
mission assumes. -/
noncomputable def coeff {n : ℕ} (O : Op n) (lam : Bits n × Bits n) : ℂ :=
  ((2 : ℂ) ^ n)⁻¹ * (pauli lam * O).trace

end ShallowShadows.ShadowNorm


