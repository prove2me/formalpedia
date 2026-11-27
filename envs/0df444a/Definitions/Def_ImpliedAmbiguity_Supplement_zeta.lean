-- Prove2me | Definitions.Def_ImpliedAmbiguity_Supplement_zeta
-- name    : ImpliedAmbiguity_Supplement_zeta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:02:11.075034+00:00
-- url     : https://prove2.me/theorems/a83d186f-5be8-4c9e-a3b8-b1eaade5f080
-- title:
--   The optimal-portfolio direction $\zeta(\eta) = (I+\eta Q)^{-1}\Sigma_R^{-1}(\mu-R_f\mathbf 1)$
-- statement:
--   With $\Sigma_R \in \mathcal S^N_{++}$, $0\le\Sigma_M\le\Sigma_R$, $Q = \Sigma_R^{-1}\Sigma_M$ and the expected excess return vector $c = \mu - R_f\mathbf 1$, define $\zeta : (-1,\infty) \to \mathbb R^N$ by
--
--   $$
--   \zeta(\eta) = (I + \eta Q)^{-1}\,\Sigma_R^{-1}(\mu - R_f\mathbf 1). \tag{10}
--   $$
--
--   For a coefficient $\theta > 0$ of absolute risk aversion and a coefficient $\eta > -1$ of relative ambiguity aversion, the optimal portfolio (8) of the ambiguity-averse investor is $x = \theta^{-1}\zeta(\eta)$, so $\zeta$ isolates how the optimal portfolio depends on $\eta$ while $\Sigma_R$ and $\Sigma_M$ are held fixed.
--
--   **Formalization Note** The excess return vector is an argument `c` (Theorem 1 passes `excessReturn μ Rf`). Both inverses are Mathlib's total matrix inverse and the function is defined for every real $\eta$; Theorem 1 uses it only for $\eta > -1$, where $I + \eta Q$ is invertible under the standing assumptions.
-- source:
--   Hara & Honda, Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors, working paper (October 9, 2018; published version doi:10.1287/mnsc.2021.4097), eq. (10), p.14

import Mathlib
import Definitions.Def_ImpliedAmbiguity_Supplement_Q

open Matrix

namespace ImpliedAmbiguity.Supplement

/-- Hara & Honda, *Implied Ambiguity: Mean-Variance Efficiency and Pricing Errors*, working
paper (October 9, 2018; published version Management Science 2022, doi:10.1287/mnsc.2021.4097),
eq. (10), p.14: `ζ : (−1, ∞) → R^N`, `ζ(η) = (I + ηQ)⁻¹ Σ_R⁻¹ (µ − R_f 1)`, with
`Q = Σ_R⁻¹Σ_M`. For `(θ, η) ∈ R_++ × (−1, ∞)` the optimal portfolio (8) is `x = θ⁻¹ζ(η)` (p.14).

**Formalization Note.** The excess return vector `µ − R_f 1` is passed as `c` (Theorem 1
instantiates it with `ImpliedAmbiguity.excessReturn μ Rf`). Both inverses are Mathlib's total
matrix inverse; the function is total in `η : ℝ`, and Theorem 1 uses it only for `η > −1`, where
`I + ηQ` is invertible when `Σ_R ∈ S^N_++` and `0 ≤ Σ_M ≤ Σ_R` (the eigenvalues of `Q` lie in
`[0, 1]`). -/
noncomputable def zeta {N : ℕ} (SigmaR SigmaM : Matrix (Fin N) (Fin N) ℝ) (c : Fin N → ℝ)
    (η : ℝ) : Fin N → ℝ :=
  (1 + η • Q SigmaR SigmaM)⁻¹ *ᵥ (SigmaR⁻¹ *ᵥ c)

end ImpliedAmbiguity.Supplement


