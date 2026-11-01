-- Prove2me | Definitions.Def_DRORSEquiv_empiricalOptimum
-- name    : DRORSEquiv_empiricalOptimum
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:35:26.307147+00:00
-- url     : https://prove2.me/theorems/5976d489-211d-4b6e-a4bf-f8893427bca7
-- title:
--   Empirical optimum $Z_0$
-- statement:
--   The **empirical (nominal) optimum** is
--
--   $$Z_0=\min_{x\in\mathcal X}\mathbb E_{\mathbb P^\dagger}[f(x,\tilde z)]=\min_{x\in\mathcal X}\frac1S\sum_{s\in[S]}f(x,\hat z_s),$$
--
--   the optimal value of sample average approximation. Targets of the RS model satisfy $\tau\ge Z_0$.
--
--   **Formalization Note** The minimum is an infimum in `EReal` ($-\infty$ if unbounded below, $+\infty$ if $\mathcal X=\emptyset$).
-- source:
--   Wang, Ran, Zhou, He, On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models, authors' manuscript (2025), §2, p.6

import Mathlib
import Definitions.Def_DRORSEquiv_Model

namespace DRORSEquiv

/-- **The empirical (nominal) optimum** `Z₀` (Wang, Ran, Zhou, He, *On the Equivalence and Performance of Distributionally Robust Optimization and Robust Satisficing Models*, authors' manuscript (2025), §2, p.6):
`Z₀ = min_{x ∈ X} E_{P†}[f(x, z̃)] = min_{x ∈ X} (1/S) ∑_{s ∈ [S]} f(x, ẑ_s)`, where `P†` is the empirical
distribution of the samples.

**Formalization Note.** The minimum is written as an infimum in `EReal` (`−∞` if unbounded below,
`+∞` if `X = ∅`). -/
noncomputable def empiricalOptimum {E Ω : Type*} {S : ℕ} (M : Model E Ω S) : EReal :=
  ⨅ x ∈ M.X, (((1 / (S : ℝ)) * ∑ s : Fin S, M.f x (M.zhat s) : ℝ) : EReal)

end DRORSEquiv


