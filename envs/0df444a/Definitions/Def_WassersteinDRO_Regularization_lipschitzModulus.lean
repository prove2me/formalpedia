-- Prove2me | Definitions.Def_WassersteinDRO_Regularization_lipschitzModulus
-- name    : WassersteinDRO_Regularization_lipschitzModulus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:40:23.590118+00:00
-- url     : https://prove2.me/theorems/4b529bd2-b93b-4beb-8052-47ba88c61683
-- title:
--   Lipschitz modulus of a function
-- statement:
--   The Lipschitz modulus of a real-valued function $\varphi$ on $E$ with respect to a fixed norm
--   is $\mathrm{Lip}(\varphi) = \sup_{\xi \ne \xi'} |\varphi(\xi)-\varphi(\xi')| / \|\xi-\xi'\|$,
--   valued in the extended nonnegative reals so a non-Lipschitz function is recorded as
--   $\mathrm{Lip}(\varphi) = \infty$.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization, INFORMS TutORials 2019, displayed equation, p. 4, just before Theorem 2

import Mathlib

namespace WassersteinDRO.Regularization

/-- The Lipschitz modulus of a real-valued function `φ` on `E` with respect to the fixed
norm `‖·‖`, Kuhn et al. 2019, p. 4 (displayed equation just before Theorem 2):
`Lip(φ) = sup_{ξ≠ξ'} |φ(ξ)-φ(ξ')| / ‖ξ-ξ'‖`. Valued in `ℝ≥0∞` so that a function that fails
to be Lipschitz continuous is faithfully recorded as `Lip(φ) = ∞`. Redefined locally in this
chapter's own namespace; see `Def_WassersteinDRO_Regularization_wassersteinDistance` for
why. -/
noncomputable def lipschitzModulus {E : Type*} [NormedAddCommGroup E] (φ : E → ℝ) : ENNReal :=
  ⨆ (x : E) (y : E) (_ : x ≠ y), ENNReal.ofReal (|φ x - φ y| / ‖x - y‖)

end WassersteinDRO.Regularization


