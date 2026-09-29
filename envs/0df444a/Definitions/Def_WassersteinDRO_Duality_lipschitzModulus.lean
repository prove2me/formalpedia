-- Prove2me | Definitions.Def_WassersteinDRO_Duality_lipschitzModulus
-- name    : WassersteinDRO_Duality_lipschitzModulus
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T02:14:51.998855+00:00
-- url     : https://prove2.me/theorems/31fea54c-a350-45ed-8837-e09860ee3d6a
-- title:
--   Lipschitz modulus of a function
-- statement:
--   The Lipschitz modulus of a real-valued function $\varphi$ on $E$ with respect to the
--   fixed norm $\|\cdot\|$ is
--   $$\mathrm{Lip}(\varphi) = \sup_{\xi \ne \xi'} \frac{|\varphi(\xi)-\varphi(\xi')|}{\|\xi-\xi'\|},$$
--   valued in $[0,\infty]$ so that a function with no finite Lipschitz bound has modulus
--   $+\infty$ rather than an arbitrary or undefined value.
-- source:
--   Kuhn et al. 2019, p. 4, displayed equation immediately preceding Theorem 2

import Mathlib

namespace WassersteinDRO.Duality

/-- The Lipschitz modulus of a real-valued function `φ` on `E` with respect to the fixed norm
`‖·‖`, Kuhn et al. 2019, p. 4 (displayed equation just before Theorem 2):

`Lip(φ) = sup_{ξ≠ξ'} |φ(ξ)-φ(ξ')| / ‖ξ-ξ'‖`.

Valued in `ℝ≥0∞` so that a function that fails to be Lipschitz continuous (no finite bound)
is faithfully recorded as `Lip(φ) = ∞`, matching the paper's own remark that Theorem 5 is
"trivially satisfied" when `Lip(ℓ) = ∞`. -/
noncomputable def lipschitzModulus {E : Type*} [NormedAddCommGroup E] (φ : E → ℝ) : ENNReal :=
  ⨆ (x : E) (y : E) (_ : x ≠ y), ENNReal.ofReal (|φ x - φ y| / ‖x - y‖)

end WassersteinDRO.Duality


