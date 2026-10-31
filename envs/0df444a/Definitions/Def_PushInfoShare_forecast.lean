-- Prove2me | Definitions.Def_PushInfoShare_forecast
-- name    : PushInfoShare_forecast
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:03.908994+00:00
-- url     : https://prove2.me/theorems/b7c0ee73-dd03-4095-a7ff-76d1de7f5aa0
-- title:
--   Retailer's forecast $\mathbb E[\theta\mid\delta_1,\delta_2]$
-- statement:
--   At prices $w$ and signals $y$, the retailer's forecast of $\theta$ is
--   $$S_1X_1+S_2X_2,\qquad X_j=\begin{cases}y_j&\text{if }j\text{ shares},\\(w_j-\alpha_j)/B_j&\text{otherwise.}\end{cases}$$
--   A signal that is not shared is inferred from the price through the conjectured rule, at every price, on or off the equilibrium path. This inference is the signaling effect of the wholesale price.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), §3, p.8; §4, pp.10–11

import Mathlib
import Definitions.Def_PushInfoShare_Profile

namespace PushInfoShare

/-- The retailer's forecast `E[θ | δ₁, δ₂]` of Jain, SSRN:3388957 (PDF of 2021-04-25), §3–§4,
pp.8–11, at observed prices `w` and signals `y`: `S₁ X₁ + S₂ X₂`, where `Xⱼ = yⱼ` if `δⱼ` is true
(signal shared), and `Xⱼ = (wⱼ − αⱼ) / Bⱼ` otherwise, the signal inferred from the price through
the conjectured rule.

**Formalization Note.** The inference applies at every `w`, on or off the equilibrium path. The
equilibrium predicate requires `Bⱼ ≠ 0` for an unshared signal. That `S₁ Y₁ + S₂ Y₂` is the
conditional expectation of `θ` is `assumption_1_relations`. -/
noncomputable def forecast (S : Fin 2 → ℝ) (δ : Fin 2 → Bool) (str : Profile)
    (w y : Fin 2 → ℝ) : ℝ :=
  ∑ j : Fin 2, S j * (if δ j then y j else (w j - str.α j) / str.B j)

end PushInfoShare


