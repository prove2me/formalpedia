-- Prove2me | Definitions.Def_SilverRateSC_bridgePhi
-- name    : SilverRateSC_bridgePhi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:46:59.0591+00:00
-- url     : https://prove2.me/theorems/004459ed-dd9d-4220-94b9-3144f1e70f5c
-- title:
--   The bridging component (§3.3)
-- statement:
--   With $\delta_{\rm H}$ from (13), the **bridging component** uses the threshold and triangle
--   $$\ell_{i+1}=\frac{D_i\eta_i}2,\qquad K_\triangle=\operatorname{conv}\{0,(\delta_{\rm H},-\delta_{\rm H}),(\delta_{\rm H},0)\},$$
--   and
--   $$\Phi_i(X,Y)=\max_{g\in K_\triangle}\Bigl\{\bigl\langle g,(X-\ell_i-\ell_{i+1},\,Y-\ell_{i+1})\bigr\rangle-\tfrac12\|g\|^2\Bigr\}.$$
--   It is inserted between a Huber repair and the next bending component, so that the next coordinate is not affected once it passes $\ell_{i+1}$.
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), §3.3, p.16

import Mathlib
import Definitions.Def_SilverRateSC_envSupp
import Definitions.Def_SilverRateSC_repairPhi

namespace SilverRateSC

/-- The outgoing threshold of the bridge, `ℓ_{i+1} = D_i η_i / 2` (p. 16). -/
noncomputable def bridgeEll (κ : ℝ) (hs : List ℝ) (ℓ D : ℝ) : ℝ := D * etaGap κ hs ℓ D / 2

/-- The triangle `K_△ = conv{0, (δ_H, −δ_H), (δ_H, 0)}` (p. 16). -/
noncomputable def bridgeK (κ : ℝ) (hs : List ℝ) (ℓ D : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  convexHull ℝ {0, !₂[deltaH κ hs ℓ D, -deltaH κ hs ℓ D], !₂[deltaH κ hs ℓ D, 0]}

/-- **The bridging component** (§3.3): with `δ_H` from (13), `ℓ_{i+1} = D_i η_i / 2`,
`K_△ = conv{0, (δ_H, −δ_H), (δ_H, 0)}` and
`Φ_i(X, Y) = max_{g ∈ K_△} {⟨g, (X − ℓ_i − ℓ_{i+1}, Y − ℓ_{i+1})⟩ − ½‖g‖²}`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, §3.3, p. 16.

**Formalization Note** The max is `envSupp K_△` (a real supremum over the compact nonempty
triangle, hence a maximum). `hs` are the gap stepsizes, `ℓ = ℓ_i`, `D = D_i`. -/
noncomputable def bridgePhi (κ : ℝ) (hs : List ℝ) (ℓ D : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  envSupp (bridgeK κ hs ℓ D)
    !₂[z 0 - ℓ - bridgeEll κ hs ℓ D, z 1 - bridgeEll κ hs ℓ D]

end SilverRateSC


