-- Prove2me | Definitions.Def_SilverRateSC_repairPhi
-- name    : SilverRateSC_repairPhi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:46:00.306956+00:00
-- url     : https://prove2.me/theorems/b7752976-682c-4481-b7fb-244851d2c674
-- title:
--   The Huber repair component (13) and its outgoing pair (14)
-- statement:
--   Let $H_\delta$ be the one-sided Huber function ($0$ for $t\le0$, $t^2/2$ for $0\le t\le\delta$, $\delta t-\delta^2/2$ for $t\ge\delta$). With $\chi_i,\eta_i$ from (7), the **Huber repair component** is
--   $$\delta_{\rm H}=\frac{D_i\eta_i}{2+(\kappa-1)(1-\chi_i)},\qquad \Phi_i(X,Y)=\tfrac12H_{2\delta_{\rm H}}(X-Y-\ell_i),\qquad \ell_{i+1}=\frac{(\kappa-1)(1-\chi_i)\delta_{\rm H}}2.$$
--   The auxiliary `repairStep` returns the pair $(\ell_{i+1},D_{i+1})$ with $D_{i+1}=D_i\,\frac{(1-1/\kappa)b_i\chi_i\eta_i}{2[2+(\kappa-1)(1-\chi_i)]}$, the value identity (14) of Lemma 3.2 assigns to a checkpoint stepsize $b_i$.
--
--   **Formalization Note** $H_\delta$ is the published `SilverRateLB.oneSidedHuber`.
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), §3.2, (13), p.15 and (14), p.16

import Mathlib
import Definitions.Def_SilverRateLB_oneSidedHuber
import Definitions.Def_SilverRateSC_etaGap

namespace SilverRateSC

/-- The Huber scale `δ_H = D_i η_i / (2 + (κ − 1)(1 − χ_i))`, (13). -/
noncomputable def deltaH (κ : ℝ) (hs : List ℝ) (ℓ D : ℝ) : ℝ :=
  D * etaGap κ hs ℓ D / (2 + (κ - 1) * (1 - chiGap κ hs))

/-- **The Huber repair component** (13): `Φ_i(X, Y) = ½ H_{2δ_H}(X − Y − ℓ_i)`, with `H_δ` the
one-sided Huber function and `δ_H = D_i η_i / (2 + (κ − 1)(1 − χ_i))`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, §3.2, (13), p. 15.

**Formalization Note** `H_δ` is the published `SilverRateLB.oneSidedHuber`. `hs` are the gap
stepsizes, `ℓ = ℓ_i`, `D = D_i`. -/
noncomputable def repairPhi (κ : ℝ) (hs : List ℝ) (ℓ D : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  SilverRateLB.oneSidedHuber (2 * deltaH κ hs ℓ D) (z 0 - z 1 - ℓ) / 2

/-- The outgoing threshold of the Huber repair, `ℓ_{i+1} = (κ − 1)(1 − χ_i) δ_H / 2` (p. 15). -/
noncomputable def repairEll (κ : ℝ) (hs : List ℝ) (ℓ D : ℝ) : ℝ :=
  (κ - 1) * (1 - chiGap κ hs) * deltaH κ hs ℓ D / 2

/-- The outgoing pair `(ℓ_{i+1}, D_{i+1})` of a Huber repair at a checkpoint with stepsize `b`:
`ℓ_{i+1}` as above and `D_{i+1} = D_i (1 − 1/κ) b χ_i η_i / (2[2 + (κ − 1)(1 − χ_i)])`, the
identity (14) of Lemma 3.2. -/
noncomputable def repairStep (κ : ℝ) (hs : List ℝ) (b ℓ D : ℝ) : ℝ × ℝ :=
  (repairEll κ hs ℓ D,
    D * ((1 - 1 / κ) * b * chiGap κ hs * etaGap κ hs ℓ D /
      (2 * (2 + (κ - 1) * (1 - chiGap κ hs)))))

end SilverRateSC


