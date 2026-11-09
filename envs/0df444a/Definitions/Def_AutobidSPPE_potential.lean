-- Prove2me | Definitions.Def_AutobidSPPE_potential
-- name    : AutobidSPPE_potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T18:09:49.605834+00:00
-- url     : https://prove2.me/theorems/e408b20e-9c38-4902-81a6-f7b84349a71f
-- title:
--   Augmented error potential $\mathcal V(\alpha)$ (43)
-- statement:
--   Partition the bidders into $I_0=\{i:\bar v_i\le4\rho_i\}$ and $I_1=[n]\setminus I_0$. The **augmented error potential** of a multiplier profile $\alpha$ is
--   $$
--   \mathcal V(\alpha)=\max\Big\{\frac{E(y)^2}{U^2},\ \max_{i\in I_0}(1-\alpha_i)^2\Big\},\qquad y_i=\bar v_i\alpha_i .
--   $$
--   The maximum over $I_0$ is zero when $I_0$ is empty.
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), (43), p.23

import Mathlib
import Definitions.Def_AutobidSPPE_weightedError
import Definitions.Def_AutobidSPPE_supU

namespace AutobidSPPE

/-- The augmented error potential (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6), (43), p.23):
`𝒱(α) = max{E(y)²/U², max_{i∈I₀} (1 − αᵢ)²}` with `yᵢ = v̄ᵢαᵢ` and `I₀ = {i : v̄ᵢ ≤ 4ρᵢ}`.

**Formalization Note** The maximum over `I₀` is `⨆` over the subtype, which is `0` when `I₀` is
empty, as on the page. -/
noncomputable def potential {n : ℕ} (vbar vhat ρ : Fin n → ℝ) (α : Fin n → ℝ) : ℝ :=
  max (weightedError vbar vhat ρ (fun i => vbar i * α i) ^ 2 / supU vhat ^ 2)
    (⨆ i : {i : Fin n // vbar i ≤ 4 * ρ i}, (1 - α i.1) ^ 2)

end AutobidSPPE


