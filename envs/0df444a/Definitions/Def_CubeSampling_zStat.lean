-- Prove2me | Definitions.Def_CubeSampling_zStat
-- name    : CubeSampling_zStat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:16:45.416451+00:00
-- url     : https://prove2.me/theorems/e446358d-6753-4d9c-8fed-a80c9cb3478c
-- title:
--   The statistic $Z_{n,V}$ of Theorem 2.1
-- statement:
--   Let $G = (G_1,\dots,G_m) \sim N(0, I_m)$ be independent of the inputs. Then
--   $$
--   Z_{n,V} = \begin{cases} \dfrac{\sigma^2}{n}\, G^\top \hat\Sigma_V^{-1} G, & \hat\Sigma_V \text{ invertible},\\[4pt] +\infty, & \hat\Sigma_V \text{ singular}.\end{cases}
--   $$
--   Its $(1-\delta)$-quantile equals the minimax risk $R^*_{n,\delta}(V)$.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Theorem 2.1, p.7

import Mathlib
import Definitions.Def_CubeSampling_empCov
open Matrix
open scoped ENNReal

namespace CubeSampling

/-- The statistic `Z_{n,V}` of Theorem 2.1 (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Theorem 2.1, p.7): for inputs `X` and an
independent `G ~ N(0, I_m)`, `Z = (σ²/n) G^⊤ Σ̂_V^{−1} G` if `Σ̂_V` is invertible and `+∞` if it is
singular. -/
noncomputable def zStat {d m : ℕ} (Φ : Fin m → Cube d → ℝ) (σ : ℝ) (n : ℕ)
    (ω : (Fin n → Cube d) × (Fin m → ℝ)) : ℝ≥0∞ :=
  haveI := Classical.propDecidable (IsUnit (empCov Φ n ω.1).det)
  if IsUnit (empCov Φ n ω.1).det then
    ENNReal.ofReal (σ ^ 2 / n * (ω.2 ⬝ᵥ ((empCov Φ n ω.1)⁻¹ *ᵥ ω.2)))
  else ⊤

end CubeSampling


