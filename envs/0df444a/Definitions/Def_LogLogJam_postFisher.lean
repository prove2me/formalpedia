-- Prove2me | Definitions.Def_LogLogJam_postFisher
-- name    : LogLogJam_postFisher
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:23:55.230659+00:00
-- url     : https://prove2.me/theorems/8431847c-775b-4e0d-b54b-beb2c88a534d
-- title:
--   Posterior $p_H$, posterior Fisher information $F(p_H)$, predictive density, and the potential $G(H)$
-- statement:
--   Given a history $H$ and the uniform prior on $\mathbb T$, the **posterior** density of the squeezing angle is
--
--   $$
--   p_H(\theta)=\frac{q_\theta(H)}{\int_{\mathbb T}q_{\theta'}(H)\,d\theta'},
--   $$
--
--   and $F(p_H)$ is its Fisher information on the circle. If the next measurement has seed $W$ on $k$ copies, the next outcome has **predictive density** $q_0(y)=\int_{\mathbb T}p_H(\theta)f^W_\theta(y)\,d\theta$, and the conditional expectation of a function $\Phi$ of the extended history is $\mathbb E[\Phi(H_{t+1})\mid H_t=H]=\int q_0(y)\,\Phi(H,(W,y))\,dy$. The potential of §6.2 is
--
--   $$
--   G(H)=\frac{1+F(p_H)}{(8\pi E)^2}.
--   $$
--
--   The proof of the $\log\log E$ bound tracks $G$ along the protocol: $G(H_0)=1/(8\pi E)^2$ and $G$ must reach order $1/\varepsilon^2$ for success.
--
--   **Formalization Note** For histories whose seeds lie in $\mathrm{Cov}$ the normaliser is a positive real number. A randomized next measurement averages the per-seed conditional expectation over its seed. $F$ and $G$ take values in $[0,\infty]$.
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), §5.5, pp.25–26 (PDF pp.28–29); proof of Lemma 5.10, p.26; §6.2, p.30 (PDF p.33) ($G$)

import Mathlib
import Definitions.Def_LogLogJam_Obs

open MeasureTheory
open scoped ENNReal

namespace LogLogJam

/-- The normaliser `∫_𝕋 q_{θ'}(H) dθ'` of the posterior (arXiv:2607.12983, version of November 3,
2026, sha256 97b751ca…, §5.5, p.25), an integral over one period `[0, π)`. -/
noncomputable def postNorm {t : ℕ} (lam : ℝ) (H : Hist t) : ℝ :=
  ∫ θ in Set.Ico 0 Real.pi, histDens lam θ H

/-- The posterior density `p_{H}(θ) = q_θ(H) / ∫_𝕋 q_{θ'}(H) dθ'` of the parameter under the
uniform prior on `𝕋` (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, §5.5,
p.25).

**Formalization Note** For a history whose seeds all lie in `Cov` (every history a protocol
generates, almost surely) the normaliser is a positive real number. -/
noncomputable def post {t : ℕ} (lam : ℝ) (H : Hist t) (θ : ℝ) : ℝ :=
  histDens lam θ H / postNorm lam H

/-- The posterior Fisher information `F(p_H) = E_{θ∼p_H}[(∂_θ log p_H(θ))²]` (arXiv:2607.12983,
version of November 3, 2026, sha256 97b751ca…, §5.5, p.26). -/
noncomputable def postFisher {t : ℕ} (lam : ℝ) (H : Hist t) : ℝ≥0∞ :=
  circFisher (post lam H)

/-- The predictive density of the next outcome `y` given the history `H` and the next seed `W`:
`∫_𝕋 p_H(θ) f^W_θ(y) dθ` (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, proof
of Lemma 5.10, p.26: "q₀(y) is simply the probability density of observing H_t conditioned on
H_{t−1}"). -/
noncomputable def predDens {t : ℕ} (lam : ℝ) (H : Hist t) (k : ℕ) (W : Q k → Q k → ℝ)
    (y : Q k → ℝ) : ℝ :=
  ∫ θ in Set.Ico 0 Real.pi, post lam H θ * outDens k (VsqK lam θ k + Matrix.of W) y

/-- The conditional expectation `E[Φ(H_{t+1}) | H_t = H]` when the next measurement has seed `W`
on `k` copies: `∫ q₀(y) Φ(H, (W, y)) dy` with `q₀` the predictive density (arXiv:2607.12983,
version of November 3, 2026, sha256 97b751ca…, Lemma 5.10 and eq. (13), pp.26–30).

**Formalization Note** A randomized next measurement (an ensemble of seeds) gives the average of
this quantity over the seed; the statements are made for each seed. -/
noncomputable def nextCondExp {t : ℕ} (lam : ℝ) (H : Hist t) (k : ℕ) (W : Q k → Q k → ℝ)
    (Φ : Hist (t + 1) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (predDens lam H k W y) * Φ (Fin.snoc H ⟨k, (W, y)⟩)

/-- The potential `G(H) = (1 + F(p_H)) / (8πE)²` of §6.2 (arXiv:2607.12983, version of November 3,
2026, sha256 97b751ca…, p.30), with `E = energy lam`. Valued in `[0, ∞]`. -/
noncomputable def Gpot {t : ℕ} (lam : ℝ) (H : Hist t) : ℝ≥0∞ :=
  (1 + postFisher lam H) / ENNReal.ofReal ((8 * Real.pi * energy lam) ^ 2)

end LogLogJam


