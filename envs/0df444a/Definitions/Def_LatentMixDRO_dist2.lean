-- Prove2me | Definitions.Def_LatentMixDRO_dist2
-- name    : LatentMixDRO_dist2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:40.35193+00:00
-- url     : https://prove2.me/theorems/1a6acfea-36ae-4ec7-8a0d-f42b4fd151f9
-- title:
--   Euclidean distance on $\mathcal X\times\mathcal Y\subset\mathbb R^d\times\mathbb R$
-- statement:
--   For points $u=(x,y)$ and $u'=(x',y')$ of $\mathbb R^d\times\mathbb R$, the **Euclidean distance** is
--
--   $$
--   d\big((x,y),(x',y')\big)=\sqrt{\|x-x'\|^2+(y-y')^2}.
--   $$
--
--   This is the metric of the Lipschitz assumption A3 and of the Wasserstein distance $W_{p-1}$ on $\mathcal Z=\mathcal X\times\mathcal Y$.
--
--   **Formalization Note** Mathlib's product metric on $\mathbb R^d\times\mathbb R$ is the supremum metric, so the distance is written out. The label space is taken inside $\mathbb R$: the paper leaves $\mathcal Y$ unspecified, but the exponent $d+1$ in its rate requires $\dim(\mathcal X\times\mathcal Y)=d+1$.
-- source:
--   Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures, arXiv:2007.13982v2, Assumption A3, p.9, and Appendix D.7, p.38

import Mathlib

namespace LatentMixDRO

/-- The Euclidean distance on `𝒳 × 𝒴 ⊂ ℝ^d × ℝ`, written out:
`dist2 (x, y) (x', y') = √(‖x - x'‖² + (y - y')²)`.

Duchi, Hashimoto & Namkoong, Distributionally Robust Losses for Latent Covariate Mixtures,
arXiv:2007.13982v2, Assumption A3, p.9, and `‖(x, y) - (x', y')‖` in Appendix D.7, p.38.

**Formalization Note.** Mathlib's product metric on `E × ℝ` is the sup metric, so it is not used;
the paper's sample points live in `ℝ^d × ℝ` with the Euclidean norm of `ℝ^(d+1)`. -/
noncomputable def dist2 {d : ℕ} (u u' : EuclideanSpace ℝ (Fin d) × ℝ) : ℝ :=
  Real.sqrt (‖u.1 - u'.1‖ ^ 2 + (u.2 - u'.2) ^ 2)

end LatentMixDRO


