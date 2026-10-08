-- Prove2me | Definitions.Def_WassersteinDRO_Guarantees_gelbrichRisk_v2
-- name    : WassersteinDRO_Guarantees_gelbrichRisk_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:49:40.115703+00:00
-- url     : https://prove2.me/theorems/85d79e26-87c1-419a-9cb5-34a7836121d0
-- title:
--   Gelbrich risk $R_\varepsilon(\hat\mu,\hat\Sigma,\ell)$ (paper's convention)
-- statement:
--   The Gelbrich risk (eq. (18)): $$R_\varepsilon(\hat\mu,\hat\Sigma,\ell) = \sup_{Q \in \mathcal{G}_\varepsilon(\hat\mu,\hat\Sigma)} R(Q,\ell) \in [-\infty,\infty],$$ the supremum over the Gelbrich hull of the risk $R(Q,\ell) = \mathbb{E}_Q[\ell(\xi)]$ taken with the paper's convention for non-integrable losses (`nominalRisk`). It replaces the `gelbrichRisk` that discarded every $Q$ under which $\ell$ is not integrable and ranged over the uncorrected hull.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen & Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, INFORMS TutORials 2019 (arXiv:1908.08729v2, 4 Nov 2024), eq. (18), p. 18

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_gelbrichHull_v2
import Definitions.Def_WassersteinDRO_Guarantees_nominalRisk_v2

open MeasureTheory

namespace WassersteinDRO.Guarantees

/-- The Gelbrich risk `R_ε(µ̂,Σ̂,ℓ) = sup_{Q ∈ G_ε(µ̂,Σ̂)} R(Q,ℓ)`, Kuhn et al. 2019, eq. (18),
p. 18: the supremum over the Gelbrich hull of the risk `R(Q,ℓ) = E_Q[ℓ(ξ)]` taken with the
paper's convention for non-integrable losses (`nominalRisk`). Valued in `EReal` (genuine
supremum; `+∞` if unbounded, `-∞` if the hull is empty). Replaces the retired `gelbrichRisk`,
which dropped every `Q` under which `ℓ` is not integrable (an `Integrable ℓ Q` guard) instead
of assigning it the paper's value, and which ranged over the retired hull. -/
noncomputable def gelbrichRisk {m : ℕ} (ε : ℝ) (Ξ : Set (EuclideanSpace ℝ (Fin m)))
    (μhat : EuclideanSpace ℝ (Fin m)) (SigmaHat : Matrix (Fin m) (Fin m) ℝ)
    (ℓ : EuclideanSpace ℝ (Fin m) → ℝ) : EReal :=
  ⨆ (Q : Measure (EuclideanSpace ℝ (Fin m))) (_ : Q ∈ gelbrichHull ε Ξ μhat SigmaHat),
    nominalRisk Q ℓ

end WassersteinDRO.Guarantees


