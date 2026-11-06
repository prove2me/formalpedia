-- Prove2me | Definitions.Def_FTPLLinBandit_weightLaw
-- name    : FTPLLinBandit_weightLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:02:45.730946+00:00
-- url     : https://prove2.me/theorems/2ade44f7-e361-40b0-94cc-89aca1698436
-- title:
--   Law of the random weights $\xi_{t,\tau}\sim\varphi$ of a scheme
-- statement:
--   For random weighting with scalar law $\varphi$ (Table 3), the **weight law** is the law on $\mathbb R$ with density $\varphi$: each slot of round $t$ draws fresh independent weights $\xi_{t,\tau}\sim\varphi$, $\tau<t$. The elliptical scheme uses no weights; its weight law is the point mass at $0$.
--
--   **Formalization Note** Giving the elliptical scheme the point-mass law lets a single run structure serve both constructions; the constant weights $0$ exist on every probability space, so no condition is added. The definition module also records that the law is $\sigma$-finite (needed to form product laws).
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Figure 2, Option 1, p.8; Table 3, p.21

import Mathlib
import Definitions.Def_FTPLLinBandit_Scheme
import Definitions.Def_FTPLLinBandit_scalarDens

open MeasureTheory

namespace FTPLLinBandit

/-- **The law of the scalar weights `ξ_{t,τ}` of a scheme.** Wei, arXiv:2610.17818, Figure 2,
Option 1, p.8: "independently drawing Z′ ∼ ρ₁ and ξ_τ ∼ φ for all τ < t"; Table 3, p.21.

For random weighting with scalar law `φ` it is the law with density `scalarDens φ`. The elliptical
scheme uses no weights; its weight law is the point mass at `0`, so its weights are the constant
`0` and play no role.

**Formalization Note.** Giving the elliptical scheme a weight law (the point mass at `0`) lets one
run structure serve both schemes; any probability space carries such weights (the constant `0`),
so this adds no condition. -/
noncomputable def weightLaw (s : Scheme) : Measure ℝ :=
  match s with
  | .randomWeighting _ φ => volume.withDensity fun ξ => ENNReal.ofReal (scalarDens φ ξ)
  | .elliptical _ => Measure.dirac 0

instance (s : Scheme) : SigmaFinite (weightLaw s) := by
  cases s <;> simp only [weightLaw] <;> infer_instance

end FTPLLinBandit


