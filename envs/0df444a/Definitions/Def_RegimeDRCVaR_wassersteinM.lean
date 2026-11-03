-- Prove2me | Definitions.Def_RegimeDRCVaR_wassersteinM
-- name    : RegimeDRCVaR_wassersteinM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:23:22.855788+00:00
-- url     : https://prove2.me/theorems/54f85cd2-324c-4f1f-9110-f824ec524032
-- title:
--   Wasserstein distance $W_m$ with $\ell_m$ cost
-- statement:
--   For laws $\mathbb P,\mathbb Q$ on $\mathbb R^I$, the **Wasserstein distance with $\ell_m$-norm** is
--   $$
--   W_m(\mathbb P,\mathbb Q)=\inf_\nu\Big\{\mathbb E^\nu\big[\|p-q\|_m\big]\ \Big|\ \nu\in\mathcal P(\mathbb R^I\times\mathbb R^I),\ \Pi_p\nu=\mathbb P,\ \Pi_q\nu=\mathbb Q\Big\},
--   $$
--   the least expected transport cost over couplings of $\mathbb P$ and $\mathbb Q$.
--
--   It measures the radius of the regime balls in Lemma EC.1.
--
--   **Formalization Note** $W_m$ is the published optimal transport cost `ShapleyNV.transportCost` (an infimum over the published `WassersteinDRO.StrongDuality.couplings`) with ground cost $c(p,q)=\|p-q\|_m$. The cost is nonnegative, so the expectation is a lower Lebesgue integral and $W_m$ takes values in $[0,+\infty]$ ($+\infty$ when there is no coupling). The published `WassersteinDRO.StrongDuality.wasserstein` is not reused: on `Fin I → ℝ` it would use Mathlib's sup norm, i.e. fix $m=\infty$.
-- source:
--   Pun, Wang, Yan, Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set, SSRN 4378930, display (2), p.8, with ρ(p,q) = ‖p − q‖_m, p.9 (W_m)

import Mathlib
import Definitions.Def_RegimeDRCVaR_normM
import Definitions.Def_ShapleyNV_transportCost

open MeasureTheory
open scoped ENNReal

namespace RegimeDRCVaR

/-- **The Wasserstein distance with ℓm cost** `W_m(P, Q)`
(Pun, Wang, Yan, *Data-Driven Distributionally Robust CVaR Portfolio Optimization under Regime-Switching Ambiguity Set*, SSRN 4378930, display (2), p.8, with `ρ(p, q) = ‖p − q‖_m`, p.9):
`W(P, Q) := inf_ν {𝔼^ν[ρ(p, q)] | ν ∈ 𝒫(ℝ^I × ℝ^I), Π_p ν = P, Π_q ν = Q}`.

**Formalization Note** This is the published optimal transport cost
`ShapleyNV.transportCost c P Q = inf_{γ ∈ couplings P Q} ∫⁻ ofReal (c q.1 q.2) dγ` (couplings are the
published `WassersteinDRO.StrongDuality.couplings`) with the ground cost `c(p, q) = ‖p − q‖_m`.
The cost is nonnegative, so `ofReal` loses nothing and the distance is in `ℝ≥0∞` (`∞` when there
is no coupling). The platform's `WassersteinDRO.StrongDuality.wasserstein` is not reused: on
`Fin I → ℝ` it would integrate Mathlib's sup norm, i.e. fix `m = ∞`. -/
noncomputable def wassersteinM {I : ℕ} (m : ℝ≥0∞) (P Q : Measure (Fin I → ℝ)) : ℝ≥0∞ :=
  ShapleyNV.transportCost (fun p q => normM m (p - q)) P Q

end RegimeDRCVaR


