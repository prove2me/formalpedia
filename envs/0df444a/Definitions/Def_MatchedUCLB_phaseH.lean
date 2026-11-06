-- Prove2me | Definitions.Def_MatchedUCLB_phaseH
-- name    : MatchedUCLB_phaseH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:23.563433+00:00
-- url     : https://prove2.me/theorems/7100b389-f14d-4c84-afe1-6d71755547b7
-- title:
--   The center increment $h_j=t^\star_jv_j+\sum_i(m-i+1)\tau_ju_{j,i}$
-- statement:
--   For a scale $\tau>0$, a starting direction $v$ and chain directions $u_1,\dots,u_m$, the **center increment** of the phase is
--
--   $$
--   h=t^\star v+\sum_{i=1}^{m}(m-i+1)\,\tau\,u_i,\qquad t^\star=\sqrt m\,(m+1)\tau .
--   $$
--
--   At $h$ all chain residuals of (4.9) equal $\tau$.
--
--   **Formalization Note** The chain directions are indexed from $0$, so the coefficient of the $0$-based direction $u_i$ is $(m-i)\tau$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.10), p.8; Definition E.1, p.83

import Mathlib
import Definitions.Def_MatchedUCLB_tStar

namespace MatchedUCLB

/-- **The center increment `h_j`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Eq. (4.10), p.8:
"`h_j = t⋆_j v_j + ∑_{i=1}^m (m − i + 1) τ_j u_{j,i}`", and Definition E.1, p.83.

**Formalization Note.** The chain directions are `u : Fin m → ℝ^d` indexed from `0`, so `u i` is
the paper's `u_{j,i+1}` and the coefficient `m − (i+1) + 1` becomes `m − i`. -/
noncomputable def phaseH {d m : ℕ} (τ : ℝ) (v : EuclideanSpace ℝ (Fin d)) (u : Fin m → EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  tStar m τ • v + ∑ i : Fin m, (((m : ℝ) - (i : ℕ)) * τ) • u i

end MatchedUCLB


