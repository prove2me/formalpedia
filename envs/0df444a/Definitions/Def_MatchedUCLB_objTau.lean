-- Prove2me | Definitions.Def_MatchedUCLB_objTau
-- name    : MatchedUCLB_objTau
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:36.337826+00:00
-- url     : https://prove2.me/theorems/3daea2df-b38d-45bc-b1c1-b53bb29736aa
-- title:
--   The phase scales $\tau_j=\eta^j\tau_0$
-- statement:
--   For an initial scale $\tau_0>0$, the **phase scales** are $\tau_j=\eta^j\tau_0$, with $\eta=\gamma/(2(1+\theta))$.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (4.15), p.9; Lemma 4.5, p.10

import Mathlib
import Definitions.Def_MatchedUCLB_eta

namespace MatchedUCLB

/-- **The phase scales `τ_j = η^j τ_0`.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, Eq. (4.15), p.9, with `η = γ/(2(1+θ))`
(Lemma 4.5, p.10). -/
noncomputable def objTau (q τ₀ : ℝ) (j : ℕ) : ℝ :=
  eta q ^ j * τ₀

end MatchedUCLB


