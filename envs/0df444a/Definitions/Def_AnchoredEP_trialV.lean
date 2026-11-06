-- Prove2me | Definitions.Def_AnchoredEP_trialV
-- name    : AnchoredEP_trialV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:52.529519+00:00
-- url     : https://prove2.me/theorems/af642831-d212-4c0f-9efd-1b95cb13ad01
-- title:
--   Trial vector $v_{k+1}(a)$
-- statement:
--   The vector associated with the trial point is
--   $$
--   v_{k+1}(a)=\frac1a\Big(\frac{a}{A_k+a}z_0+\frac{A_k}{A_k+a}z_k-z_{k+1}(a)\Big)-P_{k,a}(z_{k+1}(a)),
--   $$
--   with $P_{k,a}=\mathbb T^{(p-1)}_{L_p}(\cdot\,;z_{k+\frac12}(a))$. By the subproblem inclusion it lies in $H(z_{k+1}(a))$.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Appendix G.2, Eq. (88), p.37

import Mathlib
import Definitions.Def_AnchoredEP_regTaylor
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_trialAnchor
import Definitions.Def_AnchoredEP_trialMid
import Definitions.Def_AnchoredEP_trialZ

namespace AnchoredEP

/-- **The trial vector `v_{k+1}(a)`.** Jiang–Yoon, arXiv:2609.30212, Appendix G.2, Eq. (88), p.37:
`v_{k+1}(a) := (1/a)(a/(A_k + a) z₀ + A_k/(A_k + a) z_k − z_{k+1}(a)) − P_{k,a}(z_{k+1}(a))`,
with `P_{k,a} = 𝕋_λ^{(p−1)}(·; z_{k+½}(a))` and `λ = L_p` (also Algorithm 3 line 10). -/
noncomputable def trialV {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (p : ℕ) (L : ℝ)
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) (a : ℝ) : EuclideanSpace ℝ (Fin d) :=
  a⁻¹ • (trialAnchor z0 s a - trialZ F sol z0 s a)
    - regTaylor F p L (trialMid F z0 s a) (trialZ F sol z0 s a)

end AnchoredEP


