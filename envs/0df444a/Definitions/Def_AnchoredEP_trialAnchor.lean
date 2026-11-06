-- Prove2me | Definitions.Def_AnchoredEP_trialAnchor
-- name    : AnchoredEP_trialAnchor
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:35:47.251064+00:00
-- url     : https://prove2.me/theorems/1d85c192-4cff-4b2f-9c38-33b5072cc016
-- title:
--   Anchored point of a trial step
-- statement:
--   At the state $(z_k,v_k,A_k)$ with anchor $z_0$, the trial step $a$ anchors its subproblem at
--   $$
--   \frac{a}{A_k+a}z_0+\frac{A_k}{A_k+a}z_k .
--   $$
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Appendix G.2, Eq. (87), p.37

import Mathlib
import Definitions.Def_AnchoredEP_IterState

namespace AnchoredEP

/-- **The anchored point of a trial step.** Jiang–Yoon, arXiv:2609.30212, Appendix G.2, Eq. (87),
p.37: for a trial step `a`, the subproblem is anchored at `a/(A_k + a) z₀ + A_k/(A_k + a) z_k`.

`trialAnchor z0 s a` is this point for the state `s = (z_k, v_k, A_k)`. -/
noncomputable def trialAnchor {d : ℕ} (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d)
    (a : ℝ) : EuclideanSpace ℝ (Fin d) :=
  (a / (s.A + a)) • z0 + (s.A / (s.A + a)) • s.z

end AnchoredEP


