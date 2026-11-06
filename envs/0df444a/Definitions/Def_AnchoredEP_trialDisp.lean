-- Prove2me | Definitions.Def_AnchoredEP_trialDisp
-- name    : AnchoredEP_trialDisp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:37:49.60554+00:00
-- url     : https://prove2.me/theorems/b3144393-fcd1-4507-a333-80471cc53a03
-- title:
--   Trial displacement $d_k(a)$
-- statement:
--   The **trial displacement** is
--   $$
--   d_k(a)=z_{k+1}(a)-z_{k+\frac12}(a)\quad(a>0),\qquad d_k(0)=0 .
--   $$
--   Its size and its Lipschitz modulus in $a$ control the regularity of the merit function of the line search.
-- source:
--   Jiang–Yoon, Anchored Extra-Proximal Methods: Optimal Higher-Order Methods for Monotone Inclusion Problems, arXiv:2609.30212, Appendix H, Eq. (99), p.40

import Mathlib
import Definitions.Def_AnchoredEP_IterState
import Definitions.Def_AnchoredEP_trialMid
import Definitions.Def_AnchoredEP_trialZ

namespace AnchoredEP

/-- **The trial displacement `d_k(a)`.** Jiang–Yoon, arXiv:2609.30212, Appendix H, Eq. (99), p.40:
`d_k(a) := z_{k+1}(a) − z_{k+½}(a)` for `a > 0`, and `d_k(0) := 0`.

**Formalization Note.** Defined by cases at `a = 0`, as in (99); only `a ∈ [0, ā_k]` is used. -/
noncomputable def trialDisp {d : ℕ} (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (sol : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z0 : EuclideanSpace ℝ (Fin d)) (s : IterState d) (a : ℝ) : EuclideanSpace ℝ (Fin d) :=
  if a = 0 then 0 else trialZ F sol z0 s a - trialMid F z0 s a

end AnchoredEP


