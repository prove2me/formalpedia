-- Prove2me | Definitions.Def_OmniMix_bV
-- name    : OmniMix_bV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:16.950682+00:00
-- url     : https://prove2.me/theorems/31bc43c6-780c-4831-972f-f594e6201652
-- title:
--   Threshold test function $b_v(p,q)$
-- statement:
--   For a threshold $v$ and $p,q$,
--   $$
--   b_v(p,q)=\mathbb I\{p<v\le q\}-\mathbb I\{q<v\le p\}\in\{-1,0,1\}.
--   $$
--   It is the closed form of the test function $b_{\lambda_v}$ of the V-shaped loss (see the milestone on closed forms).
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §2, p.10

import Mathlib

namespace OmniMix

/-- **Threshold test function `b_v(p, q)`.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §2, p.10: "`b_v(p, q) = I{p < v ≤ q} − I{q < v ≤ p}`",
the closed form of `b_{λ_v}` (proved equal in the milestone `closed_forms_bv_dv`). -/
noncomputable def bV (v p q : ℝ) : ℝ :=
  (if p < v ∧ v ≤ q then 1 else 0) - (if q < v ∧ v ≤ p then 1 else 0)

end OmniMix


