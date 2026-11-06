-- Prove2me | Definitions.Def_OmniMix_clip
-- name    : OmniMix_clip
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:22.05111+00:00
-- url     : https://prove2.me/theorems/7163223d-e2a6-4810-83f9-9ffbbc1535b8
-- title:
--   Clipping $\mathrm{clip}(q,I_\delta)$
-- statement:
--   For $q\in[0,1]$ and $\delta\in[0,1/2]$,
--   $$
--   \mathrm{clip}(q,I_\delta)=\min\{1-\delta,\max\{\delta,q\}\},
--   $$
--   the point of $I_\delta$ nearest to $q$.
--
--   **Formalization Note** The value is returned in $[0,1]$ by a projection onto $[0,1]$ that does not change it when $0\le\delta\le1/2$.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §2, p.8 and Lemma 3.7, p.15

import Mathlib

namespace OmniMix

/-- **Clipping `clip(q, I_δ) = min{1 − δ, max{δ, q}}`.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §2, p.8 ("The clipping operator is
`clip(x, [a, b]) = min{b, max{a, x}}`") and Lemma 3.7, p.15.

**Formalization Note.** The value is returned as an element of `unitInterval` through
`Set.projIcc 0 1`, which does not change it when `0 ≤ δ ≤ 1/2` (every use has `0 < δ < 1/2`). -/
noncomputable def clip (δ : ℝ) (q : unitInterval) : unitInterval :=
  Set.projIcc 0 1 zero_le_one (min (1 - δ) (max δ (q : ℝ)))

end OmniMix


