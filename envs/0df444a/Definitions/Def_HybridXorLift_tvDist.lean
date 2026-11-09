-- Prove2me | Definitions.Def_HybridXorLift_tvDist
-- name    : HybridXorLift_tvDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:11:47.765597+00:00
-- url     : https://prove2.me/theorems/5fea141f-585f-4ed5-8f16-79a6552269e4
-- title:
--   Total variation distance $\|P - P'\|_{\mathrm{TV}}$
-- statement:
--   For probability distributions $P, P'$ on a finite set $H$, the **total variation distance** is
--   $$
--   \|P - P'\|_{\mathrm{TV}} = \frac12 \sum_{h \in H} |P(h) - P'(h)| .
--   $$
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §2.4, p.10 (PDF p.12)

import Mathlib

namespace HybridXorLift

/-- The total variation distance `‖P − P′‖_TV = ½ Σ_h |P(h) − P′(h)|` of two distributions on a
finite set (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §2.4, p.10 (PDF p.12)). -/
noncomputable def tvDist {X : Type} [Fintype X] (p p' : X → ℝ) : ℝ :=
  (∑ x, |p x - p' x|) / 2

end HybridXorLift


