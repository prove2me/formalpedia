-- Prove2me | Definitions.Def_ProxGapTight_J32
-- name    : ProxGapTight_J32
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:33.600536+00:00
-- url     : https://prove2.me/theorems/e452e87c-cd5c-47ee-9d31-40f27e580528
-- title:
--   One-and-a-half Johnson radius $J_{3/2}(\delta)$
-- statement:
--   For $0<\delta<1$, the **one-and-a-half Johnson radius** is
--   $$
--   J_{3/2}(\delta)=1-(1-\delta)^{1/3}.
--   $$
--
--   Every linear code of relative distance $\delta$ has the proximity-gaps property at every radius below $J_{3/2}(\delta)$ [BGKS20]; the mission's main theorem shows that this radius cannot be improved for general linear codes.
--
--   **Formalization Note** The real power $(1-\delta)^{1/3}$; for $0<\delta<1$ the base is in $(0,1)$.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), §1, p.2, display

import Mathlib

namespace ProxGapTight

/-- The **one-and-a-half Johnson radius** `J_{3/2}(δ) := 1 − (1 − δ)^{1/3}`, Kominers, Thaler, Zheng,
manuscript (Sept. 2026), §1, p.2, display.

**Formalization Note.** `Real.rpow`; for the paper's range `0 < δ < 1` the base `1 − δ` is in
`(0, 1)`, so the real cube root is the usual one. -/
noncomputable def J32 (δ : ℝ) : ℝ := 1 - (1 - δ) ^ ((1 : ℝ) / 3)

end ProxGapTight


