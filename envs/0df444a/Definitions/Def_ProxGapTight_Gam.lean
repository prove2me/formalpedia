-- Prove2me | Definitions.Def_ProxGapTight_Gam
-- name    : ProxGapTight_Gam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:38.079438+00:00
-- url     : https://prove2.me/theorems/fda8d5ae-2c4a-4ce4-81be-e0649d5611fb
-- title:
--   Defining-vector threshold $\Gamma(\delta)$
-- statement:
--   For $0<\delta<1$, the **defining-vector threshold** is
--   $$
--   \Gamma(\delta)=1-(1-\delta)^{4/9}.
--   $$
--
--   In the main theorem the two counterexample words are at relative distance greater than $\Gamma(\delta)$ from the code, and every radius $\rho$ with $J_{3/2}(\delta)<\rho<\Gamma(\delta)$ is shown to fail the proximity-gaps property.
--
--   **Formalization Note** The real power $(1-\delta)^{4/9}$; for $0<\delta<1$ the base is in $(0,1)$.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), §1.1, p.2, display

import Mathlib

namespace ProxGapTight

/-- The **defining-vector threshold** `Γ(δ) := 1 − (1 − δ)^{4/9}`, Kominers, Thaler, Zheng,
manuscript (Sept. 2026), §1.1, p.2, display.

**Formalization Note.** `Real.rpow`; for the paper's range `0 < δ < 1` the base `1 − δ` is in
`(0, 1)`. -/
noncomputable def Gam (δ : ℝ) : ℝ := 1 - (1 - δ) ^ ((4 : ℝ) / 9)

end ProxGapTight


