-- Prove2me | Definitions.Def_SmoothedMIS_B0
-- name    : SmoothedMIS_B0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:46:43.353444+00:00
-- url     : https://prove2.me/theorems/0767e730-36d2-4a26-bbdd-f3f4b5213ada
-- title:
--   Parameters $B_0,\lambda,B,\theta,\ell,k$ of Algorithm 1 and its analysis
-- statement:
--   With natural logarithms:
--   1. the degree scale $B_0=\lfloor e^{\sqrt{\ln n}}\rfloor$ (§2);
--   2. $\lambda=\beta\ln n$ (§2);
--   3. the degree threshold $B=B_0+2\lambda$ (§4.1), a real number;
--   4. the marking probability $\theta=\lceil\lambda/2\rceil/\lambda$ (§4.1);
--   5. the gathering budget $\ell=1000\lceil\sqrt{\ln n}\rceil$ (§4.1);
--   6. $k=\lceil a\ln n\rceil$ (§4.2), which equals $\theta\lambda=\lceil\lambda/2\rceil$ when $\beta=2a$.
--
--   Every vertex of Algorithm 1 computes $B,\theta,\ell$ from $n$ and the built-in $\beta$; $k$ is used only in the analysis.
--
--   **Formalization Note** At $\lambda=0$ (only for $n=1$) Lean's division gives $\theta=0$; the coin law clamps $\theta$ to $[0,1]$.
-- source:
--   Dey, Dufoulon, Moses Jr., Pandurangan, Smoothed Analysis for Distributed MIS (manuscript, STOC 2027 submission, sha256 dc2131db058466142db72a65b8482787f2b03f36c54eb18702fb92825cdfb42d), §2, p.9 (PDF p.11); §4.1, p.17 (PDF p.19); §4.2, p.20 (PDF p.22)

import Mathlib

namespace SmoothedMIS

/-- **The degree scale** `B0 = ⌊e^{√ln n}⌋` (Dey, Dufoulon, Moses Jr., Pandurangan, *Smoothed
Analysis for Distributed MIS* (manuscript, sha256 dc2131db…), §2, p.9).

**Formalization Note** `ln` is `Real.log`; the floor is `Nat.floor`. The companion parameters
of Algorithm 1 (§4.1, p.17) and of its analysis (§4.2, p.20) are defined below. -/
noncomputable def B0 (n : ℕ) : ℕ := ⌊Real.exp (Real.sqrt (Real.log n))⌋₊

/-- `λ = β ln n` (§2, p.9). -/
noncomputable def lam (n : ℕ) (β : ℝ) : ℝ := β * Real.log n

/-- The degree threshold `B = B0 + 2λ` of Algorithm 1 (§4.1, p.17), a real number. -/
noncomputable def Bthr (n : ℕ) (β : ℝ) : ℝ := (B0 n : ℝ) + 2 * lam n β

/-- The marking probability `θ = ⌈λ/2⌉/λ` of Algorithm 1 (§4.1, p.17). For `λ = 0` (only at
`n = 1`) Lean's division gives `0`; the coin law clamps it to `[0, 1]`. -/
noncomputable def theta (n : ℕ) (β : ℝ) : ℝ := (⌈lam n β / 2⌉₊ : ℝ) / lam n β

/-- The gathering round budget `ℓ = 1000⌈√ln n⌉` of Algorithm 1 (§4.1, p.17). -/
noncomputable def ell (n : ℕ) : ℕ := 1000 * ⌈Real.sqrt (Real.log n)⌉₊

/-- `k = ⌈a ln n⌉` of the analysis (§4.2, p.20; equal to `θλ = ⌈λ/2⌉` when `β = 2a`). -/
noncomputable def kParam (a : ℝ) (n : ℕ) : ℕ := ⌈a * Real.log n⌉₊

end SmoothedMIS


