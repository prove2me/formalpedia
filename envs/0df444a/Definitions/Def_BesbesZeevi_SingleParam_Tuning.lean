-- Prove2me | Definitions.Def_BesbesZeevi_SingleParam_Tuning
-- name    : BesbesZeevi_SingleParam_Tuning
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T14:42:07.444333+00:00
-- url     : https://prove2.me/theorems/97a2fae6-ec12-44c6-8afc-1f9c8f46e98f
-- title:
--   Tuning (19)–(20): number of stages $\ell_n$ and stage lengths $\Delta^{(m)}_n$
-- statement:
--   For $m\ge1$ let $a_m=2^{m-1}/(2^m-1)$. For a market size $n$, the number of stages is
--
--   $$
--   \ell_n=\big\lceil(\log 2)^{-1}\log\log n\big\rceil ,
--   $$
--
--   and for a horizon $T>0$ the stage lengths are
--
--   $$
--   \Delta^{(m)}_n=\beta_n\,n^{(a_{\ell_n}/a_m)-1},\qquad m=1,\dots,\ell_n,\qquad \beta_n=\frac{T}{\sum_{m=1}^{\ell_n}n^{(a_{\ell_n}/a_m)-1}},
--   $$
--
--   so that $\Delta^{(1)}_n+\dots+\Delta^{(\ell_n)}_n=T$. Stage lengths grow geometrically in the exponent: the last stage has length $\beta_n$, and the first has length proportional to $n^{a_{\ell_n}-1}$.
--
--   **Formalization Note** The paper's $\ell_n=(\log 2)^{-1}\log\log n$ is not an integer; it is rounded up (`Nat.ceil`, which is $0$ when $\log_2\log n\le0$, i.e. for $n\le2$). Rounding up keeps $2^{\ell_n}\ge\log n$, which the rate computation on p. 37 needs; rounding down would not.
-- source:
--   Besbes & Zeevi, Dynamic Pricing Without Knowing the Demand Function: Risk Bounds and Near-Optimal Algorithms, Operations Research 57(6), 2009, DOI 10.1287/opre.1080.0640 (authors' final manuscript, last revised December 16, 2007), p. 18 (PDF p. 20), eqs. (19)-(20)

import Mathlib

namespace BesbesZeevi.SingleParam

/-- `a_m = 2^{m-1} / (2^m - 1)` for `m ≥ 1` (p. 18, after (20)). -/
noncomputable def aCoef (m : ℕ) : ℝ := (2 : ℝ) ^ (m - 1) / ((2 : ℝ) ^ m - 1)

/-- The number of stages `ℓ_n` of (19), p. 18: the paper's `(log 2)⁻¹ log log n`, rounded up to
an integer, `ℓ_n = ⌈log₂ (log n)⌉` (`0` when `log₂ (log n) ≤ 0`). -/
noncomputable def numStages (n : ℕ) : ℕ := ⌈Real.logb 2 (Real.log n)⌉₊

/-- The normalizing constant `β_n > 0` of (20), chosen so that the stage lengths sum to `T`:
`β_n = T / ∑_{m=1}^{ℓ_n} n^{a_{ℓ_n}/a_m - 1}`. -/
noncomputable def betaNorm (T : ℝ) (n : ℕ) : ℝ :=
  T / ∑ m ∈ Finset.Icc 1 (numStages n), (n : ℝ) ^ (aCoef (numStages n) / aCoef m - 1)

/-- The stage lengths (20), p. 18: `Δ^{(m)}_n = β_n n^{(a_{ℓ_n}/a_m) - 1}`, `m = 1, …, ℓ_n`. -/
noncomputable def stageLength (T : ℝ) (n : ℕ) (m : ℕ) : ℝ :=
  betaNorm T n * (n : ℝ) ^ (aCoef (numStages n) / aCoef m - 1)

end BesbesZeevi.SingleParam


