-- Prove2me | Definitions.Def_LevyExtrema_SBA_stickSummand
-- name    : LevyExtrema_SBA_stickSummand
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:39:56.45439+00:00
-- url     : https://prove2.me/theorems/549ce7d9-7caf-4f25-a788-c598d3005c83
-- title:
--   The summands $(Y_{L_{k-1}}-Y_{L_k},(Y_{L_{k-1}}-Y_{L_k})^+,\ell_k\mathbb 1_{\{Y_{L_{k-1}}-Y_{L_k}>0\}})$ of (1.1)
-- statement:
--   Given a path $Y$ and a stick-breaking process $(\ell_k,L_k)$ on $[0,T]$, the $k$-th **stick-breaking summand** is the vector in $\mathbb R^3$
--
--   $$\Big(Y_{L_{k-1}}-Y_{L_k},\ (Y_{L_{k-1}}-Y_{L_k})^+,\ \ell_k\cdot\mathbb 1_{\{Y_{L_{k-1}}-Y_{L_k}>0\}}\Big),\qquad x^+=\max\{x,0\}.$$
--
--   It is the increment of $Y$ over the stick $[L_k,L_{k-1}]$, its positive part, and the stick's length if the increment is positive. The stick-breaking representation (1.1) writes $(X_T,\overline X_T,\tau_T)$ as the sum of all summands, and the SBA (1.2) keeps the first $n$.
--
--   **Formalization Note** 0-based: `stickSummand T Y V k` is the paper's $(k+1)$-th summand, so $\sum_{k=1}^n$ becomes a sum over `range n`.
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, (1.1), p. 2

import Mathlib
import Definitions.Def_LevyExtrema_SBA_StickBreaking

open scoped NNReal

namespace LevyExtrema.SBA

/-- **The k-th summand of the stick-breaking representation (1.1) and of the SBA (1.2).**
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, (1.1), p. 2: the summands
`(Y_{L_{k−1}} − Y_{L_k}, (Y_{L_{k−1}} − Y_{L_k})^+, ℓ_k · 1{Y_{L_{k−1}} − Y_{L_k} > 0})`.

With `D = Y_{L_k} − Y_{L_{k+1}}` (0-based), `stickSummand T Y V k = (D, max D 0, ℓ_{k+1}·1{D > 0})`.

**Formalization Note.** Lean's index `k` is the paper's `k + 1`: `stickSummand T Y V k` is the
paper's (k+1)-th summand, so the paper's `Σ_{k=1}^n` is `Σ_{k ∈ range n}`. -/
noncomputable def stickSummand (T : ℝ≥0) {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ)
    (k : ℕ) (ω : Ω) : ℝ × ℝ × ℝ :=
  let D := atStick T Y V k ω - atStick T Y V (k + 1) ω
  (D, max D 0, if 0 < D then stickLen T V k ω else 0)

end LevyExtrema.SBA


