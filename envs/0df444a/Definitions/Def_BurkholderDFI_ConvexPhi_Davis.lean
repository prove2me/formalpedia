-- Prove2me | Definitions.Def_BurkholderDFI_ConvexPhi_Davis
-- name    : BurkholderDFI_ConvexPhi_Davis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:11:43.273976+00:00
-- url     : https://prove2.me/theorems/6a1e6d71-d0b4-4193-b428-9b70a1cc29eb
-- title:
--   Davis's decomposition into small and large martingale jumps
-- statement:
--   For a martingale with differences $d_k$, let $d_k^*=\max_{0\le j\le k}|d_j|$, where $d_0=0$. Davis splits each difference into
--   $$
--   y_k=d_k\mathbf1_{\{|d_k|\le2d_{k-1}^*\}},\qquad
--   z_k=d_k\mathbf1_{\{|d_k|>2d_{k-1}^*\}}.
--   $$
--   Set $a_k=y_k-E(y_k\mid\mathcal A_{k-1})$, $b_k=z_k+E(y_k\mid\mathcal A_{k-1})$, $g_n=\sum_{k=1}^n a_k$, and $h_n=\sum_{k=1}^n b_k$. The small-jump process $g$ and large-jump process $h$ form the decomposition in (14.1).
--
--   **Formalization Note** The conditional expectation of $y_k$ is the ordinary real-valued conditional expectation: $|y_k|\le|d_k|$ and martingale differences are integrable. At index zero, the partial sums $g_0$ and $h_0$ are zero; the martingale theorem specifies their Mathlib extensions.
-- source:
--   Burkholder, Distribution Function Inequalities for Martingales, Ann. Probability 1 (1973), §14, p. 33, (14.1)

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

namespace BurkholderDFI.ConvexPhi

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- §14, p. 33: yₖ = dₖ 1{|dₖ| ≤ 2d*ₖ₋₁}. -/
noncomputable def davisY (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if |BurkholderDFI.SquareFnLp.dseq f k ω| ≤ 2 * (BurkholderDFI.SquareFnLp.maxFnN (BurkholderDFI.SquareFnLp.dseq f) (k - 1) ω).toReal then BurkholderDFI.SquareFnLp.dseq f k ω else 0

/-- §14, p. 33: zₖ = dₖ 1{|dₖ| > 2d*ₖ₋₁}. -/
noncomputable def davisZ (f : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if 2 * (BurkholderDFI.SquareFnLp.maxFnN (BurkholderDFI.SquareFnLp.dseq f) (k - 1) ω).toReal < |BurkholderDFI.SquareFnLp.dseq f k ω| then BurkholderDFI.SquareFnLp.dseq f k ω else 0

/-- §14: aₖ = yₖ − E(yₖ|𝒜ₖ₋₁). -/
noncomputable def davisA (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω => davisY f k ω - (P[davisY f k | ℱ (k - 1)]) ω

/-- §14: bₖ = zₖ + E(yₖ|𝒜ₖ₋₁). -/
noncomputable def davisB (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (k : ℕ) : Ω → ℝ :=
  fun ω => davisZ f k ω + (P[davisY f k | ℱ (k - 1)]) ω

/-- (14.1): gₙ = ∑ₖ₌₁ⁿ aₖ. -/
noncomputable def davisG (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.Icc 1 n, davisA ℱ P f k ω

/-- (14.1): hₙ = ∑ₖ₌₁ⁿ bₖ. -/
noncomputable def davisH (ℱ : Filtration ℕ mΩ) (P : Measure Ω) (f : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ k ∈ Finset.Icc 1 n, davisB ℱ P f k ω

end BurkholderDFI.ConvexPhi


