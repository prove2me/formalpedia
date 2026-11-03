-- Prove2me | Definitions.Def_FreeOrderEPTAS_IsGuess
-- name    : FreeOrderEPTAS_IsGuess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:27:14.848658+00:00
-- url     : https://prove2.me/theorems/ffc08c4f-f08a-43c4-b764-2dd471ca075d
-- title:
--   The guesses (14) and (15)
-- statement:
--   Guesses for the $2K+1$ buckets of $\sigma$ satisfy, for each bucket $B_i$,
--   $$\mathrm{BaseVal}(B_i)-\epsilon^2E\le\mathrm{BaseGuess}(B_i)\le\mathrm{BaseVal}(B_i),$$
--   $$\mathrm{BaseVal}(B_{i+1})-\mathrm{BaseVal}(B_i)-\epsilon^2E\le\mathrm{DeltaGuess}(B_i)\le\mathrm{BaseVal}(B_{i+1})-\mathrm{BaseVal}(B_i).$$
--   These are (14) and (15). The guesses are also non-negative, as the paper's grid is.
--
--   **Formalization Note** At the top bucket, `BaseVal` at $2K+1$ is $V^*_1$; the paper leaves $\mathrm{BaseVal}(B_{2K+2})$ undefined.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §3.3, p.18

import Mathlib
import Definitions.Def_FreeOrderEPTAS_bucket

namespace FreeOrderEPTAS

variable {n : ℕ}

/-- The guesses of §3.3 (arXiv:2007.13121v3, p.18) for the `2K + 1` buckets of `σ*`:
inequalities (14) and (15), with non-negative guesses as enumerated by the paper's grid
(`Fin (2K + 1)` is the 0-based index set; `BaseVal` at `2K + 1` is `V*_1`). -/
structure IsGuess (I : Instance n) (σ : Equiv.Perm (Fin n)) (ϵ E : ℝ)
    (b Δ : Fin (2 * numJumps I σ ϵ + 1) → ℝ) : Prop where
  /-- The grid is non-negative. -/
  base_nonneg : ∀ i, 0 ≤ b i
  /-- The grid is non-negative. -/
  delta_nonneg : ∀ i, 0 ≤ Δ i
  /-- (14), left. -/
  base_lower : ∀ i, BaseVal I σ ϵ i.val - ϵ ^ 2 * E ≤ b i
  /-- (14), right. -/
  base_upper : ∀ i, b i ≤ BaseVal I σ ϵ i.val
  /-- (15), left. -/
  delta_lower : ∀ i, BaseVal I σ ϵ (i.val + 1) - BaseVal I σ ϵ i.val - ϵ ^ 2 * E ≤ Δ i
  /-- (15), right. -/
  delta_upper : ∀ i, Δ i ≤ BaseVal I σ ϵ (i.val + 1) - BaseVal I σ ϵ i.val

end FreeOrderEPTAS


