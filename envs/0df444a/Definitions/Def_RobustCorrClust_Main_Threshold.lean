-- Prove2me | Definitions.Def_RobustCorrClust_Main_Threshold
-- name    : RobustCorrClust_Main_Threshold
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:38:38.071137+00:00
-- url     : https://prove2.me/theorems/b8e268d5-fa46-4802-a2af-1016f6223ce6
-- title:
--   The triangular random threshold θ = (U₁+U₂)/2 and the mislabel probability (§6.3)
-- statement:
--   Let $U_1,U_2$ be independent uniform random variables on $[0,1]$ and $\theta=(U_1+U_2)/2$. For a real $\hat y$ and a real $b$,
--   $$\Pr_\theta\big[\mathbf 1[\hat y\ge\theta]\ne b\big]$$
--   is the Lebesgue measure of the set of $(U_1,U_2)\in[0,1]^2$ with $\mathbf 1[\hat y\ge(U_1+U_2)/2]\ne b$.
--
--   **Formalization Note.** The probability is `volume` on `ℝ × ℝ` of a subset of the unit square, converted to a real (it is finite).
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), pp. 49-50, rounding algorithm and Lemma 6.7

import Mathlib

namespace RobustCorrClust.Main

open MeasureTheory

/-! The random threshold of the rounding algorithm (§6.3, pp. 49–50). -/

/-- `Pr_θ[1[ŷ ≥ θ] ≠ b]` for `θ = (U₁ + U₂)/2`, `U₁, U₂` independent uniform on `[0, 1]`
(Lemma 6.7, p. 50): the Lebesgue measure of the set of `(U₁, U₂) ∈ [0, 1]²` with
`1[ŷ ≥ (U₁ + U₂)/2] ≠ b`, as a real number. -/
noncomputable def thrProb (y b : ℝ) : ℝ :=
  (volume {p : ℝ × ℝ | p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 ∧
    (if (p.1 + p.2) / 2 ≤ y then (1 : ℝ) else 0) ≠ b}).toReal

end RobustCorrClust.Main


