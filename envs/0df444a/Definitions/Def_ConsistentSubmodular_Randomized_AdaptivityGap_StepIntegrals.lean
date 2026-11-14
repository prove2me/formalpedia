-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals
-- name    : ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:08:40.860264+00:00
-- url     : https://prove2.me/theorems/33de9ac7-67a8-47e5-b4ce-28f79a5d6872
-- title:
--   Law of the random left endpoint: cdf $W$, ramp $H$, mean $B$, inverse $X=H^{-1}$, slope $g=1/W\circ X$, scaling
-- statement:
--   - `LeftLaw` $\iota$: for a finite index type $\iota$, a structure describing the law of the random left endpoint $\ell_J$: weights `prob` $p_j\ge0$ with $\sum_jp_j=1$, left endpoints `left` $\ell_j\in\mathbb R$, and a real number `low` such that $\mathrm{low}\le\ell_j$ whenever $p_j\ne0$ and some $j$ with $p_j\ne0$ has $\ell_j\le\mathrm{low}$ (so low is the smallest point of the support, which is an atom).
--
--   For a law $L$:
--
--   - `cdf` $x$: the distribution function $W(x)=\Pr[\ell_J\le x]=\sum_{j:\ell_j\le x}p_j$.
--   - `ramp` $x$: $H(x)=\sum_jp_j\,(x-\ell_j)^+=\int_{\mathrm{low}}^xW$ for $x\ge\mathrm{low}$.
--   - `mean`: $B=\mathbb E[\ell_J]=\sum_jp_j\ell_j$.
--   - `inv` $y$: the inverse $X=H^{-1}:[0,\infty)\to[\mathrm{low},\infty)$, defined as a right inverse of $H$ on $[\mathrm{low},\infty)$ evaluated at $\max(y,0)$, so that $X(y)=X(0)$ for negative $y$.
--   - `slope` $y$: $g(y)=1/W(X(y))$.
--   - `scale` $M\,hM$ (for $M>0$): the law with all endpoints, including low, divided by $M$ and the same weights.
--
--   These objects support the step-function integral computations of the adaptivity-gap analysis: the fixed and adaptive values of an interval instance are expressed through $W$, $H$, $B$ and $X$, and the scaling reduces to normalized instances.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/StepIntegrals.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ShadowChains

noncomputable section

open scoped BigOperators Topology

open MeasureTheory Filter Set

namespace ConsistentSubmodular.Shadow

/-- The law of the random left endpoint `ℓ_J`: weights `prob` on the left endpoints `left`,
whose support has smallest point `low`. -/
structure LeftLaw (ι : Type*) [Fintype ι] where
  prob : ι → ℝ
  left : ι → ℝ
  low : ℝ
  prob_nonneg : ∀ j, 0 ≤ prob j
  prob_sum : ∑ j, prob j = 1
  low_le : ∀ j, prob j ≠ 0 → low ≤ left j
  atom : ∃ j, prob j ≠ 0 ∧ left j ≤ low

namespace LeftLaw

variable {ι : Type*} [Fintype ι] (L : LeftLaw ι)

/-- The distribution function `W(x) = Pr[ℓ_J ≤ x]`. -/
def cdf (x : ℝ) : ℝ := ∑ j, if L.left j ≤ x then L.prob j else 0

/-- `H(x) = Σ_j p_j (x - ℓ_j)⁺ = ∫_{low}^x W`. -/
def ramp (x : ℝ) : ℝ := ∑ j, L.prob j * max 0 (x - L.left j)

/-- The mean left endpoint `B = E[ℓ_J]`. -/
def mean : ℝ := ∑ j, L.prob j * L.left j

/-- The inverse `X = H⁻¹ : [0, ∞) → [low, ∞)`, extended by `X(0)` to negative arguments. -/
def inv (y : ℝ) : ℝ := Function.invFunOn L.ramp (Ici L.low) (max y 0)

/-- `g(y) = 1 / W(X(y))`. -/
def slope (y : ℝ) : ℝ := 1 / L.cdf (L.inv y)

/-- The law with every endpoint divided by `M > 0`. -/
def scale (M : ℝ) (hM : 0 < M) : LeftLaw ι where
  prob := L.prob
  left j := L.left j / M
  low := L.low / M
  prob_nonneg := L.prob_nonneg
  prob_sum := L.prob_sum
  low_le j hj := div_le_div_of_nonneg_right (L.low_le j hj) hM.le
  atom := by
    obtain ⟨j, hj, hjl⟩ := L.atom
    exact ⟨j, hj, div_le_div_of_nonneg_right hjl hM.le⟩

end LeftLaw

end ConsistentSubmodular.Shadow

end


