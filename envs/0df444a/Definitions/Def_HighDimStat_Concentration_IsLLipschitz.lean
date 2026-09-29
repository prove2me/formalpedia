-- Prove2me | Definitions.Def_HighDimStat_Concentration_IsLLipschitz
-- name    : HighDimStat_Concentration_IsLLipschitz
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:24:10.925255+00:00
-- url     : https://prove2.me/theorems/62f68ac5-088b-48ad-a278-3b478eb3c0db
-- title:
--   An L-Lipschitz function with respect to the Euclidean norm
-- statement:
--   **Eq. (3.15).** A function $f:\mathbb R^n\to\mathbb R$ is $L$-**Lipschitz** with respect to
--   the Euclidean norm if $|f(x)-f(x')|\le L\|x-x'\|_2$ for all $x,x'\in\mathbb R^n$.
--
--   **Formalization Note** Restated locally in this chapter's own sub-namespace, per this book
--   series' cross-chapter rule, rather than importing Chapter 2's
--   `HighDimStat.TailBounds.IsLLipschitz`; realized directly via the explicit Euclidean-distance
--   formula on `Fin n → ℝ` rather than the `EuclideanSpace` type, matching how this chapter's own
--   other definitions (`IsSeparatelyConvex`) use plain coordinate vectors.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 62 (PDF p. 82), Eq. (3.15)

import Mathlib

namespace HighDimStat.Concentration

/-- **Eq. (3.15)**, Wainwright, *High-Dimensional Statistics* (2019), p. 62. A function
`f : ℝⁿ → ℝ` is `L`-Lipschitz with respect to the Euclidean norm `‖·‖₂` if
`|f(x)-f(x')| ≤ L‖x-x'‖₂` for all `x,x' ∈ ℝⁿ`. Restated locally in this chapter's own
sub-namespace, per this book series' cross-chapter rule, rather than importing Chapter 2's
`HighDimStat.TailBounds.IsLLipschitz`. -/
def IsLLipschitz {n : ℕ} (f : (Fin n → ℝ) → ℝ) (L : ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, |f x - f y| ≤ L * Real.sqrt (∑ i, (x i - y i) ^ 2)

end HighDimStat.Concentration


