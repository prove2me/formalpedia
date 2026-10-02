-- Prove2me | Definitions.Def_DiscreteConvex_EconomicEquilibriumB_MNaturalConvexC
-- name    : DiscreteConvex_EconomicEquilibriumB_MNaturalConvexC
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T05:55:34.984649+00:00
-- url     : https://prove2.me/theorems/61ed6666-3bf9-4013-b28c-50e939ffeb09
-- title:
--   M-natural convexity of a cost function
-- statement:
--   M$^\natural$-convexity of a cost function $C:\mathbb{Z}^K\to\mathbb{R}\cup\{+\infty\}$, the mirror of M$^\natural$-concavity: for $x,y$ in the effective domain and $i\in\operatorname{supp}^+(x-y)$, $C(x)+C(y)\ge\min\{C(x-\chi_i)+C(y+\chi_i),\ \min_{j\in\operatorname{supp}^-(x-y)}[C(x-\chi_i+\chi_j)+C(y+\chi_i-\chi_j)]\}$.
--
--   Section 11.5 assumes it of every producer's cost function.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §11.5.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, §11.5

import Mathlib
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SuppPos
import Definitions.Def_DiscreteConvex_EconomicEquilibriumB_SuppNeg

namespace DiscreteConvex.EconomicEquilibriumB

open Classical
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- M♮-convexity of a cost function `C : Zᴷ → R ∪ {+∞}`, the mirror of `MNaturalConcave`.
Murota, *Discrete Convex Analysis*, SIAM 2003, §11.5 assumes it of every producer's cost. -/
def MNaturalConvexC (C : (K → ℤ) → WithTop ℝ) : Prop :=
  {z | C z ≠ ⊤}.Nonempty ∧
  ∀ x, C x ≠ ⊤ → ∀ y, C y ≠ ⊤ → ∀ i ∈ SuppPos x y,
    C x + C y ≥ min
      (C (fun w => x w - (if w = i then (1:ℤ) else 0)) +
        C (fun w => y w + (if w = i then (1:ℤ) else 0)))
      ((SuppNeg x y).inf (fun j =>
        C (fun w => x w - (if w = i then (1:ℤ) else 0) + (if w = j then (1:ℤ) else 0)) +
          C (fun w => y w + (if w = i then (1:ℤ) else 0) - (if w = j then (1:ℤ) else 0))))

end DiscreteConvex.EconomicEquilibriumB


