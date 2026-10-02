-- Prove2me | Definitions.Def_DiscreteConvex_MConvexSetsB_LovaszExtension
-- name    : DiscreteConvex_MConvexSetsB_LovaszExtension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:30:49.791883+00:00
-- url     : https://prove2.me/theorems/973eeb62-8ad9-4be9-94d8-9bff85b6327e
-- title:
--   LovaszExtension
-- statement:
--   The **Lovász extension** $\hat\rho : \mathbb R^V \to \mathbb R \cup \{\pm\infty\}$ of a set function $\rho$, Eq. (4.6): the linear interpolation $\hat\rho(p) = \sum_{i=1}^{m-1}(\hat p_i-\hat p_{i+1})\rho(U_i) + \hat p_m\rho(U_m)$ with respect to the representation (4.5) of $p$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, Eq. (4.6).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.103, Eq. (4.6)

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SortedValues
import Definitions.Def_DiscreteConvex_MConvexSetsB_LevelSet
import Definitions.Def_DiscreteConvex_MConvexSetsB_ScalarWithTop

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.103, Eq. (4.6): the Lovász extension of a
set function, in `DiscreteConvex.MConvexSetsB`.
-/

namespace DiscreteConvex.MConvexSetsB

open Classical in
/-- The **Lovász extension** `ρ̂ : Rⱽ → R ∪ \{±∞\}` of a set function `ρ`, Eq. (4.6): the linear
interpolation `ρ̂(p) = Σᵢ₌₁^{m-1} (p̂ᵢ - p̂ᵢ₊₁) ρ(Uᵢ) + p̂ₘ ρ(Uₘ)` with respect to the
representation (4.5) of `p` as a combination of the level-set indicators `χ_{Uᵢ}`. -/
noncomputable def LovaszExtension {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (p : V → ℝ) : WithTop ℝ :=
  let vals := SortedValues p
  let m := vals.length
  (∑ i ∈ Finset.range (m - 1),
      ScalarWithTop (vals.getD i 0 - vals.getD (i + 1) 0) (ρ (LevelSet p (i + 1)))) +
    ScalarWithTop (vals.getD (m - 1) 0) (ρ (LevelSet p m))

end DiscreteConvex.MConvexSetsB


