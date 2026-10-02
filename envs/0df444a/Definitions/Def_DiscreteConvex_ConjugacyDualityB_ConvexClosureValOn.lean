-- Prove2me | Definitions.Def_DiscreteConvex_ConjugacyDualityB_ConvexClosureValOn
-- name    : DiscreteConvex_ConjugacyDualityB_ConvexClosureValOn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T01:31:10.275657+00:00
-- url     : https://prove2.me/theorems/68e8bb8d-5c1a-449b-9122-57b550cb10e7
-- title:
--   ConvexClosureValOn
-- statement:
--   The value of a convex-combination representation of $f$ restricted to a finite point set $S$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityB_DomZ

namespace DiscreteConvex.ConjugacyDualityB

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The value of a convex-combination representation of `f` restricted to a finite point set
`S`. -/
noncomputable def ConvexClosureValOn (f : (V → ℤ) → WithTop ℝ) (S : Finset (V → ℤ)) (x : V → ℝ) :
    WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
    (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ f) ∧
    (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) ∧
    L = ((∑ y ∈ S, lam y * (f y).untopD 0 : ℝ) : WithTop ℝ)}

end DiscreteConvex.ConjugacyDualityB


