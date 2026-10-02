-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsD_ConvexClosureValOn
-- name    : DiscreteConvex_MConvexFunctionsD_ConvexClosureValOn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:50:33.958375+00:00
-- url     : https://prove2.me/theorems/037fa9ce-2130-4c7b-a9d6-5c62404a1a31
-- title:
--   ConvexClosureValOn
-- statement:
--   The value of a convex-combination representation of $f$ restricted to a finite point set $S$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsD_DomZ

namespace DiscreteConvex.MConvexFunctionsD

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- The convex closure of `f`, restricted to representations using points of `S`. -/
noncomputable def ConvexClosureValOn (f : (V → ℤ) → WithTop ℝ) (S : Finset (V → ℤ)) (x : V → ℝ) :
    WithTop ℝ :=
  sInf {L : WithTop ℝ | ∃ lam : (V → ℤ) → ℝ,
    (∀ y ∈ S, 0 ≤ lam y) ∧ (∑ y ∈ S, lam y = 1) ∧ (∀ y ∈ S, y ∈ DomZ f) ∧
    (∀ v, ∑ y ∈ S, lam y * (y v : ℝ) = x v) ∧
    L = ((∑ y ∈ S, lam y * (f y).untopD 0 : ℝ) : WithTop ℝ)}

end DiscreteConvex.MConvexFunctionsD


