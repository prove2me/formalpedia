-- Prove2me | Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexClosureValOn
-- name    : DiscreteConvex_MConvexFunctionsC_ConvexClosureValOn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:24:14.588254+00:00
-- url     : https://prove2.me/theorems/38a3f8c4-44c0-4785-9c98-f61126d96731
-- title:
--   ConvexClosureValOn
-- statement:
--   The value at $x$ of a convex-combination representation of $f$ restricted to a finite point set $S$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent, supporting the convex closure.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.97, Eq. (3.57)-adjacent, supporting the convex closure

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomZ

namespace DiscreteConvex.MConvexFunctionsC

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

end DiscreteConvex.MConvexFunctionsC


