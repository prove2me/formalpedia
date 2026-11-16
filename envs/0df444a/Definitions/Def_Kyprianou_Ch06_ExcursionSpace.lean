-- Prove2me | Definitions.Def_Kyprianou_Ch06_ExcursionSpace
-- name    : Kyprianou_Ch06_ExcursionSpace
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:01:03.625019+00:00
-- url     : https://prove2.me/theorems/5c6d57f8-f6bc-4389-a9ab-045df2403ff6
-- title:
--   Definition 6.14: excursion paths, lifetimes and cemetery state
-- statement:
--   The excursion space consists of real-valued càdlàg paths whose lifetime is strictly positive and may be infinite; each path is strictly negative on the open interval between zero and its lifetime, and returns to a non-negative value at its finite lifetime. A separate dummy or cemetery state represents times without an excursion. A path's values outside its lifetime are irrelevant to membership.
-- source:
--   Kyprianou (2006), first edition, Definition 6.14, printed pp. 154–155; physical two-up PDF pp. 82–83.

import Mathlib
open Filter
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Definition 6.14: an excursion has a strictly positive possibly infinite
lifetime, stays strictly below zero before its terminal time, has càdlàg
interior paths, and ends nonnegatively when its lifetime is finite. The
total representative's values outside (0, zeta] are immaterial. -/
def IsExcursion
    (epsilon : NNReal → Real) (zeta : WithTop NNReal) : Prop :=
  (0 : WithTop NNReal) < zeta ∧
  (∀ t : NNReal, 0 < t → (t : WithTop NNReal) < zeta →
     epsilon t < 0) ∧
  (zeta ≠ ⊤ → 0 ≤ epsilon (zeta.untopD 0)) ∧
  (∀ t : NNReal, 0 < t → (t : WithTop NNReal) < zeta →
     ContinuousWithinAt epsilon (Set.Ioi t) t) ∧
  (∀ t : NNReal, 0 < t → (t : WithTop NNReal) ≤ zeta →
     ∃ y : Real,
       Tendsto epsilon (nhdsWithin t (Set.Iio t)) (nhds y))

/-- The set E of all paths satisfying Definition 6.14. -/
def ExcursionSpace : Set ((NNReal → Real) × WithTop NNReal) :=
  {e | IsExcursion e.1 e.2}

/-- An excursion is a member of E, carrying its path and lifetime. -/
def Excursion := {e : (NNReal → Real) × WithTop NNReal // e ∈ ExcursionSpace}

/-- The distinguished cemetery state is separate from genuine excursions. -/
abbrev ExcursionOrCemetery := Option Excursion

end Kyprianou.Ch06


