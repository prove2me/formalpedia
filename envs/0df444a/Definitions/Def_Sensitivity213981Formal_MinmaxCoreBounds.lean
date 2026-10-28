-- Prove2me | Definitions.Def_Sensitivity213981Formal_MinmaxCoreBounds
-- name    : Sensitivity213981Formal_MinmaxCoreBounds
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T21:04:39.71098+00:00
-- url     : https://prove2.me/theorems/2128a45e-654c-4601-a02b-ad70a7d55272
-- title:
--   Minmax Core Bounds — sensitivity certificate definitions
-- statement:
--   The definitions for Minmax Core Bounds in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundMinmaxNumeric.dCore`, `ThreeBoundMinmaxNumeric.pCore`.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; MinmaxCoreBounds.lean, lines 1–86.

import Definitions.Def_Sensitivity213981Formal_MinmaxExpressions
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section
/- Reuse verified A/M/P entries in the min/max conditional formula. -/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ThreeBoundMinmaxNumeric
open ThreeBoundNumeric ThreeBoundFullProfile

def pCore (n pcross : ℕ) (v : Profile n) (j k l : Entry) (first : ℕ) : ℕ :=
  if j.same k then 0 else
    if j.tolerance=0 ∧ l.tolerance=0 ∧ j.plain ∧ k.plain ∧ l.plain then
      let tj := j.lowerAt 0
      let tk := k.lowerAt 0
      let tl := l.lowerAt 0
      let cross := pcross*(aExpr n j.guard tl).eval v
      let m0 := (minusExpr n l.guard tj tk).eval v
      let m1 := (minusExpr n l.guard k.guard j.guard).eval v
      let basic := 2*(bExpr n l.guard tj).eval v+cross+max ((plusExpr n tj tk tl).eval v) m1
      let target := if tj< tk then cross+max (max (2*m0) (m0+(bExpr n l.guard tk).eval v))
        ((unionExpr n l.guard tj tk tl).eval v+(bExpr n l.guard tl).eval v) else 0
      let guard := if k.guard< j.guard then cross+max (2*(bExpr n l.guard tk).eval v)
        (2*(bExpr n l.guard tl).eval v+m1) else 0
      min (min first basic) (max target guard)
    else first

def dCore (n degree : ℕ) (v : Profile n) (i j k l : Entry) (first : ℕ) : ℕ :=
  if j.same k then 0 else
    if j.tolerance=0 ∧ l.tolerance=0 ∧ l.plain ∧ k.upperAt 0≤ l.lowerAt 0 then
      let ti := i.lowerAt 0
      let ui := i.upperAt 0
      let tj := j.lowerAt 0
      let uj := j.upperAt 0
      let tk := k.lowerAt 0
      let uk := k.upperAt 0
      let tl := l.lowerAt 0
      let a := (aExpr n l.guard i.guard).eval v
      min first (max ((pairMExpr n degree ti ui i.guard 0 tj uj j.guard tk uk k.guard).eval v)
        (max (if tj< tk then (bExpr n ui tl).eval v+degree*a+(unionExpr n ti tj tk tl).eval v else 0)
          (if k.guard< j.guard then (bExpr n ti tl).eval v+(bExpr n ui tl).eval v+(degree-1)*a+
            (unionExpr n l.guard k.guard j.guard i.guard).eval v else 0)))
    else first













end ThreeBoundMinmaxNumeric



end
end Sensitivity213981Formal


