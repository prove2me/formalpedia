-- Prove2me | Definitions.Def_Kyprianou_Ch05_MonotoneDensity
-- name    : Kyprianou_Ch05_MonotoneDensity
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T09:25:38.457342+00:00
-- url     : https://prove2.me/theorems/688e7c6c-78d7-4e12-b1f1-279732ae74b0
-- title:
--   Eventually monotone densities and slow variation at zero
-- statement:
--   An eventually monotone density may become monotone in either direction beyond a finite cutoff. Slow variation at zero is regular variation with index zero, ensuring the correct endpoint in Corollary 5.15.
-- source:
--   Kyprianou (2006), Definition 5.12 and Theorem 5.14, printed pp. 126-127.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
open MeasureTheory Filter
set_option autoImplicit false

namespace Kyprianou.Ch05

/-- Ultimately monotone (in either direction), as required by Theorem 5.14. -/
def UltimatelyMonotone (u : Real → Real) : Prop :=
  ∃ a : Real, MonotoneOn u (Set.Ici a) ∨ AntitoneOn u (Set.Ici a)

/-- Slowly varying at the origin, needed for Corollary 5.15. -/
def SlowlyVaryingAtZero (f : Real → Real) : Prop :=
  RegularlyVaryingAtZero f 0

/-- Monotone in a punctured right neighbourhood of zero, for Corollary 5.15. -/
def UltimatelyMonotoneAtZero (u : Real → Real) : Prop :=
  ∃ delta : Real, 0 < delta ∧
    (MonotoneOn u (Set.Ioc 0 delta) ∨
     AntitoneOn u (Set.Ioc 0 delta))

end Kyprianou.Ch05


