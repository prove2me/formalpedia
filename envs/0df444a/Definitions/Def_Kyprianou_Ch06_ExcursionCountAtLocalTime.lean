-- Prove2me | Definitions.Def_Kyprianou_Ch06_ExcursionCountAtLocalTime
-- name    : Kyprianou_Ch06_ExcursionCountAtLocalTime
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-15T22:15:35.556702+00:00
-- url     : https://prove2.me/theorems/3a3aa740-d396-4776-9d74-cc63bd2f20f1
-- title:
--   Excursion-mark count at finite local-time levels
-- statement:
--   Count the non-cemetery excursions whose inverse-local-time jump index is in (0,t] and whose càdlàg path/lifetime record belongs to a measurable mark set. In the Poisson setting counts are finite almost surely for finite-intensity sets.
-- source:
--   Kyprianou (2006), Definition 6.13 and Theorem 6.15, printed pp. 154–156.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_IndexedExcursion
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Count true excursions at local-time epochs in a prescribed measurable
set of excursion path/lifetime records, ignoring the cemetery state. -/
noncomputable def excursionCountAtLocalTime
    {Omega : Type}
    (X : NNReal → Omega → Real)
    (L : NNReal → Omega → NNReal)
    (omega : Omega) (t : NNReal)
    (A : Set ((NNReal → Real) × WithTop NNReal)) : Nat :=
  ( {s : NNReal | 0 < s ∧ s ≤ t ∧
      ∃ e, indexedExcursion X L s omega = some e ∧ e ∈ A} ).ncard

end Kyprianou.Ch06


