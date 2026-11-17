-- Prove2me | Definitions.Def_Kyprianou_Ch07_UnitTimeOscillationObservables
-- name    : Kyprianou_Ch07_UnitTimeOscillationObservables
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-16T14:53:19.63214+00:00
-- url     : https://prove2.me/theorems/66840285-424f-4b8d-a09d-fd8613f385d6
-- title:
--   Exercise 7.2: maximal unit-time Lévy increment
-- statement:
--   For each integer n≥0 and path ω, the unit-time maximal absolute Lévy increment Y_n(ω) equals sup_{t∈[n,n+1]}|X_t(ω)−X_n(ω)|. This is the exact observable appearing before Exercise 7.2(i).
-- source:
--   Kyprianou (2006), Exercise 7.2 preamble, printed p.207; original physical PDF p.216, Windows Ky.pdf sheet 109.

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch07

/-- Exercise 7.2: maximal increment within the unit interval [n,n+1],
relative to the process value at its left endpoint. -/
noncomputable def maximalUnitIncrement
    {Omega : Type} (X : NNReal → Omega → Real)
    (n : Nat) (omega : Omega) : Real :=
  sSup {z : Real | ∃ t : NNReal,
    (n : NNReal) ≤ t ∧ t ≤ (n + 1 : NNReal) ∧
      z = |X t omega - X n omega|}

end Kyprianou.Ch07


