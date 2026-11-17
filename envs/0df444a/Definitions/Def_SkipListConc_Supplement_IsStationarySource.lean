-- Prove2me | Definitions.Def_SkipListConc_Supplement_IsStationarySource
-- name    : SkipListConc_Supplement_IsStationarySource
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:57:23.173181+00:00
-- url     : https://prove2.me/theorems/05f7fad5-0a29-4e00-b90b-a5420910353a
-- title:
--   Stationary source
-- statement:
--   A source of accesses $X_1,\dots,X_m$ to $n$ items is **stationary** if its accesses are independent draws from one fixed (arbitrary) distribution on the items.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.2, p.11

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SkipListConc.Supplement

/-- A stationary source (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §1.2, p.11): the accesses `X_1, …, X_m` (indices into the `n`
items) are independent draws from one fixed, arbitrary distribution on the items. -/
structure IsStationarySource {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n m : ℕ}
    (X : Fin m → Ω → Fin n) : Prop where
  /-- every access is a random variable -/
  measurable : ∀ i, Measurable (X i)
  /-- the accesses are independent -/
  indep : iIndepFun X P
  /-- the accesses have one common law -/
  identDistrib : ∃ q : Measure (Fin n), ∀ i, P.map (X i) = q

end SkipListConc.Supplement


