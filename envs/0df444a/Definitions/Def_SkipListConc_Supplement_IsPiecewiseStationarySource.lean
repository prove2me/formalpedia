-- Prove2me | Definitions.Def_SkipListConc_Supplement_IsPiecewiseStationarySource
-- name    : SkipListConc_Supplement_IsPiecewiseStationarySource
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:57:35.858742+00:00
-- url     : https://prove2.me/theorems/1260bb8e-5dc9-4f3e-8dd1-53c016b1bf0d
-- title:
--   Piecewise-stationary source with $P$ phases
-- statement:
--   A source of accesses $X_1,\dots,X_m$ is **piecewise stationary with $P$ phases** if its accesses are independent and come in $P$ consecutive phases, phase $s$ drawing from its own distribution $q_s$; the distributions and the change points are arbitrary and fixed in advance.
--
--   **Formalization Note** The phases are a monotone map from access indices to $\{0,\dots,P-1\}$; a phase may be empty, which only overcounts $P$.
-- source:
--   Kapoor–Tanveer, Counter-Free Self-Adjusting Skip Lists: Concentration Bounds, STOC 2027 submission (manuscript sha256 f82c3d35…), §1.2, p.11; Lemma 5.6(iii), p.36

import Mathlib

open MeasureTheory ProbabilityTheory

namespace SkipListConc.Supplement

/-- A piecewise-stationary source with `P` phases (Kapoor–Tanveer, *Counter-Free Self-Adjusting Skip Lists: Concentration Bounds*, STOC 2027
submission manuscript (sha256 f82c3d35…6dab6c), §1.2, p.11, and Lemma 5.6(iii),
p.36): the accesses `X_1, …, X_m` are independent and come in consecutive phases (blocks), phase
`s` drawing from its own distribution `q_s`; the distributions and the change points are
arbitrary and fixed in advance.

**Formalization Note** The phases are a monotone map `phase : Fin m → Fin P` (consecutive
blocks); a phase may be empty, which only overcounts `P`. -/
structure IsPiecewiseStationarySource {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n m : ℕ} (X : Fin m → Ω → Fin n) (P : ℕ) : Prop where
  /-- every access is a random variable -/
  measurable : ∀ i, Measurable (X i)
  /-- the accesses are independent -/
  indep : iIndepFun X μ
  /-- consecutive phases, each with its own law -/
  phases : ∃ phase : Fin m → Fin P, Monotone phase ∧
    ∃ q : Fin P → Measure (Fin n), ∀ i, μ.map (X i) = q (phase i)

end SkipListConc.Supplement


