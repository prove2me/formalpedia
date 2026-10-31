-- Prove2me | Definitions.Def_MissionAbort_IsLifetimeLaw
-- name    : MissionAbort_IsLifetimeLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:47:51.744394+00:00
-- url     : https://prove2.me/theorems/5d09b4f8-800f-4db6-989b-602f14419624
-- title:
--   Laws of $T_{12}$ and $T_{23}$
-- statement:
--   A law on the real line is a lifetime law if it is a probability measure, gives no mass to any point, and gives no mass to $(-\infty,0)$. These are the laws of $T_{12}$ and $T_{23}$ of the paper, which are general continuous distributions on $[0,\infty)$.
--
--   **Formalization Note** The paper assumes densities $g,f$. Only continuity of the CDFs is used in its proofs, so that is what is required here.
-- source:
--   Sun, Hu & Ye, Optimal Abort Policy for Mission-Critical Systems under Imperfect Condition Monitoring, arXiv:2505.03225v1, §3.1, p.9; Appendix A.2, p.EC.3

import Mathlib

namespace MissionAbort

open MeasureTheory

/-- A law of `T₁₂` or `T₂₃` (Sun, Hu & Ye, arXiv:2505.03225v1, §3.1, p.9, "a general continuous
distribution"): a probability measure on `ℝ` carried by `[0, ∞)` with a continuous CDF.

**Formalization Note.** The page assumes densities `g`, `f`. Only continuity of the CDFs is used
(p.EC.3, "the continuity assumption on T12, T13, T23"), so this is `NullSingletonClass` (no atoms). -/
structure IsLifetimeLaw (F : Measure ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure F
  noAtoms : NullSingletonClass F
  nonneg : F (Set.Iio 0) = 0

end MissionAbort


