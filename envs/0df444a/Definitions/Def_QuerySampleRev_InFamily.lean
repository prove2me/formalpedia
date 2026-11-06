-- Prove2me | Definitions.Def_QuerySampleRev_InFamily
-- name    : QuerySampleRev_InFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:29.695895+00:00
-- url     : https://prove2.me/theorems/1d1ff83f-97bf-4c28-9e3f-5f15d7e3b805
-- title:
--   The quasi-MHR family of value distributions
-- statement:
--   A measure $\mu$ on $\mathbb R$ belongs to the **quasi-MHR family** if
--   1. $\mu$ is a probability measure;
--   2. $\mu$ is supported on $[0,\infty)$, i.e. $\mu((-\infty,0))=0$;
--   3. $\mu$ is quasi-MHR;
--   4. its optimal revenue $r^*=\sup_{p\ge0}pQ(p)$ is finite.
--
--   These are the paper's standing assumptions: value distributions are supported on $[0,\infty)$ (§2.1) and have finite optimal revenue (§2.2). The family is the class over which the PAC guarantee of Theorem 21 is required.
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), §2.1, p.11 (PDF p.13); §2.2, p.13 (PDF p.15); Definition 4, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_QuerySampleRev_rStar
import Definitions.Def_QuerySampleRev_IsQuasiMHR

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev

/-- **The quasi-MHR family.** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue Maximization*
(manuscript, sha256 c31ea3d3…), §2.1, p.11 (PDF 13): "We consider value distributions supported on
`[0, ∞)`"; §2.2, p.13 (PDF 15): "We consider distributions with finite optimal revenue"; Definition 4,
p.12 (PDF 14) with `λ = 0` (quasi-MHR).

`InFamily μ`: `μ` is a probability measure on `ℝ` giving no mass to `(−∞, 0)`, it is quasi-MHR, and its
optimal revenue `r∗` is finite.

**Formalization Note.** A value distribution on `[0, ∞)` is encoded as a probability measure on `ℝ`
with `μ((−∞, 0)) = 0`. The finite-`r∗` clause is the standing assumption of §2.2. -/
def InFamily (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ μ (Set.Iio 0) = 0 ∧ IsQuasiMHR μ ∧ rStar μ ≠ ⊤

end QuerySampleRev


