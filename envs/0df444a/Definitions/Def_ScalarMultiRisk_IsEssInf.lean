-- Prove2me | Definitions.Def_ScalarMultiRisk_IsEssInf
-- name    : ScalarMultiRisk_IsEssInf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:29.308433+00:00
-- url     : https://prove2.me/theorems/fe3d61bd-c7ab-4e4f-84cc-8e84150f73bd
-- title:
--   Essential infimum of a family of extended random variables
-- statement:
--   A random variable $Z$ with values in $[-\infty,\infty]$ is the **essential infimum** of a family $(F_i)_{i\in I}$ when $-Z$ is the essential supremum of $(-F_i)_{i\in I}$. Equivalently, $Z$ is an a.s. lower bound of the family and a.s. above every other a.s. lower bound.
--
--   This is the form in which $\mathbb K_t$-compatibility and the primal representations are stated.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, Definition 3.1, p.7, and Corollary 4.10, p.22

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup

open MeasureTheory

namespace ScalarMultiRisk

/-- **Essential infimum of a family of extended random variables.** `Z` is the essential
infimum of `F` when `-Z` is the essential supremum of `-F`.

**Formalization Note.** The essential infima of the paper (Definition 3.1, p.7; Corollary 4.10,
p.22) are stated through the published `CondConvexRisk.Representation.IsEssSup`, which also
requires `Z` to be `P`-a.e. measurable: that is the paper's `L⁰` setting. -/
def IsEssInf {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ι → Ω → EReal)
    (Z : Ω → EReal) : Prop :=
  CondConvexRisk.Representation.IsEssSup P (fun i ω => -F i ω) fun ω => -Z ω

end ScalarMultiRisk


