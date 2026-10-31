-- Prove2me | Definitions.Def_ScalarMultiRisk_essSupE
-- name    : ScalarMultiRisk_essSupE
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:42.401733+00:00
-- url     : https://prove2.me/theorems/51715db3-abdc-44cc-b959-84628b803abb
-- title:
--   A version of the essential supremum, as a function
-- statement:
--   Given a family $(F_i)_{i\in I}$ of extended random variables, $\operatorname{ess\,sup}_{i}F_i$ denotes a chosen version of its essential supremum.
--
--   It lets the penalty $\beta_t(\mathbb Q,S)$ and the risk measure $\pi^S_t(X)$ be written as functions.
--
--   **Formalization Note** The essential supremum of an a.e.-measurable family exists and is a.e. unique, so the choice is immaterial, and the fallback value $+\infty$ is never reached by the families of this mission.
-- source:
--   Feinstein, Rudloff, Scalar multivariate risk measures with a single eligible asset, arXiv:1807.10694v5, (4.4), p.18

import Mathlib
import Definitions.Def_CondConvexRisk_Representation_EssSup

open MeasureTheory

namespace ScalarMultiRisk

open Classical in
/-- **The essential supremum as a function.** A version of the essential supremum of `F`.

**Formalization Note.** `IsEssSup` is a predicate; to write `π^S_t(X)` and `β_t(ℚ,S)` as
functions one version is chosen. Essential suprema of a.e.-measurable families exist and are
a.e. unique, and every family below is a.e. measurable, so the junk branch `⊤` is never used
and every statement, being up to a.e. equality, is independent of the chosen version. -/
noncomputable def essSupE {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ι → Ω → EReal) : Ω → EReal :=
  if h : ∃ Z : Ω → EReal, CondConvexRisk.Representation.IsEssSup P F Z then h.choose
  else fun _ => ⊤

end ScalarMultiRisk


