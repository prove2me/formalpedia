-- Prove2me | Definitions.Def_FoundationsRL_E2DStructured_lowerConf
-- name    : FoundationsRL_E2DStructured_lowerConf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:19:58.907986+00:00
-- url     : https://prove2.me/theorems/b5fb48b6-21bb-444c-814b-9c6432ed331f
-- title:
--   The lower confidence function $\underline f^t$
-- statement:
--   The lower confidence function of a class $\mathcal F^t$ is
--   $$\underline f^t(\pi)=\min_{f\in\mathcal F^t}f(\pi).$$
--   The difference $\bar f^t-\underline f^t$ is the confidence width.
--
--   **Formalization Note** The minimum is read as a real infimum; the statements using it assume the values bounded below.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, §4.4.1, (4.27), p. 76

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace FoundationsRL.E2DStructured

/-- The lower confidence function `f̲^t(π) = min_{f∈F^t} f(π)` of a class
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, §4.4.1, p. 76, (4.27)).

**Formalization Note.** `min` is read `inf`; every statement that uses it assumes the pointwise values
bounded below, so the real `sInf` is genuine. -/
noncomputable def lowerConf {D : Type*} (G : Set (D → ℝ)) (π : D) : ℝ :=
  sInf ((fun f : D → ℝ => f π) '' G)

end FoundationsRL.E2DStructured


