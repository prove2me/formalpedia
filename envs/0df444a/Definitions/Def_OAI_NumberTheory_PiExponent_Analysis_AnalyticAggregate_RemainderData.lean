-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
-- name    : OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-11T20:05:57.341822+00:00
-- url     : https://prove2.me/theorems/04008248-130e-40ba-b6a3-df3e9b9df91b
-- title:
--   Original collision and translation remainders for analytic aggregation
-- statement:
--   Define $r=\exp(-\log 2/2)$, the collision remainder $C(M,H)=(\log M+\log 2/4-\log(1-r))/H$, and the translation term count $T(m,v,H)=(\lfloor H\rfloor_{\mathbb N}+1)^{2m}(\lfloor H/v\rfloor_{\mathbb N}+1)$. For the original fixed admissible data $d$ with row count $M_d(H)$, define
--
--   $$R_d(H)=C(M_d(H),H)+\frac{\log T(d.m,d.v_0,H)}{H}.$$
--
--   Here $M,m$ are natural numbers and $v,H$ are real. The natural floor is the original source operation; the definitions impose no positivity hypotheses and assert no convergence or determinant estimate. These exact quantities state the two immediate original children of the analytic aggregate theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticAggregate.lean#L49-L51

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData


namespace OAI.PiExponent.Collision

open scoped BigOperators

noncomputable def collisionRatio : ℝ := Real.exp (-Real.log 2 / 2)

end OAI.PiExponent.Collision

namespace OAI.PiExponent.Collision

open scoped BigOperators

noncomputable def collisionRemainder (M : ℕ) (H : ℝ) : ℝ :=
  (Real.log M + Real.log 2 / 4 - Real.log (1 - collisionRatio)) / H

end OAI.PiExponent.Collision

namespace OAI.PiExponent

open Filter Topology

noncomputable def translationTermCount (m : ℕ) (v H : ℝ) : ℕ :=
  (⌊H⌋₊ + 1) ^ (2 * m) * (⌊H / v⌋₊ + 1)

end OAI.PiExponent

namespace OAI.PiExponent.LiteralAnalytic

open scoped BigOperators Topology
open Filter
open DeterminantContradiction

noncomputable def analyticRemainder {nu : ℝ} (d : FixedData nu) (H : ℝ) : ℝ :=
  Collision.collisionRemainder (actualRowCount d H) H +
    Real.log (translationTermCount d.m d.v0 H : ℝ) / H

end OAI.PiExponent.LiteralAnalytic


