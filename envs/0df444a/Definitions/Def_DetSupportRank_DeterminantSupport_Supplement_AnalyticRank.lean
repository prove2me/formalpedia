-- Prove2me | Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_AnalyticRank
-- name    : DetSupportRank_DeterminantSupport_Supplement_AnalyticRank
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:07:37.163204+00:00
-- url     : https://prove2.me/theorems/bf59231a-f849-4a09-af7b-b432cf69c91d
-- title:
--   Logarithmic analytic rank with an explicit infinite boundary
-- statement:
--   For a function $T:A\to F_q$ on a finite set and a finite field of cardinality $q$, define
--   $$\operatorname{AR}(T)=-\frac{\log\operatorname{bias}(T)}{\log q}$$
--   when the bias is positive, and give nonpositive bias the value $+\infty$. This extended-real convention prevents a finite rank bound from arising through a total logarithm at zero. On the multilinear source domain of positive degree the bias is positive; that fact is not assumed as an extra hypothesis. Field nontriviality ensures $q>1$.
-- source:
--   Neil Krishnan, Guy Moshkovitz, Optimal partition rank bounds for the determinant and other multilinear polynomials, STOC 2027 submission #631 (October 2026), §1, definition of analytic rank, p. 2 (PDF p. 2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/631.pdf

import Definitions.Def_DetSupportRank_DeterminantSupport_Supplement_UniformBias

noncomputable section
open scoped BigOperators

namespace DetSupportRank.DeterminantSupport.Supplement

/-- The actual -log_q(bias), §1, p.2. Nonpositive bias is assigned +∞,
so a finite upper bound cannot come from Lean's total log at zero. -/
def analyticRank {A F : Type*} [Fintype A] [Field F] [Fintype F] (T : A → F) : EReal :=
  if 0 < uniformBias T then
    ((-Real.log (uniformBias T) / Real.log (Fintype.card F : ℝ)) : ℝ)
  else ⊤
end DetSupportRank.DeterminantSupport.Supplement


