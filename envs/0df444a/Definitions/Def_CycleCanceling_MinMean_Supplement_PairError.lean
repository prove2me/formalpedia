-- Prove2me | Definitions.Def_CycleCanceling_MinMean_Supplement_PairError
-- name    : CycleCanceling_MinMean_Supplement_PairError
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:19:59.005147+00:00
-- url     : https://prove2.me/theorems/680660d9-5164-464e-92f5-3087b9ea9907
-- title:
--   Fixed-price error of a circulation
-- statement:
--   Let $N$ be a finite circulation network, $f$ a real arc flow and $p$ real vertex prices. The fixed-price error is
--
--   $$\varepsilon(f,p)=\max\bigl(\{0\}\cup\{-c_p(v,w):(v,w)\in E,\ u(v,w)-f(v,w)>0\}\bigr).$$
--
--   It is the least nonnegative error satisfying all relaxed optimality constraints at these particular prices. This is the progress quantity of cancel-and-tighten; unlike $\varepsilon(f)$, it does not optimize over prices.
--
--   **Formalization Note** The finite maximum includes zero, so its defining set is nonempty even when no arc is residual, in which case the value is zero. No infimum or default for an unbounded set is used.
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, https://doi.org/10.1145/76359.76368, p. 880, Section 4, definition of ε(f,p)

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_EpsOptimal

namespace CycleCanceling.MinMean.Supplement

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Section 4, p. 880: ε(f,p), as the finite maximum of 0 and all negative
reduced costs of residual arcs. The inserted zero also covers an empty residual graph. -/
noncomputable def pairError (N : CircNetwork V) (f : V → V → ℝ)
    (p : V → ℝ) : ℝ := by
  classical
  exact (insert 0 ((N.E.filter (fun a => 0 < resCap N f a.1 a.2)).image
    (fun a => -reducedCost N p a.1 a.2))).max'
      (Finset.insert_nonempty _ _)

end CycleCanceling.MinMean.Supplement


