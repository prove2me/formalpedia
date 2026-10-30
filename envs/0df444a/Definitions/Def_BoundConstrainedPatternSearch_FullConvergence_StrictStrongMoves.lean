-- Prove2me | Definitions.Def_BoundConstrainedPatternSearch_FullConvergence_StrictStrongMoves
-- name    : BoundConstrainedPatternSearch_FullConvergence_StrictStrongMoves
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:39:55.92626+00:00
-- url     : https://prove2.me/theorems/116a1813-b4df-4ac8-ae06-629383fc6db4
-- title:
--   Strict Strong Hypotheses on Bound Constrained Exploratory Moves
-- statement:
--   Let $B,C_k=[\Gamma_k\;L_k],x_k,\Delta_k,s_k$ be pattern-search data and let $\Omega=\{x:\ell\le x\le u\}$. At every iteration the selected step is an actual column of $\Delta_k BC_k$ and $x_k+s_k\in\Omega$. If any feasible core column strictly improves $f(x_k)$, require
--
--   $$
--   f(x_k+s_k)<f(x_k+y)\quad\text{for every feasible column }y\text{ of }\Delta_k B\Gamma_k.
--   $$
--
--   These are all three printed Strong Hypotheses. For a nonempty finite feasible core the comparison is precisely strict comparison with its minimum. With no feasible core column the trigger is false. The canonical weak-run predicate supplies the remaining algorithm and mesh-update rules. This predicate deliberately preserves the source's strict comparison, independently of the published non-strict StrongHyp predicate.
-- source:
--   Lewis and Torczon, Pattern Search Algorithms for Bound Constrained Minimization, ICASE Report 96-20, March 1996, printed p. 7 (PDF p. 9), Strong Hypotheses on Bound Constrained Exploratory Moves

import Mathlib
import Definitions.Def_LewisTorczon_BoundPS_GPS
open LewisTorczon.BoundPS

namespace BoundConstrainedPatternSearch.FullConvergence

/-- All three printed Strong Hypotheses (printed p. 7). The third uses the
literal strict comparison. The existential trigger avoids an empty real minimum.
The first two clauses also occur in the canonical weak-run predicate. -/
def StrictStrongMoves {n m : ℕ} (P : GPSParams n) (lo hi : Fin n → EReal)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (R : GPSRun n m) : Prop :=
  ∀ k,
    (∃ c ∈ cols R k, R.s k = stepOf P (R.Δ k) c) ∧
    R.x k + R.s k ∈ box lo hi ∧
    ((∃ c ∈ coreCols R k, R.x k + stepOf P (R.Δ k) c ∈ box lo hi ∧
        f (R.x k + stepOf P (R.Δ k) c) < f (R.x k)) →
      ∀ c ∈ coreCols R k, R.x k + stepOf P (R.Δ k) c ∈ box lo hi →
        f (R.x k + R.s k) < f (R.x k + stepOf P (R.Δ k) c))

end BoundConstrainedPatternSearch.FullConvergence


