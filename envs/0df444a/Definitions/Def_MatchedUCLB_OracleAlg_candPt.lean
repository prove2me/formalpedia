-- Prove2me | Definitions.Def_MatchedUCLB_OracleAlg_candPt
-- name    : MatchedUCLB_OracleAlg_candPt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:31:43.153955+00:00
-- url     : https://prove2.me/theorems/e5025edc-3378-484d-8908-c07d45ab510e
-- title:
--   The candidate solution $\hat x_s$ after $s$ oracle calls
-- statement:
--   For a deterministic $p$th-order oracle algorithm $\mathcal A$ run on $F$, the **candidate solution after $s$ calls** is $\hat x_s=\hat{\mathcal A}_s(H_s)$, the candidate map applied to the history $H_s$ of the run. For $s=0$ it is the candidate $\hat x_0$ chosen before any oracle call.
-- source:
--   Bai, Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity, arXiv:2611.05527, Eq. (F.2), p.98; Definition B.1, p.17

import Mathlib
import Definitions.Def_MatchedUCLB_OracleAlg_hist

namespace MatchedUCLB

/-- **The candidate solution after `s` oracle calls.** Bai, *Tight Lower Bounds under Matched High-Order Hölder Smoothness and Uniform Convexity*, arXiv:2611.05527, (F.2), p.98: `x̂_s = Â_s(H_s)`;
Definition B.1, p.17 (a candidate `x̂_0` before the first call is allowed).

`A.candPt F s` is the candidate solution `x̂_s` that `A` outputs after `s` oracle calls on `F`. -/
noncomputable def OracleAlg.candPt {d p : ℕ} (A : OracleAlg d p) (F : EuclideanSpace ℝ (Fin d) → ℝ) (s : ℕ) : EuclideanSpace ℝ (Fin d) :=
  A.cand s (A.hist F s)

end MatchedUCLB


