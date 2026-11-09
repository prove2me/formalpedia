-- Prove2me | Definitions.Def_HybridXorLift_pathProb
-- name    : HybridXorLift_pathProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:16:23.230843+00:00
-- url     : https://prove2.me/theorems/b7230e00-8aff-4ec1-b88c-8cbc86ef95f6
-- title:
--   Path probability $|c_h(x)|^2$
-- statement:
--   The probability that a parallel hybrid algorithm run on input $x$ follows the history $h$ is
--   $$
--   \Pr_x[h] = |c_h(x)|^2 ,
--   $$
--   the product of the outcome probabilities $|a_{v,y}(x)|^2$ along the path (3.2). On terminal histories it is the law of the terminal transcript on input $x$.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), §3.1, Eq. (3.2), p.11 (PDF p.13)

import Definitions.Def_HybridXorLift_ParallelHybridAlg_ampl

namespace HybridXorLift

/-- The probability `Pr_x[h] = |c_h(x)|²` that the algorithm on input `x` follows the path `h`
(Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), §3.1, Eq. (3.2), p.11 (PDF p.13)): the product of the outcome probabilities
`|a_{h,y}(x)|²` along the path. On a terminal history it is the probability of that terminal
transcript. -/
noncomputable def pathProb {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type}
    (A : ParallelHybridAlg ι α) (x : ι → Bool) (h : List (Step ι)) : ℝ :=
  ‖A.ampl x h‖ ^ 2

end HybridXorLift


