-- Prove2me | Definitions.Def_ConstrainedCorrelationRepulsion_Main_Supplement_MustLinks
-- name    : ConstrainedCorrelationRepulsion_Main_Supplement_MustLinks
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:05:01.56181+00:00
-- url     : https://prove2.me/theorems/4bfe7e7c-6ed2-48ae-998c-23c8d80c69db
-- title:
--   Uniform polynomial approximation on the must-link-only domain
-- statement:
--   For a ratio $r$, the must-link-only approximation predicate asserts the existence of one finite randomized program and positive natural constants $C,d$ that work for every vertex count $n$ and every feasible complete unweighted instance $I$ whose cannot-link graph is empty. It requires the published operational guarantee
--
--   $$\mathbb E[\operatorname{cost}_I(P)]\le r\operatorname{OPT}(I),\qquad T\le C\max\{2,n\}^d.$$
--
--   Every supported output is feasible, including on empty and singleton inputs. Runtime is charged by the existing fair-coin bit-cost interpreter; neither an optimal partition nor an arbitrary good-output distribution is an input. Must-links and signs are unrestricted. The condition is $H=\varnothing$, rather than the existing only-cannot-links flag, which instead enforces $M=\varnothing$.
--
--   Differences from the source:
--   - encoding: randomized polynomial-time approximation with must-links only → the published operational approximation predicate uniformly over $H=\varnothing$; reason: feasibility holds for every supported output and all polynomial constants precede the inputs.
-- source:
--   Yixin Cao, Ying Xu, STOC 2027 submission #869 (October 2026), Theorem 1.5, printed pp.2, 16 (PDF pp.3, 17)

import Definitions.Def_ConstrainedCorrelationRepulsion_Main_Algorithm

namespace ConstrainedCorrelationRepulsion.Main.Supplement

/-- The H-empty domain. One finite fair-coin bit-cost program and one polynomial work on
all feasible inputs; no bound on must-link components, n, signs or accuracy is imposed. -/
def MustLinkApproximation (ratio : ℝ) : Prop :=
  ∃ code : Program, ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
    ∀ n (I : Instance n), FeasibleInput I → I.cannotLink = ⊥ →
      Approximates code I ratio (polynomialBound C d n)

end ConstrainedCorrelationRepulsion.Main.Supplement


