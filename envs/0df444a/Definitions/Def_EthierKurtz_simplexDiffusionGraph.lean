-- Prove2me | Definitions.Def_EthierKurtz_simplexDiffusionGraph
-- name    : EthierKurtz_simplexDiffusionGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:16:44.646907+00:00
-- url     : https://prove2.me/theorems/82098d19-9775-4025-a606-384590681d0d
-- title:
--   C² diffusion graph on the simplex
-- statement:
--   The graph in C(K_d)×C(K_d) consisting of restrictions of globally twice continuously differentiable functions paired with their simplex diffusion-operator images.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 2, Theorem 2.8, printed p. 375 (PDF p. 384), with the closed-convex-set C² extension convention in Appendix 6, printed pp. 499–500 (PDF pp. 508–509).

import Definitions.Def_EthierKurtz_WFState
import Definitions.Def_EthierKurtz_simplexDiffusionOperator

open Filter
open scoped Topology BigOperators ContDiff NNReal
namespace EthierKurtz

/-- The full C²(K_d) graph in the product uniform norm. Appendix 6,
Theorem 6.1 and Corollary 6.3 permit global C² extensions from the simplex.
All continuous functions on this compact state space are bounded. -/
def simplexDiffusionGraph {d : ℕ} (b : WFState d → Fin d → ℝ) :
    Set (BoundedContinuousFunction (WFState d) ℝ ×
      BoundedContinuousFunction (WFState d) ℝ) :=
  {fg | ∃ f : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 f ∧
    (∀ x, fg.1 x = f x.val) ∧
    (∀ x, fg.2 x = simplexDiffusionOperator b f x)}

end EthierKurtz


