-- Prove2me | Definitions.Def_DiscreteConvex_NetworkFlowsB_FeasibleFlowMCFP3
-- name    : DiscreteConvex_NetworkFlowsB_FeasibleFlowMCFP3
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T02:23:31.623538+00:00
-- url     : https://prove2.me/theorems/9d9ab9bd-8dab-4a97-a803-c82f596e5bd4
-- title:
--   FeasibleFlowMCFP3
-- statement:
--   Feasibility for the minimum cost flow problem MCFP3 / the M-convex submodular flow problem MSFP3.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.246-247, Eqs. (9.7)-(9.9).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.246-247, Eqs. (9.7)-(9.9)

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsB_Boundary

namespace DiscreteConvex.NetworkFlowsB

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Feasibility for the (nonlinear-cost) minimum cost flow problem MCFP3 / the M-convex
submodular flow problem MSFP3. -/
def FeasibleFlowMCFP3 (tail head : A → V) (fa : A → ℝ → WithTop ℝ) (f : (V → ℝ) → WithTop ℝ)
    (xi : A → ℝ) : Prop :=
  (∀ a : A, fa a (xi a) ≠ ⊤) ∧ f (Boundary tail head xi) ≠ ⊤

end DiscreteConvex.NetworkFlowsB


