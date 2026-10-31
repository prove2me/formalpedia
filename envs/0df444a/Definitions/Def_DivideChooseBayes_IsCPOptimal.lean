-- Prove2me | Definitions.Def_DivideChooseBayes_IsCPOptimal
-- name    : DivideChooseBayes_IsCPOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:27:07.328989+00:00
-- url     : https://prove2.me/theorems/b76d0a35-9552-4342-9a7a-5509c97eb523
-- title:
--   Optimal solution of $\mathcal C_P$
-- statement:
--   A point $q$ is an **optimal solution** of $\mathcal C_P$ if it is feasible for $\mathcal C_P$ and $u_P(q')\le u_P(q)$ for every feasible $q'$.
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Algorithm 1, line 5, p.9

import Mathlib
import Definitions.Def_DivideChooseBayes_cpObjective
import Definitions.Def_DivideChooseBayes_cpFeasibleSet

namespace DivideChooseBayes

/-- **Optimal solution of `C_P`.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Algorithm 1, line 5, p.9: "optimal solution to the following program `C_P`" (maximize
`u_P` over the feasible set). -/
def IsCPOptimal {ι : Type*} [Fintype ι] (gD m σ : ι → ℝ) (P : ℝ) (q : ι → ℝ) : Prop :=
  q ∈ cpFeasibleSet gD m σ P ∧
    ∀ q' ∈ cpFeasibleSet gD m σ P, cpObjective gD P q' ≤ cpObjective gD P q

end DivideChooseBayes


