-- Prove2me | Definitions.Def_BauerleRiederMDP_LPDuality_gridOp
-- name    : BauerleRiederMDP_LPDuality_gridOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:30:06.385318+00:00
-- url     : https://prove2.me/theorems/b4643256-f53f-412e-a591-a4bae13fb223
-- title:
--   Grid operator $\mathcal T_G$
-- statement:
--   Given a grid scheme on $E$, the **grid operator** is
--   $$
--   \mathcal T_Gv(x):=\begin{cases} \mathcal Tv(x), & x\in G,\\ \sum_k\lambda_k\,\mathcal Tv(x_k), & x\notin G,\ x=\sum_k\lambda_kx_k,\ x_k\in G,\ \lambda_k\ge0,\ \sum_k\lambda_k=1,\end{cases}
--   $$
--   where $\mathcal T$ is the maximal reward operator. $\mathcal T_G$ coincides with $\mathcal T$ on $G$ and is a linear interpolation elsewhere; value iteration on the grid computes the iterates $\mathcal T_G^ng$.
--
--   **Formalization Note** Both cases are the single formula $\sum_y\lambda_y(x)\,\mathcal Tv(y)$. $\mathcal T$ is the real operator `bellmanOpReal`. The operator is defined on all real functions; the mission applies it to $g\in I\!M_c$ and its iterates.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §7.5.3, p.221 (PDF 232), definition of T_G

import Mathlib
import Definitions.Def_MDPFinance_LPDuality_Model
import Definitions.Def_BauerleRiederMDP_LPDuality_GridScheme
import Definitions.Def_BauerleRiederMDP_LPDuality_bellmanOpReal

open MeasureTheory ProbabilityTheory MDPFinance.LPDuality

namespace BauerleRiederMDP.LPDuality

/-- The grid operator (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), §7.5.3, p.221, PDF 232): `T_G v(x) := T v(x)` for `x ∈ G` and
`T_G v(x) := ∑_k λ_k T v(x_k)` for `x ∉ G, x = ∑_k λ_k x_k`, i.e. `T_G` coincides with `T` on the
grid and interpolates linearly elsewhere.

**Formalization Note** Both cases are the single formula `∑_y λ_y(x) T v(y)` (the weights of a grid
point are the point mass at it). `T` is the real maximal reward operator `bellmanOpReal`. -/
noncomputable def gridOp {V A : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] [MeasurableSpace A] {S : Set V} (M : MarkovDecisionModel S A)
    (sch : GridScheme S) (v : S → ℝ) (x : S) : ℝ :=
  (sch.wt x).sum fun y c => c * bellmanOpReal M v y

end BauerleRiederMDP.LPDuality


