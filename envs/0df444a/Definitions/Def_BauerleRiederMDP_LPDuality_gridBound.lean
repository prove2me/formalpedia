-- Prove2me | Definitions.Def_BauerleRiederMDP_LPDuality_gridBound
-- name    : BauerleRiederMDP_LPDuality_gridBound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:55.276921+00:00
-- url     : https://prove2.me/theorems/b5efeb66-ca44-48ae-a13c-9cdd23029b5e
-- title:
--   Grid bounding function $b_G$
-- statement:
--   Given a grid scheme on $E$ and a bounding function $b$, the **grid bounding function** is
--   $$
--   b_G(x):=\begin{cases} b(x), & x\in G,\\ \sum_k\lambda_k b(x_k), & x\notin G,\ x=\sum_k\lambda_kx_k,\ x_k\in G,\ \lambda_k\ge0,\ \sum_k\lambda_k=1.\end{cases}
--   $$
--   It defines the weighted norm $\|\cdot\|_G$ and the module $\alpha_G$ of the grid operator.
--
--   **Formalization Note** Both cases are the single formula $\sum_y\lambda_y(x)\,b(y)$, because the weights of a grid point are the point mass at it.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §7.5.3, p.221 (PDF 232), definition of b_G

import Mathlib
import Definitions.Def_BauerleRiederMDP_LPDuality_GridScheme

open MeasureTheory ProbabilityTheory

namespace BauerleRiederMDP.LPDuality

/-- The grid bounding function (Bäuerle & Rieder, *Markov Decision Processes with Applications to
Finance* (2011), §7.5.3, p.221, PDF 232): `b_G(x) := b(x)` for `x ∈ G` and
`b_G(x) := ∑_k λ_k b(x_k)` for `x ∉ G, x = ∑_k λ_k x_k`.

**Formalization Note** Both cases are the single formula `∑_y λ_y(x) b(y)`, since the weights of a
grid point are the point mass at it (`GridScheme.on_grid`). -/
noncomputable def gridBound {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace V] {S : Set V} (sch : GridScheme S) (b : S → ℝ) (x : S) : ℝ :=
  (sch.wt x).sum fun y c => c * b y

end BauerleRiederMDP.LPDuality


