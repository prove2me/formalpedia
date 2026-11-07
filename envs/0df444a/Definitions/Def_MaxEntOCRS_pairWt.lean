-- Prove2me | Definitions.Def_MaxEntOCRS_pairWt
-- name    : MaxEntOCRS_pairWt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:24.072874+00:00
-- url     : https://prove2.me/theorems/70760d33-05b7-4799-b149-709acb208f7e
-- title:
--   Aggregated activity $\sum_{e = ab} t_e$ between two vertices
-- statement:
--   For vertices $a, b$ of a multigraph with activities $t$, the aggregated activity of the (possibly parallel) edges joining them is $\sum_{e = ab} t_e$. Section 3 uses it as
--   $$
--   a_i = \sum_{e = uy_i} t_e, \qquad b_i = \sum_{e = vy_i} t_e, \qquad w = \sum_{e = uv} t_e .
--   $$
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 3, p.5

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace MaxEntOCRS

open Classical in
/-- The aggregated activity `∑_{e = ab} t_e` of all (parallel) edges joining `a` and `b`
(Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §3, p.5: `a_i = ∑_{e=uy_i} t_e`, `b_i = ∑_{e=vy_i} t_e`, `w = ∑_{e=uv} t_e`). -/
noncomputable def pairWt {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (a b : V) : ℝ :=
  ∑ e ∈ Finset.univ.filter (fun e => G.ends e = s(a, b)), t e

end MaxEntOCRS


