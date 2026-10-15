-- Prove2me | Definitions.Def_OAI_Probability_Ising_Main
-- name    : OAI_Probability_Ising_Main
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T22:11:13.854895+00:00
-- url     : https://prove2.me/theorems/4ebfa52b-74bd-4f07-8927-8dd20984d171
-- title:
--   Oriented coupling matrix of a finite edge-list graph
-- statement:
--   Let $G$ be a finite ferromagnetic graph on $V=\{0,\dots,n-1\}$ given by an edge list: edge $e$ has an ordered pair of endpoints $(l(e),r(e))$ with $l(e)\neq r(e)$ and a coupling $K_e\ge0$, and parallel edges are allowed. Its oriented coupling matrix is
--
--   $$J^G_{uv}=\sum_{e:\ l(e)=u,\ r(e)=v}K_e\qquad(u,v\in V).$$
--
--   Each edge contributes once, in its own orientation, and parallel edges with the same orientation are summed; all entries are nonnegative and the diagonal vanishes because there are no loops. With this matrix the matrix-form Hamiltonian $\sum_{u,v}J^G_{uv}\sigma_u\sigma_v+\sum_uh_u\sigma_u$ coincides with the edge-list energy $\sum_eK_e\sigma_{l(e)}\sigma_{r(e)}+\sum_vh_v\sigma_v$ for every field $h$, so the Gibbs weights and expectations of the two presentations agree exactly, with no auxiliary vertices and no change of the field. This is how results proved for coupling arrays, such as the influence bound and the covariance bound, are transferred to finite graphs.
--
--   **Formalization Note** The Lean name is `dssMatrix G u v`, written as a sum over all edge indices of nested conditionals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Main.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Main.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BufferedIsing mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic
import Definitions.Def_OAI_Probability_Ising_Colorings
import Definitions.Def_OAI_Probability_Ising_EdwardsSokal
import Definitions.Def_OAI_Probability_Ising_TwoSpin
import Definitions.Def_OAI_Probability_Ising_SpinCorrelation
import Definitions.Def_OAI_Probability_Ising_Marginals
import Definitions.Def_OAI_Probability_Ising_PinnedMarginal
import Definitions.Def_OAI_Probability_Ising_Covariance
import Definitions.Def_OAI_Probability_Ising_Contraction
import Definitions.Def_OAI_Probability_Ising_GibbsMeasure
import Definitions.Def_OAI_Probability_Ising_Interpolation
import Definitions.Def_OAI_Probability_Ising_FieldUpdate
import Definitions.Def_OAI_Probability_Ising_Influence

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

noncomputable section

/-- The oriented pair matrix is precisely the original edge-list interaction;
parallel edges are summed, with no ghost and no change to the field. -/
def dssMatrix {n m : ℕ} (G : FiniteGraph n m) (u v : Fin n) : ℝ :=
  ∑ e, if G.left e = u then if G.right e = v then G.coupling e else 0 else 0

end

end BufferedIsing

end OAI


