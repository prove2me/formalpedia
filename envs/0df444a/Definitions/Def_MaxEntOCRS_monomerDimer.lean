-- Prove2me | Definitions.Def_MaxEntOCRS_monomerDimer
-- name    : MaxEntOCRS_monomerDimer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:32:39.455856+00:00
-- url     : https://prove2.me/theorems/9eb0f71b-6b99-4c21-bf91-cd2833555c41
-- title:
--   Monomer–dimer (Gibbs) measure $\mu(M) = Z(G)^{-1}\prod_{e\in M} t_e$
-- statement:
--   The **monomer–dimer measure** of a finite loopless multigraph $G$ with nonnegative activities $(t_e)_{e \in E}$ is the distribution on matchings
--   $$
--   \mu(M) = Z(G)^{-1} \prod_{e \in M} t_e , \qquad M \in \mathcal M(G),
--   $$
--   where $Z(G)$ is the partition function. Theorem 2 is a statement about these measures.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_mdWeight
import Definitions.Def_MaxEntOCRS_partitionFn

namespace MaxEntOCRS

/-- The monomer–dimer (Gibbs) measure `μ(M) = Z(G)⁻¹ ∏_{e ∈ M} t_e` on the matchings of `G`
with activities `t` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4). -/
noncomputable def monomerDimer {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) : Finset E → ℝ :=
  fun M => mdWeight G t M / partitionFn G t

end MaxEntOCRS


