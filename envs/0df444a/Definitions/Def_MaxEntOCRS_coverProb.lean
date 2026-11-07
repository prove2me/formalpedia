-- Prove2me | Definitions.Def_MaxEntOCRS_coverProb
-- name    : MaxEntOCRS_coverProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:28.633169+00:00
-- url     : https://prove2.me/theorems/dfa8af3d-5922-4e19-80a7-1730a0f6e778
-- title:
--   Covering probability $m_z$
-- statement:
--   For a distribution $\mu$ on the matchings of $G$ and a vertex $z$, the **covering probability** $m_z = \Pr_\mu(z \text{ is covered})$ is the probability that some edge of the matching contains $z$.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_prob
import Definitions.Def_MaxEntOCRS_Covers

namespace MaxEntOCRS

/-- The covering probability `m_z = Pr_μ(z is covered)` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4). -/
noncomputable def coverProb {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (μ : Finset E → ℝ) (z : V) : ℝ :=
  prob μ (fun M => Covers G M z)

end MaxEntOCRS


