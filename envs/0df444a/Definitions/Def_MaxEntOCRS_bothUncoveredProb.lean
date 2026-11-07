-- Prove2me | Definitions.Def_MaxEntOCRS_bothUncoveredProb
-- name    : MaxEntOCRS_bothUncoveredProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:27.843257+00:00
-- url     : https://prove2.me/theorems/aef4939c-6b5b-43b6-b155-5c075e170d53
-- title:
--   Joint vacancy probability $\Pr_\mu(u, v \text{ both uncovered})$
-- statement:
--   For a distribution $\mu$ on the matchings of $G$ and vertices $u, v$, this is the probability $\Pr_\mu(u \text{ and } v \text{ are both uncovered})$ that no edge of the matching contains $u$ and none contains $v$. Theorem 2 bounds it below by $\alpha$.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Theorem 2, p.2

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_prob
import Definitions.Def_MaxEntOCRS_Covers

namespace MaxEntOCRS

/-- `Pr_μ(u and v are both uncovered)` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), Theorem 2, p.2). -/
noncomputable def bothUncoveredProb {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (μ : Finset E → ℝ) (u v : V) : ℝ :=
  prob μ (fun M => ¬ Covers G M u ∧ ¬ Covers G M v)

end MaxEntOCRS


