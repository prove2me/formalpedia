-- Prove2me | Definitions.Def_MaxEntOCRS_mdWeight
-- name    : MaxEntOCRS_mdWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:30:22.277634+00:00
-- url     : https://prove2.me/theorems/ebf76c72-4968-4a89-9748-cfaa413e2eb5
-- title:
--   Monomer–dimer weight $\prod_{e\in M} t_e$ of a matching
-- statement:
--   For a finite loopless multigraph $G$ with activities $t \in \mathbb R^E$, the **monomer–dimer weight** of an edge set $M$ is $\prod_{e \in M} t_e$ if $M$ is a matching and $0$ otherwise.
--
--   **Formalization Note** Nonnegativity of the activities is not built in; every theorem assumes $t \ge 0$.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph

namespace MaxEntOCRS

open Classical in
/-- The monomer–dimer weight `∏_{e ∈ M} t_e` of a matching `M`, and `0` for a non-matching
(Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4). Nonnegativity of the activities is a hypothesis of every theorem, not part of
this definition. -/
noncomputable def mdWeight {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ) (M : Finset E) : ℝ :=
  if EdmondsMatching65.Polyhedron.IsMatching G M then ∏ e ∈ M, t e else 0

end MaxEntOCRS


