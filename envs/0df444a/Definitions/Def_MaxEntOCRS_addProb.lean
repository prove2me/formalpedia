-- Prove2me | Definitions.Def_MaxEntOCRS_addProb
-- name    : MaxEntOCRS_addProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:24.251771+00:00
-- url     : https://prove2.me/theorems/63077f11-6439-4b1b-935b-e9edceddfd10
-- title:
--   Addability probability $\Pr_\mu[\mathrm{Add}(e)]$
-- statement:
--   For an edge $e$ of a finite loopless multigraph $G$, $\mathrm{Add}(e)$ is the event that $(M \setminus \{e\}) \cup \{e\}$ is a matching of $G$. This definition gives
--   $$
--   \Pr_\mu[\mathrm{Add}(e)] = \sum_{M :\ (M\setminus\{e\})\cup\{e\} \in \mathcal M(G)} \mu(M).
--   $$
--   The template is $\alpha'$-selectable when $\Pr_{\mu^*}[\mathrm{Add}(e)] \ge \alpha'$ for every edge.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_prob

namespace MaxEntOCRS

/-- `Pr_μ[Add(e)]`, where `Add(e)` is the event that `(M ∖ {e}) ∪ {e}` is a matching
(Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4). -/
noncomputable def addProb {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (μ : Finset E → ℝ) (e : E) : ℝ :=
  prob μ (fun M => EdmondsMatching65.Polyhedron.IsMatching G (insert e (M.erase e)))

end MaxEntOCRS


