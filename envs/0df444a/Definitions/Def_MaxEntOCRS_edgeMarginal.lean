-- Prove2me | Definitions.Def_MaxEntOCRS_edgeMarginal
-- name    : MaxEntOCRS_edgeMarginal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:31:15.193859+00:00
-- url     : https://prove2.me/theorems/c6b1629c-37c3-4e8a-9049-162262983995
-- title:
--   Edge marginal $\Pr_\mu(e \in M)$
-- statement:
--   The **marginal** of an edge $e$ under a weight function $\mu$ on edge sets is $\Pr_\mu(e \in M) = \sum_{M \ni e} \mu(M)$. A distribution on matchings has marginals $q$ if $\Pr_\mu(e\in M) = q_e$ for every edge $e$.
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Section 2, p.4 (distributions with marginals α′x)

import Mathlib
import Definitions.Def_MaxEntOCRS_prob

namespace MaxEntOCRS

/-- The edge marginal `Pr_μ(e ∈ M)` (Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), §2, p.4: "distributions on M(G) with marginals α′x"). -/
noncomputable def edgeMarginal {E : Type} [Fintype E] (μ : Finset E → ℝ) (e : E) : ℝ :=
  prob μ (fun M => e ∈ M)

end MaxEntOCRS


