-- Prove2me | Definitions.Def_RGGDetect_erLaw
-- name    : RGGDetect_erLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:37:54.922164+00:00
-- url     : https://prove2.me/theorems/c1dc0889-b7a7-4973-92ff-8c287dfec289
-- title:
--   The Erdős–Rényi law $P_{\mathrm{ER}}=G(n,p)$
-- statement:
--   The **Erdős–Rényi graph** $G(n,p)$ on $[n]$ includes every pair $\{i,j\}$, $i\ne j$, as an edge independently with probability $p$. Its law gives a graph $G$ with edge set $E(G)$ the mass
--
--   $$
--   P_{\mathrm{ER}}(G)=\prod_{\{i,j\}}p^{\mathbf 1\{ij\in E(G)\}}(1-p)^{\mathbf 1\{ij\notin E(G)\}}=p^{|E(G)|}(1-p)^{\binom n2-|E(G)|}.
--   $$
--
--   It is the null model against which the random geometric graph is compared.
--
--   **Formalization Note** The law is the finite sum $\sum_G P_{\mathrm{ER}}(G)\,\delta_G$ over `SimpleGraph (Fin n)`, the product running over the off-diagonal elements of `Sym2 (Fin n)`. For $p\in[0,1]$ its total mass is $1$ (proved in the mission's sanity file).
-- source:
--   Du, Mao, Sun, Wu, Xu, Sharp detection thresholds for random geometric graphs with polynomial average degrees, arXiv:2610.08517 (held version, sha256 e7bebd4a…), §1, p.1 (PDF p.3)

import Mathlib
import Definitions.Def_RGGDetect_rggLaw

open MeasureTheory
open scoped Classical

namespace RGGDetect

/-- The off-diagonal unordered pairs `{i, j}`, `i ≠ j`, of `Fin n`: the possible edges. -/
noncomputable def edgeSlots (n : ℕ) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter fun e => ¬ e.IsDiag

/-- The probability `∏_{i<j} p^{A_{ij}} (1-p)^{1-A_{ij}} = p^{|E(G)|}(1-p)^{\binom n2-|E(G)|}` of the
graph `G` under `G(n, p)`. -/
noncomputable def erWeight {n : ℕ} (p : ℝ) (G : SimpleGraph (Fin n)) : ℝ :=
  ∏ e ∈ edgeSlots n, if e ∈ G.edgeSet then p else 1 - p

/-- `P_ER`, the law of the Erdős–Rényi graph `G(n, p)`: every pair of distinct vertices is an edge
independently with probability `p` (arXiv:2610.08517, held version, §1, p.1).

**Formalization Note** The law is the finite sum `∑_G w(G) δ_G` with `w(G)` the product of `p` over
the edges and `1 - p` over the non-edges; for `p ∈ [0, 1]` it is a probability measure. -/
noncomputable def erLaw (n : ℕ) (p : ℝ) : Measure (SimpleGraph (Fin n)) :=
  ∑ G : SimpleGraph (Fin n), ENNReal.ofReal (erWeight p G) • Measure.dirac G

end RGGDetect


