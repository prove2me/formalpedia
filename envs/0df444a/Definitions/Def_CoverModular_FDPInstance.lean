-- Prove2me | Definitions.Def_CoverModular_FDPInstance
-- name    : CoverModular_FDPInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:13:30.327817+00:00
-- url     : https://prove2.me/theorems/a3b304b1-757b-464b-8078-cc665ee6908a
-- title:
--   Flexibility design instance $(\mu,c,d,p)$
-- statement:
--   A **flexibility design instance** consists of finite sets $I$ of supply nodes and $J$ of demand nodes, a finite set $\Omega$ of scenarios with weights $\mu_\omega$, realized capacities $c_{i\omega}$ of supply node $i$ and demands $d_{j\omega}$ of demand node $j$ in scenario $\omega$, and a unit profit $p_{ij}$ for each arc $(i,j)\in I\times J$. The set of all arcs is the universe $\mathcal F=I\times J$, and a flexibility structure is a subset $\mathcal A\subseteq\mathcal F$.
--
--   **Formalization Note** Only the data are recorded; the sign conditions are the separate predicate `FDPInstance.Standing`, and finiteness enters through the `Fintype` instances of the definitions that use the data.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), §2, pp.5–6

import Mathlib

namespace CoverModular

/-- The data of a flexibility design problem (DeValve, Pekeč, Wei, *Approximate submodularity
in network design problems*, SSRN 3844987, §2, pp.5–6): supply nodes `I` (the paper's
`i = 1, …, m`), demand nodes `J` (`j = 1, …, n`), a finite scenario set `Ω` with weights
`μ ω` (the probabilities `µ_ω`), realized capacities `c i ω` (`c_iω`), realized demands
`d j ω` (`d_jω`), and unit profits `p i j` (`p_ij`).

**Formalization Note** Only the data are recorded; the standing sign conditions are the
separate predicate `FDPInstance.Standing`. Finiteness of `I`, `J`, `Ω` is imposed by the
`Fintype` instances of the definitions that use the data. -/
structure FDPInstance (I J Ω : Type) where
  /-- Scenario weights `µ_ω`. -/
  μ : Ω → ℝ
  /-- Realized capacity `c_iω` of supply node `i` in scenario `ω`. -/
  c : I → Ω → ℝ
  /-- Realized demand `d_jω` of demand node `j` in scenario `ω`. -/
  d : J → Ω → ℝ
  /-- Unit profit `p_ij` of arc `(i, j)`. -/
  p : I → J → ℝ

end CoverModular


