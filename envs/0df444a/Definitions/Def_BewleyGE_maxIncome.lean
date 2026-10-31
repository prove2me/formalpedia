-- Prove2me | Definitions.Def_BewleyGE_maxIncome
-- name    : BewleyGE_maxIncome
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:11.175958+00:00
-- url     : https://prove2.me/theorems/85a4edf5-c1d8-495a-88dc-055bc89ae721
-- title:
--   Highest income $\max_{y\in\mathcal Y}p\cdot y$
-- statement:
--   At prices $p$, the **highest income** is $\max_{y\in\mathcal Y}p\cdot y$. It enters the maximal wealth $\bar a(p,r)$.
--
--   **Formalization Note** A genuine maximum over the nonempty finite set $\mathcal Y$.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, §2.1, p.7

import Mathlib
import Definitions.Def_BewleyGE_Economy

namespace BewleyGE

/-- **Highest income** `max_{y ∈ 𝒴} p · y`. Light, arXiv:1906.06810v2, §2.1, p.7.

**Formalization Note.** A genuine maximum over the nonempty finite set `𝒴` (`Finset.sup'`). -/
noncomputable def maxIncome {n : ℕ} (E : Economy n) (p : Fin n → ℝ) : ℝ :=
  E.Y.sup' E.Y_nonempty (fun y => ∑ i, p i * y i)

end BewleyGE


