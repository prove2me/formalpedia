-- Prove2me | Definitions.Def_BewleyGE_minIncome
-- name    : BewleyGE_minIncome
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:27.655787+00:00
-- url     : https://prove2.me/theorems/00693a8c-1977-4067-911e-c8269fbbf318
-- title:
--   Lowest income $\min_{y\in\mathcal Y}p\cdot y$
-- statement:
--   At prices $p$, the **lowest income** is $\min_{y\in\mathcal Y}p\cdot y$, the smallest value of an endowment vector. It determines the natural borrowing limit.
--
--   **Formalization Note** A genuine minimum over the nonempty finite set $\mathcal Y$.
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, §2, p.5; §2.1, p.7

import Mathlib
import Definitions.Def_BewleyGE_Economy

namespace BewleyGE

/-- **Lowest income** `min_{y ∈ 𝒴} p · y`. Light, arXiv:1906.06810v2, §2, p.5 and §2.1, p.7.

**Formalization Note.** A genuine minimum over the nonempty finite set `𝒴` (`Finset.inf'`). -/
noncomputable def minIncome {n : ℕ} (E : Economy n) (p : Fin n → ℝ) : ℝ :=
  E.Y.inf' E.Y_nonempty (fun y => ∑ i, p i * y i)

end BewleyGE


