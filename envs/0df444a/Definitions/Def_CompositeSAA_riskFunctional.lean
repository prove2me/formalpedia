-- Prove2me | Definitions.Def_CompositeSAA_riskFunctional
-- name    : CompositeSAA_riskFunctional
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:11.167606+00:00
-- url     : https://prove2.me/theorems/9551b8fd-0bcc-4584-b990-484c9c221083
-- title:
--   Composite risk functional $\varrho[u,X]$ (2)
-- statement:
--   Let $X$ be a random vector with law $P$. The **composite risk functional** is
--
--   $$
--   \varrho[u,X]=\mathbb E\Bigl[f_1\bigl(u,\mathbb E[f_2(u,\mathbb E[\cdots f_k(u,\mathbb E[f_{k+1}(u,X)],X)\cdots],X)],X\bigr)\Bigr],
--   $$
--
--   i.e. the perturbed objective (8) with every level's measure equal to $P$. Problem (3) minimizes it over the feasible set $U$.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, display (2), p.1

import Mathlib
import Definitions.Def_CompositeSAA_perturbedObjective

open MeasureTheory

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, display (2), p.1: the composite risk functional

`ϱ[u, X] = E[f₁(u, E[f₂(u, E[⋯ f_k(u, E[f_{k+1}(u, X)], X) ⋯], X)], X)]`,

where `X` has law `P`. It is the perturbed objective (8) with every level's measure equal to `P`
(p.5, "If `Q^j = Q` for all `j` …"). -/
noncomputable def riskFunctional {n mX k : ℕ} (D : CompositeModel n mX k)
    (P : Measure (EuclideanSpace ℝ (Fin mX))) (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  perturbedObjective D (fun _ => P) u

end CompositeSAA


