-- Prove2me | Definitions.Def_ImpactCopula_unifPair
-- name    : ImpactCopula_unifPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:53:04.480829+00:00
-- url     : https://prove2.me/theorems/27d91387-4d7f-48ce-bf5e-ea3c6dcd8e92
-- title:
--   The law of $N + N$ independent $\mathrm{Uniform}(0,1)$ variables $(U, V)$
-- statement:
--   For $N \ge 1$, let $U_1, \dots, U_N, V_1, \dots, V_N$ be mutually independent random variables, each uniform on $(0,1)$. This definition is their joint law, the product of $2N$ copies of Lebesgue measure on $[0,1]$, written as a measure on pairs $(U, V) \in \mathbb R^N \times \mathbb R^N$.
--
--   **Formalization Note** Each coordinate has law `volume.restrict (Set.Icc 0 1)`; the indices are $0, \dots, N-1$ (the paper's $1, \dots, N$).
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Theorem 1, p.10 (PDF p.13), notation used in Theorem 2, p.12 (PDF p.15)

import Mathlib

open MeasureTheory

namespace ImpactCopula

/-- The joint law of `(U, V) = (U_1, …, U_N, V_1, …, V_N)`, mutually independent `Uniform(0, 1)`
random variables (Theorem 1, p.10, PDF p.13, notation used in Theorem 2, p.12, PDF p.15), Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024).

**Formalization Note.** `U` is the first and `V` the second component of a point
`p : (Fin N → ℝ) × (Fin N → ℝ)`; each coordinate has law `volume.restrict (Set.Icc 0 1)`, and the
law of the pair is the product measure. Indices are 0-based. -/
noncomputable def unifPair (N : ℕ) : Measure ((Fin N → ℝ) × (Fin N → ℝ)) :=
  (Measure.pi fun _ : Fin N => volume.restrict (Set.Icc (0 : ℝ) 1)).prod
    (Measure.pi fun _ : Fin N => volume.restrict (Set.Icc (0 : ℝ) 1))

end ImpactCopula


