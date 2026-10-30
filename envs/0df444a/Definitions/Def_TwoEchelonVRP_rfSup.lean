-- Prove2me | Definitions.Def_TwoEchelonVRP_rfSup
-- name    : TwoEchelonVRP_rfSup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:32:05.893901+00:00
-- url     : https://prove2.me/theorems/6104752a-ef03-4878-9779-aafa992d4eab
-- title:
--   Best Lagrangean bound $\max_{\beta,\lambda,\mu} z(RF(\beta,\lambda,\mu))$
-- statement:
--   The **best Lagrangean bound** is
--
--   $$
--   \sup \bigl\{\, z(RF(\beta,\lambda,\mu)) : \mu \le 0,\ \mu_0 \le 0,\ \beta \text{ solves } (12) \,\bigr\},
--   $$
--
--   the quantity written $\max_{\beta,\lambda,\mu} z(RF(\beta,\lambda,\mu))$ in Theorem 2.
--
--   **Formalization Note** The supremum is taken in the extended reals. That it is attained, i.e. a maximum, whenever it is not $+\infty$ (in particular when F has a feasible solution) is part of Theorem 2 (`theorem_2_max_attained`); the supremum can be $+\infty$, and is then not attained.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Operations Research 61(2) (2013) 298–314, doi:10.1287/opre.1120.1153, §3.1, Theorem 2, p. 301 ('max_{β,λ,μ}{z(RF(β, λ, μ))}')

import Mathlib
import Definitions.Def_TwoEchelonVRP_Instance
import Definitions.Def_TwoEchelonVRP_MultFeasible
import Definitions.Def_TwoEchelonVRP_zRF

namespace TwoEchelonVRP

/-- **The best Lagrangean bound** `max_{β,λ,μ} z(RF(β, λ, μ))`.
Baldacci et al., *An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem*,
Operations Research 61(2) (2013) 298–314, §3.1, Theorem 2, p. 301: the quantity
`max_{β,λ,μ}{z(RF(β, λ, μ))}`, the maximum over all `β` solving (12) and all penalty vectors
`λ ∈ ℝ^{N_C}`, `μ ∈ ℝ_−^{N_S+1}` (`MultFeasible`).

**Formalization Note.** `rfSup I` is the supremum in `EReal` of `z(RF(β, λ, μ))` over the admissible
multipliers. Attainment of this supremum is a separate statement (Theorem 2, clause (b) of
`theorem_2`); when F is infeasible the supremum can be `+∞` and is then not attained. -/
noncomputable def rfSup {ns nc : ℕ} (I : Instance ns nc) : EReal :=
  sSup {v | ∃ β lam μ μ0, MultFeasible I β lam μ μ0 ∧ v = zRF I β lam μ μ0}

end TwoEchelonVRP


