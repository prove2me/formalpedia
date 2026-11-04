-- Prove2me | Definitions.Def_OverbookBL_IsAdmissible
-- name    : OverbookBL_IsAdmissible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:52:51.857959+00:00
-- url     : https://prove2.me/theorems/7146c624-f8f9-403a-bf4c-3206b2fa4efb
-- title:
--   Global optimum, optimal index solution, and admissible solutions of problem (1)
-- statement:
--   Consider problem (1) with capacity $B$, past accepted arrivals $\vec x[t-1]$ and (estimated) future arrivals $\widetilde N$.
--
--   1. $\vec x$ is **globally optimal** if $0\le\vec x\le\widetilde N$ and its objective is at least that of every $\vec y$ with $0\le\vec y\le\widetilde N$.
--   2. $\vec x$ is an **optimal index solution** if it is an index solution (Definition 1) and its objective is at least that of every index solution.
--   3. $\vec x$ is **admissible** if it is an optimal index solution that is locally optimal (Definition 2) at its threshold index.
--
--   Admissibility is the property the paper assumes of the solution $\vec x'$ found by the online index policy in line 6 of Algorithm 1 (p.21: "we only assume that it is locally optimal at its threshold index").
--
--   **Formalization Note** Optimal index solutions are optimal among index solutions only, not globally.
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, problem (1), p.10; p.11; p.21

import Definitions.Def_OverbookBL_IsLocOpt
import Definitions.Def_OverbookBL_IsIndexSol

namespace OverbookBL

/-- A globally optimal solution of problem (1) (Freund & Zhao, *Overbooking with bounded loss*,
arXiv:2204.11148v2, p.10): `x ≤ Nf` and no feasible `y ≤ Nf` has a larger objective. -/
def IsGlobOpt {k : ℕ} (I : Instance k) (B : ℕ) (past Nf x : Fin k → ℕ) : Prop :=
  x ≤ Nf ∧ ∀ y : Fin k → ℕ, y ≤ Nf → obj I B past y ≤ obj I B past x

/-- An optimal index solution of problem (1) (arXiv:2204.11148v2, p.11, "solves the optimization
problem (1) … subject to finding an index solution"): an index solution whose objective is at
least that of every index solution. It is optimal among index solutions only, not globally. -/
def IsOptIndex {k : ℕ} (I : Instance k) (B : ℕ) (past Nf x : Fin k → ℕ) : Prop :=
  (∃ e, IsIndexSol Nf x e) ∧
  ∀ y : Fin k → ℕ, (∃ e, IsIndexSol Nf y e) → obj I B past y ≤ obj I B past x

/-- An *admissible* solution: an optimal index solution of problem (1) that is locally optimal
(Definition 2) at its threshold index (the smallest one, Definition 1). This is the property the
paper assumes of the solution `x⃗′` found in line 6 of Algorithm 1 (arXiv:2204.11148v2, p.21:
"For the optimal index solution x′, we only assume that it is locally optimal at its threshold
index"; "we are guaranteed that there exists an index solution that is locally optimal at the
threshold index").

**Formalization Note** The threshold index is unique, so `∃ e` here is "the threshold index". -/
def IsAdmissible {k : ℕ} (I : Instance k) (B : ℕ) (past Nf x : Fin k → ℕ) : Prop :=
  IsOptIndex I B past Nf x ∧ ∃ e, IsThreshold Nf x e ∧ IsLocOpt I B past Nf x e

end OverbookBL


