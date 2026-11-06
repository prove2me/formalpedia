-- Prove2me | Definitions.Def_FracTruthSched_IsFeasibleOn
-- name    : FracTruthSched_IsFeasibleOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:20.039262+00:00
-- url     : https://prove2.me/theorems/7a61dd97-9923-4664-9202-61945683da1f
-- title:
--   Feasible fractional allocation on a domain of inputs
-- statement:
--   A mechanism $(x,P)$ is **feasible** on a domain $\mathcal D$ of inputs if at every $t\in\mathcal D$ it allocates every task in full:
--   $$x_{ij}(t)\in[0,1]\quad\text{for all } i,j,\qquad \sum_{i} x_{ij}(t)=1\quad\text{for every task } j.$$
--   This is part of the definition of a fractional mechanism. Without the second condition a mechanism could allocate nothing and have makespan $0$.
--
--   **Formalization Note.** The domain is the nonnegative inputs for the mechanisms $R_m$ of a family, and the graph inputs for mechanisms on $MC_\ell$; values outside the domain are unconstrained.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, §2.1, p.3

import Mathlib
import Definitions.Def_FracTruthSched_FracMech

set_option autoImplicit false

namespace FracTruthSched

/-- **Feasibility** of a fractional mechanism on a domain `D` of inputs (Anastasiadis et al.,
arXiv:2611.06642v1, §2.1, p.3: "assigns a fraction x_ij(t) ∈ [0, 1] of each task j to each
machine i, with Σ_i x_ij(t) = 1"): at every input `t ∈ D`, every `x t i j ∈ [0,1]` and every task
is allocated in full.

**Formalization Note.** `D` is `Nonneg` for the mechanisms `R_m` of the paper's families and
`IsGraphInput` for mechanisms on the core tasks of `MC_ℓ`. Values at inputs outside `D` are
unconstrained (they are never used). -/
def IsFeasibleOn {n : ℕ} {τ : Type*} (D : (Fin n → τ → ℝ) → Prop) (M : FracMech n τ) : Prop :=
  ∀ t, D t → (∀ i j, 0 ≤ M.x t i j ∧ M.x t i j ≤ 1) ∧ ∀ j, ∑ i, M.x t i j = 1

end FracTruthSched


