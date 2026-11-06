-- Prove2me | Definitions.Def_FracTruthSched_makespan
-- name    : FracTruthSched_makespan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:40.435964+00:00
-- url     : https://prove2.me/theorems/1b8983a2-23c3-49db-88ed-0375718bc579
-- title:
--   Makespan $\mathrm{Mech}_x(t)$ of a fractional mechanism
-- statement:
--   The **load** (completion time) of machine $i$ at input $t$ is $t_i\cdot x_i(t)=\sum_j t_{ij}x_{ij}(t)$, and the **makespan** is the maximum load,
--   $$\mathrm{Mech}_x(t)=\max_{i} \sum_j t_{ij}\,x_{ij}(t).$$
--   It is the performance measure of a fractional mechanism.
--
--   **Formalization Note.** The maximum over the $n\ge1$ machines is a finite maximum (`Finset.sup'`).
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, §2.1, p.3

import Mathlib
import Definitions.Def_FracTruthSched_FracMech

set_option autoImplicit false

namespace FracTruthSched

/-- The **makespan** `Mech_x(t)` of a fractional mechanism at input `t` (Anastasiadis et al.,
arXiv:2611.06642v1, §2.1, p.3): "The completion time of machine i is t_i · x_i(t) = Σ_j t_ij x_ij(t);
we also call it the load of i. The makespan Mech_x(t) is the maximum completion time."

**Formalization Note.** The maximum over the machines is `Finset.sup'` over `Fin n`, nonempty by
`[NeZero n]` (the paper has `n ≥ 1` machines). -/
noncomputable def makespan {n : ℕ} [NeZero n] {τ : Type*} [Fintype τ] (M : FracMech n τ)
    (t : Fin n → τ → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ∑ j, t i j * M.x t i j)

end FracTruthSched


