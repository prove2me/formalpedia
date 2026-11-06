-- Prove2me | Definitions.Def_FracTruthSched_schedMakespan
-- name    : FracTruthSched_schedMakespan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:13.138983+00:00
-- url     : https://prove2.me/theorems/43e62ecc-d7eb-485d-9af9-0f915c844a57
-- title:
--   Makespan of an integral allocation $\sigma$
-- statement:
--   An **integral allocation** assigns each task $j$ wholly to one machine $\sigma(j)$. Its makespan at input $t$ is the maximum load,
--   $$\max_i \sum_{j:\ \sigma(j)=i} t_{ij}.$$
--   It is the quantity minimized by the integral optimum $\mathrm{Opt}(t)$ and by the eligible optimum $C(t)$.
--
--   **Formalization Note.** An integral allocation ($x_{ij}\in\{0,1\}$, $\sum_i x_{ij}=1$) is a map $\sigma$ from tasks to machines; the maximum is over the $n\ge1$ machines.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, §2.2, p.4

import Mathlib

set_option autoImplicit false

namespace FracTruthSched

/-- The **makespan of an integral allocation** `σ` (each task `j` wholly to machine `σ j`) at
input `t` (Anastasiadis et al., arXiv:2611.06642v1, §2.2, p.4: "max_i t_i · x_i" for an integral
allocation `x`): `max_i Σ_{j : σ j = i} t_ij`.

**Formalization Note.** An integral allocation (`x_ij ∈ {0,1}`, `Σ_i x_ij = 1`) is the same as a map
`σ : τ → Fin n`. The maximum is `Finset.sup'` over `Fin n`, nonempty by `[NeZero n]`. -/
noncomputable def schedMakespan {n : ℕ} [NeZero n] {τ : Type*} [Fintype τ]
    (t : Fin n → τ → ℝ) (σ : τ → Fin n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i => ∑ j ∈ Finset.univ.filter (fun j => σ j = i), t i j)

end FracTruthSched


