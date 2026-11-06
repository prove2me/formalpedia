-- Prove2me | Definitions.Def_FracTruthSched_opt
-- name    : FracTruthSched_opt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:53.367298+00:00
-- url     : https://prove2.me/theorems/1d0ef811-305b-4820-b386-8bc1ef2cb29b
-- title:
--   Optimal integral makespan $\mathrm{Opt}(t)$
-- statement:
--   The **optimal integral makespan** of an input $t$ is
--   $$\mathrm{Opt}(t)=\min_{\sigma}\ \max_i \sum_{j:\ \sigma(j)=i} t_{ij},$$
--   the minimum over all integral allocations $\sigma$ (each task wholly to one machine). It is the benchmark of the paper's lower bound; the fractional optimum $\mathrm{Opt}_{\mathrm{frac}}(t)\le\mathrm{Opt}(t)$ is a different, weaker benchmark and is not used.
--
--   **Formalization Note.** The minimum is over the finite, nonempty set of maps from tasks to the $n\ge1$ machines. With no tasks, $\mathrm{Opt}(t)=0$.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, §2.2, p.4

import Mathlib
import Definitions.Def_FracTruthSched_schedMakespan

set_option autoImplicit false

namespace FracTruthSched

/-- The **optimal integral makespan** `Opt(t)` (Anastasiadis et al., arXiv:2611.06642v1, §2.2,
p.4: "We write Opt(t) for the optimal integral makespan, the minimum of max_i t_i · x_i over all
integral allocations x").

**Formalization Note.** The minimum is `Finset.inf'` over the finite, nonempty type `τ → Fin n` of
integral allocations (`n ≥ 1` by `[NeZero n]`). This is the *integral* benchmark; the fractional
optimum `Opt_frac` is not used anywhere in this mission. With no tasks, `opt t = 0`. -/
noncomputable def opt {n : ℕ} [NeZero n] {τ : Type*} [Fintype τ] [DecidableEq τ]
    (t : Fin n → τ → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun σ : τ → Fin n => schedMakespan t σ)

end FracTruthSched


