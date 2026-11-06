-- Prove2me | Definitions.Def_ParetoNCSched_step
-- name    : ParetoNCSched_step
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:15:18.634542+00:00
-- url     : https://prove2.me/theorems/c33fa845-161c-4ef2-bd54-4d7770b6c43c
-- title:
--   One step of the run of $\mathrm{MRC}_R$
-- statement:
--   One step of the run from the state at $t_k$:
--
--   1. if no job is unfinished, nothing changes;
--   2. if $N=1$, the last job $j$ runs alone until it completes (this final completion is not an event): time and cost increase by $p_j-e_j$ and $e_j$ becomes $p_j$;
--   3. if $N\ge2$, with $\Delta=t_{k+1}-t_k$ the step length, time increases by $\Delta$, each $e_i$ by $\Delta r_i$, and $F$ by $N\Delta$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, "The run, interval by interval", p.17; Algorithm 1, p.9

import Mathlib
import Definitions.Def_ParetoNCSched_stepLength
import Definitions.Def_ParetoNCSched_stepRates

namespace ParetoNCSched

/-- **One step of the run of `MRC_R`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, "The run, interval by interval", p.17, and
Algorithm 1, p.9. From the state at `t_k`:
1. if no job is unfinished, the state is final;
2. if `N = 1`, the last job `j` runs alone until it completes (this final completion is not an
   event): time and cost increase by `pⱼ − eⱼ`, and `eⱼ` becomes `pⱼ`;
3. if `N ≥ 2`, the rates of `stepRates` are used for the step length `Δ = t_{k+1} − t_k`: the time
   increases by `Δ`, each `eᵢ` by `Δ rᵢ`, and `F` by `N Δ`.

**Formalization Note.** `F` increases at rate `N`, constant on the step. -/
noncomputable def step {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (s : MState n) :
    MState n :=
  match committedJob p σ s with
  | none => s
  | some j =>
    if (unfinished p s).card = 1 then
      ⟨s.time + (p j - s.e j), Function.update s.e j (p j), s.F + (p j - s.e j)⟩
    else
      ⟨s.time + stepLength R p s j, s.e + stepLength R p s j • stepRates R p σ s,
        s.F + ((unfinished p s).card : ℝ) * stepLength R p s j⟩

end ParetoNCSched


