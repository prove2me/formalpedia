-- Prove2me | Definitions.Def_ParetoNCSched_stateAt
-- name    : ParetoNCSched_stateAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:22:16.021714+00:00
-- url     : https://prove2.me/theorems/129e7b62-fb77-47b1-be87-698e51490482
-- title:
--   State of the run of $\mathrm{MRC}_R$ at time $t$
-- statement:
--   The state of the run at an arbitrary time $t$: the time $t$, the elapsed times $e(t)$ and the cost so far $F(t)$ of the rate function of $\mathrm{MRC}_R$. The committed job, $N$, the waiting jobs, the level, $\gamma_c$, $\gamma_r$ and $D$ at time $t$ are those of this state.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, p.17

import Mathlib
import Definitions.Def_ParetoNCSched_mrcRate
import Definitions.Def_ParetoNCSched_costSoFar
import Definitions.Def_ParetoNCSched_MState

namespace ParetoNCSched

/-- **The state of the run of `MRC_R` at an arbitrary time `t`.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, p.17: at time `t`
the committed job, `N`, the waiting jobs, the level, `γ_c`, `γ_r` and `D` are computed from the
elapsed times `e(t)` and the cost so far `F(t)`.

**Formalization Note.** `⟨t, e(t), F(t)⟩` with `eᵢ(t) = ∫₀ᵗ rᵢ` and `F(t) = ∫₀ᵗ N` for the rate
function of `MRC_R`, so every per-state quantity applies at every time. -/
noncomputable def stateAt {n : ℕ} (R : ℝ) (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (t : ℝ) :
    MState n :=
  ⟨t, fun i => elapsed (mrcRate R p σ) i t, costSoFar p (mrcRate R p σ) t⟩

end ParetoNCSched


