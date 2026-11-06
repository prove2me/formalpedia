-- Prove2me | Definitions.Def_ParetoNCSched_MState
-- name    : ParetoNCSched_MState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:04:28.883043+00:00
-- url     : https://prove2.me/theorems/954a0e7b-3814-4e37-a7b4-501f5229ef71
-- title:
--   State $(t_k, e(t_k), F(t_k))$ of the run of $\mathrm{MRC}_R$
-- statement:
--   A state of the run of $\mathrm{MRC}_R$ records the current time $t_k$, the elapsed times $e_1(t_k),\dots,e_n(t_k)$ of all jobs and the cost so far $F(t_k)$. The algorithm acts on the state at its event times $t_0=0<t_1<\cdots$.
-- source:
--   Benomar–Perchet, Pareto-optimal Non-Clairvoyant Scheduling with Predictions, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, "The run, interval by interval", p.17

import Mathlib

namespace ParetoNCSched

/-- **State of the run of `MRC_R` at an event time.** Benomar–Perchet, *Pareto-optimal Non-Clairvoyant Scheduling with Predictions*, manuscript (STOC 2027 submission, sha256 852cb174…), Appendix B, "The run, interval by
interval", p.17: the algorithm acts on the state at event times `t_k` — the time, the elapsed
times `e`, and the cost so far `F`.

**Formalization Note.** A record `(time, e, F)`; the run of `MRC_R` is the iteration of a one-step
map on these records starting from `(0, 0, 0)`. -/
structure MState (n : ℕ) where
  /-- the current time `t_k` -/
  time : ℝ
  /-- the elapsed times `eᵢ(t_k)` -/
  e : Fin n → ℝ
  /-- the cost so far `F(t_k)` -/
  F : ℝ

end ParetoNCSched


