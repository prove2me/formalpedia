-- Prove2me | Definitions.Def_CalibeatBandit_draw_run
-- name    : CalibeatBandit_draw_run
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-23T18:52:47.173304+00:00
-- url     : https://prove2.me/theorems/28b6e6c9-ec78-40fc-af8e-37ed493a5695
-- title:
--   Draw run — one action drawn per round from a mixed strategy, given the information fixed before the draw
-- statement:
--   A *draw run* (`DrawRun K T P`) records what the analysis of a bandit algorithm uses about one action draw per round, without fixing the algorithm or the protocol around it. On a probability space $(\Omega,P)$ and for $T$ rounds with $K$ actions it consists of
--
--   - two families of sub-$\sigma$-algebras with $\mathcal F_t\subseteq\mathcal G_t\subseteq\mathcal F_{t+1}$ (`info`, `preDraw`): the information at the start of round $t$, and the information just before the action of round $t$ is drawn;
--   - reward vectors $y_t\in[0,1]^K$, measurable with respect to $\mathcal G_t$;
--   - actions $I_t\in[K]$, measurable with respect to $\mathcal F_{t+1}$;
--   - vectors $p_t$ (`played`) with $P[I_t=i\mid\mathcal G_t]=p_t(i)$ almost surely for every action $i$.
--
--   The observation of round $t$ is the bandit feedback $y_t(I_t)$ (`DrawRun.obs`).
--
--   The structure says that, given everything fixed before the draw, including the rewards of the round, the action is drawn from the mixed strategy $p_t$. A run of the interaction protocol of §2.1 of *Calibeating Bandit Advice* is a draw run, and so is a run of the pricing protocol on a finite price grid, or the rounds after a restart of an algorithm. Results stated for draw runs therefore apply to all of these.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (STOC 2027 submission 1457), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1457.pdf, §2.1 (interaction protocol, p. 7) and Appendix C.1 (pp. 30–31). Definition of jasonhartline's accepted Lean proof of CalibeatBandit.Supplement.theorem_5_1 (submission of 2026-11-16).

import Mathlib

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory

/-- The part of a bandit interaction needed to analyze a single draw per round.
The recommendation may have any label type and is included in the pre-draw
information. -/
structure DrawRun (K T : ℕ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) where
  info : ℕ → MeasurableSpace Ω
  preDraw : ℕ → MeasurableSpace Ω
  y : ℕ → Ω → Fin K → ℝ
  I : ℕ → Ω → Fin K
  played : ℕ → Ω → Fin K → ℝ
  info_le : ∀ t ≤ T, info t ≤ mΩ
  info_le_preDraw : ∀ t < T, info t ≤ preDraw t
  preDraw_le_succ : ∀ t < T, preDraw t ≤ info (t + 1)
  y_measurable : ∀ t < T, Measurable[preDraw t] (y t)
  I_measurable : ∀ t < T, Measurable[info (t + 1)] (I t)
  y_mem : ∀ t < T, ∀ ω i, y t ω i ∈ Set.Icc (0 : ℝ) 1
  I_law : ∀ t < T, ∀ i : Fin K,
    condExp (preDraw t) P ((I t ⁻¹' {i}).indicator (fun _ => (1 : ℝ))) =ᵐ[P]
      fun ω => played t ω i

namespace DrawRun

variable {K T : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

def obs (run : DrawRun K T P) (t : ℕ) (ω : Ω) : ℝ :=
  run.y t ω (run.I t ω)

end DrawRun

end CalibeatBandit

end


