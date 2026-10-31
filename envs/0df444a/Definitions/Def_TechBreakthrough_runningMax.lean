-- Prove2me | Definitions.Def_TechBreakthrough_runningMax
-- name    : TechBreakthrough_runningMax
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:32:34.935311+00:00
-- url     : https://prove2.me/theorems/250734a4-794b-44b9-ada9-73d9c50044ee
-- title:
--   The maximum process $M_t=m\vee\sup_{s\le t}X_s$ and the measure $dM$
-- statement:
--   Given $m$, the maximum process is
--
--   $$M_t=m\vee\sup_{s\le t}X_s,\qquad t\ge0.$$
--
--   Its path is continuous and nondecreasing, so it defines a Stieltjes measure $dM_t$ on the line. The pair $(X,M)$ is the Markovian state of the stopping problem: the threshold $Y$ is reached exactly when $X$ sets a new maximum.
--
--   **Formalization Note** The measure is that of $t\mapsto M_{t\vee0}$ on $\mathbb R$, through `Monotone.stieltjesFunction`.
-- source:
--   Décamps, Gensbittel & Mariotti, Investment Timing and Technological Breakthroughs, arXiv:2106.05112v1, §5, p.12; dM in (19), p.13

import Definitions.Def_TechBreakthrough_PathSpace

open MeasureTheory
open scoped NNReal

namespace TechBreakthrough

variable {α β : EReal}

/-- The maximum process `M_t = m ∨ sup_{s ≤ t} X_s`, arXiv:2106.05112v1, §5, p.12. -/
noncomputable def runningMax (m : ℝ) (t : ℝ≥0) (ω : PathSpace α β) : ℝ :=
  m ⊔ sSup ((fun s => canonicalProcess α β s ω) '' Set.Icc 0 t)

theorem bddAbove_image_Icc (t : ℝ≥0) (ω : PathSpace α β) :
    BddAbove ((fun s => canonicalProcess α β s ω) '' Set.Icc 0 t) :=
  (isCompact_Icc.image (canonicalProcess_continuous α β ω)).bddAbove

/-- The path `t ↦ M_{t ∨ 0}` on the real line is nondecreasing. -/
theorem runningMax_monotone (m : ℝ) (ω : PathSpace α β) :
    Monotone fun u : ℝ => runningMax m u.toNNReal ω := by
  intro u v huv
  refine sup_le_sup_left (csSup_le_csSup (bddAbove_image_Icc _ ω) ?_ ?_) m
  · exact ⟨_, 0, ⟨le_rfl, zero_le⟩, rfl⟩
  · exact Set.image_mono (Set.Icc_subset_Icc_right (Real.toNNReal_le_toNNReal huv))

/-- The measure `dM_t`: the Stieltjes measure on the line of the continuous nondecreasing path
`t ↦ M_{t ∨ 0}`, arXiv:2106.05112v1, (19), p.13. -/
noncomputable def dMax (m : ℝ) (ω : PathSpace α β) : Measure ℝ :=
  (runningMax_monotone m ω).stieltjesFunction.measure

end TechBreakthrough


