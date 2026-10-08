-- Prove2me | Definitions.Def_AdaptiveStepIPM_PredCorr_Algorithm
-- name    : AdaptiveStepIPM_PredCorr_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:23:39.506443+00:00
-- url     : https://prove2.me/theorems/304a7558-86ef-466e-81ce-ab2ec689acf5
-- title:
--   One predictor-corrector iteration of Algorithm 1
-- statement:
--   One iteration starts at $(x,s)$, takes a predictor direction with $\gamma=0$, and chooses the greatest nonnegative $\bar\theta$ such that every intermediate pair $(x(\theta),s(\theta))$, $0\le\theta\le\bar\theta$, lies in $N_2(1/2)$. It then takes one full corrector direction with $\gamma=1$ from the predictor endpoint. The resulting pair is the next iterate.
--
--   $$ (x^+,s^+)=(x(\bar\theta)+d'_x,\ s(\bar\theta)+d'_s). $$
--
--   This relation defines the transition used by Algorithm 1 and its termination theorem.
--
--   **Formalization Note** “Greatest” means an attained maximum. If the admissible steps have no greatest member, the relation has no successor at that input.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), pp. 6–7, Algorithm 1

import Mathlib
import Definitions.Def_AdaptiveStepIPM_PredCorr_Direction

namespace AdaptiveStepIPM.PredCorr

/-- Every step up to θ remains in the outer neighborhood. -/
def PredictorAdmissible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (x s dx ds : Fin n → ℝ) (θ : ℝ) : Prop :=
  0 ≤ θ ∧ ∀ u ∈ Set.Icc (0 : ℝ) θ,
    N2 A b c (1 / 2) (stepX x dx u) (stepS s ds u)

/-- One iteration of Algorithm 1, with the largest admissible predictor
step and one full corrector step. -/
def Alg1Step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (x s xNext sNext : Fin n → ℝ) : Prop :=
  ∃ (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (θbar : ℝ)
    (dx' : Fin n → ℝ) (dy' : Fin m → ℝ) (ds' : Fin n → ℝ),
    SearchDirection A x s 0 dx dy ds ∧
    IsGreatest {θ : ℝ | PredictorAdmissible A b c x s dx ds θ} θbar ∧
    SearchDirection A (stepX x dx θbar) (stepS s ds θbar) 1 dx' dy' ds' ∧
    xNext = stepX (stepX x dx θbar) dx' 1 ∧
    sNext = stepS (stepS s ds θbar) ds' 1

end AdaptiveStepIPM.PredCorr


