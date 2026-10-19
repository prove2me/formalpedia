-- Prove2me | Definitions.Def_AnnounceCorr_Criterion_Defs
-- name    : AnnounceCorr_Criterion_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:18.163964+00:00
-- url     : https://prove2.me/theorems/feec9286-2091-44ea-934f-9df38fe67569
-- title:
--   §3.1 and §4.2 — MSE, EA, correlation, and coefficient of variation
-- statement:
--   Let $W_D$ be a real random variable representing the steady-state wait of a delayed customer, and let $P$ be a real-valued prediction on the same probability space. Four quantities used in §4.2 are defined from their expectations:
--
--   $$
--   \operatorname{MSE}(P)=\mathbb E[(W_D-P)^2],\qquad
--   \operatorname{EA}=\mathbb E[W_D],\qquad
--   r[X,Y]=\frac{\operatorname{Cov}(X,Y)}{\sqrt{\operatorname{Var}(X)\operatorname{Var}(Y)}},\qquad
--   C_X=\frac{\sqrt{\operatorname{Var}(X)}}{\mathbb E[X]}.
--   $$
--
--   The first formula is equation (3); EA is the constant announcement from §3.1, and $C_{W_D}$ is the coefficient of variation used in Proposition 1. These definitions make the subsequent error identities statements about random variables rather than independent real parameters.
--
--   **Formalization Note** The Lean definitions are total: division by zero returns zero, and a nonintegrable real integral returns zero. The theorems impose square integrability and the positivity needed for their formulas; the definitions themselves record the paper's formulas without building the results into them.
-- source:
--   Bassamboo & Ibrahim, A General Framework to Compare Announcement Accuracy, submitted manuscript (Management Science, manuscript XXX; published as doi:10.1287/mnsc.2020.3722), pp. 7, 14 (PDF 7, 14), §3.1, §4.2, eq. (3)

import Mathlib

namespace AnnounceCorr.Criterion

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Equation (3), p. 14: `MSE(P) = E[(W_D - P)^2]`. -/
noncomputable def mse (μ : Measure Ω) (WD P : Ω → ℝ) : ℝ :=
  ∫ ω, (WD ω - P ω) ^ 2 ∂μ

/-- The static announcement `EA = E[W_D]`, pp. 7 and 14. -/
noncomputable def ea (μ : Measure Ω) (WD : Ω → ℝ) : Ω → ℝ :=
  fun _ => ∫ ω, WD ω ∂μ

/-- Pearson correlation `r[X,Y] = Cov[X,Y] / sqrt(Var[X] Var[Y])`. -/
noncomputable def corr (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  cov[X, Y; μ] / Real.sqrt (Var[X; μ] * Var[Y; μ])

/-- Coefficient of variation `C_X = sqrt(Var[X]) / E[X]`, p. 14. -/
noncomputable def coeffVar (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  Real.sqrt (Var[X; μ]) / ∫ ω, X ω ∂μ

end AnnounceCorr.Criterion


