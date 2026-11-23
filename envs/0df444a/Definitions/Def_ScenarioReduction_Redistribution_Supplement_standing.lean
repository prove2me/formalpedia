-- Prove2me | Definitions.Def_ScenarioReduction_Redistribution_Supplement_standing
-- name    : ScenarioReduction_Redistribution_Supplement_standing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:26:51.367735+00:00
-- url     : https://prove2.me/theorems/28708970-0d3f-46ae-8d48-5ad20b4ae280
-- title:
--   Standing assumptions of convex stochastic model (1)
-- statement:
--   Let $X\subseteq\mathbb R^n$ be the feasible set, $\Omega\subseteq\mathbb R^s$ the scenario space with its relative Borel sigma-field, and $f:\Omega\times\mathbb R^n\to[-\infty,+\infty]$ the random objective. The standing assumptions are
--
--   $$
--   X\ne\varnothing,\quad X\text{ closed and convex},\quad\Omega\text{ closed},
--   $$
--
--   with $f(\cdot,x)$ measurable for every $x$, and $f(\omega,\cdot)$ lower semicontinuous and convex for every $\omega$.
--
--   This predicate records the model assumptions independently of the probability distribution. It imposes no assumption about regularity of expected objectives.
--
--   **Formalization Note** The data are the published `ProbMetricStab.General.Model n s 0`: there is one objective and no stochastic constraints. Only its data, extended expectation, global value and global solution set are reused. Its normal-integrand predicate, localized probability class and modulus are not used. Convexity of an extended-real function means convexity of its real epigraph. Vectors have the Euclidean norm throughout; measures on the scenario subtype have the relative Borel sigma-field.
-- source:
--   Dupačová, Gröwe-Kuska, Römisch, Scenario reduction in stochastic programming, Math. Program. Ser. A 95 (2003), DOI 10.1007/s10107-002-0331-0, p. 493, model (1), PDF 1

import Mathlib
import Definitions.Def_ProbMetricStab_General_Setting
set_option autoImplicit false

namespace ScenarioReduction.Redistribution.Supplement

/-- Model (1), p. 493. Only the data of the published general model at zero
stochastic constraints is reused; its normal-integrand assumptions are not imposed. -/
def standing {n s : ℕ} (M : ProbMetricStab.General.Model n s 0) : Prop :=
  M.X.Nonempty ∧ IsClosed M.X ∧ Convex ℝ M.X ∧ IsClosed M.Ξ ∧
  (∀ x, Measurable (fun ω : M.Ξ => M.f 0 ω x)) ∧
  (∀ ω : M.Ξ, LowerSemicontinuous (M.f 0 ω)) ∧
  (∀ ω : M.Ξ, Convex ℝ
    {p : EuclideanSpace ℝ (Fin n) × ℝ | M.f 0 ω p.1 ≤ (p.2 : EReal)})

end ScenarioReduction.Redistribution.Supplement


