-- Prove2me | Definitions.Def_DivideChooseBayes_IsOptimalDivision
-- name    : DivideChooseBayes_IsOptimalDivision
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:31:21.222988+00:00
-- url     : https://prove2.me/theorems/9c0d2e2d-b7ab-4a36-949b-41bebf2f89d0
-- title:
--   Divider-optimal division
-- statement:
--   A division $q\in[-1,1]^n$ is **divider-optimal** for the prior $\mu$ if $U(q')\le U(q)$ for every division $q'\in[-1,1]^n$, where $U$ is the divider's interim expected utility. The maximum is over all divisions, not only those in which the divider prefers pile 1.
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, §3, p.6; Lemma 3.2

import Mathlib
import Definitions.Def_DivideChooseBayes_IsDivision
import Definitions.Def_DivideChooseBayes_interimUtility

open MeasureTheory ProbabilityTheory

namespace DivideChooseBayes

/-- **Divider-optimal division.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, §3, p.6 ("his optimal division"), Lemma 3.2 ("A divider-optimal division").

A division `q ∈ [−1,1]ⁿ` maximizing the divider's interim expected utility over **all** divisions.
-/
def IsOptimalDivision {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ)) (gD q : ι → ℝ) : Prop :=
  IsDivision q ∧ ∀ q' : ι → ℝ, IsDivision q' → interimUtility μ gD q' ≤ interimUtility μ gD q

end DivideChooseBayes


