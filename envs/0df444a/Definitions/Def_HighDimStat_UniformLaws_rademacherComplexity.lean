-- Prove2me | Definitions.Def_HighDimStat_UniformLaws_rademacherComplexity
-- name    : HighDimStat_UniformLaws_rademacherComplexity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:29:14.468734+00:00
-- url     : https://prove2.me/theorems/fc6e39b6-afc3-4ed6-a15b-682408a9f003
-- title:
--   The Rademacher complexity of a function class (Eq. 4.13)
-- statement:
--   **Eq. (4.13).** The **Rademacher complexity** of a function class $F$,
--
--   $$
--   R_n(F) \;:=\; \mathbb E_{X,\varepsilon}\Big[\sup_{f\in F}\Big|\frac1n\sum_{i=1}^n\varepsilon_if(X_i)\Big|\Big]
--   \;=\; \mathbb E[\|S_n\|_F],
--   $$
--
--   the deterministic quantity obtained by averaging the symmetrized process over both the
--   samples and the Rademacher signs. This is the complexity measure Theorem 4.10's bound is
--   stated in terms of.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 105 (PDF p. 125), Eq. (4.13)

import Mathlib
import Definitions.Def_HighDimStat_UniformLaws_symmetrizedProcess

open MeasureTheory

namespace HighDimStat.UniformLaws

/-- **Eq. (4.13)**, Wainwright, *High-Dimensional Statistics* (2019), p. 105. The Rademacher
complexity `Rₙ(F) := E_{X,ε}[sup_{f∈F} |(1/n)∑ᵢεᵢf(Xᵢ)|] = E[‖Sₙ‖_F]` of a function class
`F = {f_j, j∈ι}`. -/
noncomputable def rademacherComplexity {D ι Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    (f : ι → D → ℝ)
    (Xs : ℕ → Ω → D) (eps : ℕ → Ω → ℝ) (Prob : Measure Ω) (n : ℕ) : ℝ :=
  ∫ ω, symmetrizedProcess f Xs eps n ω ∂Prob

end HighDimStat.UniformLaws


