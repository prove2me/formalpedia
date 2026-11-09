-- Prove2me | Definitions.Def_BosonicLearn_heterodyneSuccess
-- name    : BosonicLearn_heterodyneSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:28:29.428442+00:00
-- url     : https://prove2.me/theorems/a14520a3-6a5e-4612-9fcd-fc5be65457c2
-- title:
--   Success probability of a non-adaptive heterodyne protocol
-- statement:
--   A non-adaptive heterodyne protocol measures $N$ copies of $\rho$ by independent heterodyne detections, giving i.i.d. outcomes $Y_1,\dots,Y_N$ with the heterodyne law of $\rho$, and outputs the density operator $\widehat\rho=\mathrm{est}(Y_1,\dots,Y_N)$. Its success probability at precision $\varepsilon$ is
--
--   $$\Pr\Big[\tfrac12\|\mathrm{est}(Y_1,\dots,Y_N)-\rho\|_1\le\varepsilon\Big].$$
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Theorem 3, p. 7; Theorem 8, p. 61; Corollary 19, p. 64

import Mathlib
import Definitions.Def_BosonicLearn_heterodyneLaw
import Definitions.Def_BosonicLearn_traceDist

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory
open scoped ENNReal

namespace BosonicLearn

/-- **Success probability of a non-adaptive heterodyne protocol.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Theorem 3, p. 7 ("This bound can be achieved by heterodyne measurements"), Theorem 8, p. 61 ("a
non-adaptive protocol using only independent heterodyne measurements"), Corollary 19, p. 64.

`N` copies of `ρ` are measured by independent heterodyne detections, giving `Y₁,…,Y_N` i.i.d. with law
`heterodyneLaw ρ`, and `est` maps the outcomes to a density operator. `heterodyneSuccess N est ρ ε` is the
probability that `½‖est(Y) − ρ‖₁ ≤ ε`. -/
noncomputable def heterodyneSuccess {n : ℕ} (N : ℕ)
    (est : (Fin N → EuclideanSpace ℝ (Fin n ⊕ Fin n)) → State (Occupation (Fin n)))
    (ρ : State (Occupation (Fin n))) (ε : ℝ) : ℝ≥0∞ :=
  (Measure.pi fun _ : Fin N => heterodyneLaw ρ.coefficients)
    {y | traceDist (est y).coefficients ρ.coefficients ≤ ENNReal.ofReal ε}

end BosonicLearn


