-- Prove2me | Definitions.Def_BosonicLearn_heterodyneLaw
-- name    : BosonicLearn_heterodyneLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:24:42.914287+00:00
-- url     : https://prove2.me/theorems/aa314320-e8a6-4747-bfbf-ee12f6b4ebb2
-- title:
--   Outcome law of heterodyne detection
-- statement:
--   Heterodyne detection on one copy of an $n$-mode state $\rho$ yields an outcome $Y\in\mathbb R^{2n}$ (grouped coordinates) with law
--
--   $$\Pr(Y\in B)=\int_B Q_\rho(\beta)\,d\beta ,$$
--
--   where $Q_\rho$ is the Husimi density. On a Gaussian state $\rho(\mu,\Sigma)$ this law is $\mathcal N(\mu,\Sigma+\tfrac12 I)$ (Eq. (207), a milestone).
--
--   **Formalization Note** The law is defined from the Husimi density and not from the Gaussian formula, so Eq. (207) is a theorem and also certifies the normalization.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, p. 5; Eq. (207), p. 61

import Mathlib
import Definitions.Def_BosonicLearn_husimiQ

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open MeasureTheory

namespace BosonicLearn

/-- **Outcome law of heterodyne detection on one copy.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 5, and Eq. (207), p. 61 ("a heterodyne measurement on ρ(µ, Σ) produces a classical Gaussian
outcome Y ∼ N(µ, C), C := Σ + ½I").

`heterodyneLaw ρ` is the measure on `ℝ²ⁿ` (grouped coordinates, Euclidean space indexed by `Fin n ⊕ Fin n`)
with density `Q_ρ(β)` (`husimiQ`) with respect to Lebesgue measure.

**Formalization Note.** Defined from the Husimi density, not from the Gaussian law, so Eq. (207)
(`heterodyne_law`) is a theorem, which also pins the normalization (total mass one). -/
noncomputable def heterodyneLaw {n : ℕ} (ρ : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ) :
    Measure (EuclideanSpace ℝ (Fin n ⊕ Fin n)) :=
  (volume : Measure (EuclideanSpace ℝ (Fin n ⊕ Fin n))).withDensity
    (fun β => ENNReal.ofReal (husimiQ ρ (WithLp.ofLp β)))

end BosonicLearn


