-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_IsCondUniformSample
-- name    : OptimalSpectrum_Entangled_IsCondUniformSample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:21:58.212548+00:00
-- url     : https://prove2.me/theorems/14572619-bd95-496e-ba04-ce44381a1a78
-- title:
--   $n$ i.i.d. outcomes of the conditioned uniform POVM
-- statement:
--   Random vectors $U_1,\dots,U_n$ on a probability space form a **conditioned-uniform sample** for $\sigma$ when they are measurable, mutually independent, and each has law $\nu_\sigma=(1-\mathrm{tr}\,\sigma)\delta_0+d\langle u|\sigma|u\rangle U(du)$. This models measuring the $n$ fresh copies one at a time with the conditioned uniform POVM; $X_i=X(U_i)$ are then the i.i.d. estimators of §7.1.1.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §7.1.1, p. 20 (PDF p. 22)

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_condUniformLaw

open MeasureTheory ProbabilityTheory

namespace OptimalSpectrum.Entangled

/-- **`n` i.i.d. outcomes of the conditioned uniform POVM.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §7.1.1, printed p. 20 (PDF p. 22): "X₁, …, X_n are i.i.d. estimators obtained by applying the
conditioned POVM to the n input copies."

`U₁, …, U_n : Ω → ℂ^d` are measurable, mutually independent under `P`, and each has law
`condUniformLaw σ`. -/
def IsCondUniformSample {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d n : ℕ}
    (σ : Matrix (Fin d) (Fin d) ℂ) (U : Fin n → Ω → EuclideanSpace ℂ (Fin d)) : Prop :=
  (∀ i, Measurable (U i)) ∧ iIndepFun U P ∧ ∀ i, P.map (U i) = condUniformLaw σ

end OptimalSpectrum.Entangled


