-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_condUniformLaw
-- name    : OptimalSpectrum_Entangled_condUniformLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:20:28.987554+00:00
-- url     : https://prove2.me/theorems/85bebe74-4b22-4940-90b8-600e5fa7f703
-- title:
--   Outcome law of the conditioned uniform POVM: $(1-\mathrm{tr}\,\sigma)\,\delta_0+d\langle u|\sigma|u\rangle\,U(du)$
-- statement:
--   On one copy of $\rho$, the unentangled scheme first measures $\{\overline\Pi,\Pi\}$. Outcome $\Pi$ (probability $1-\mathrm{tr}\,\sigma$, with $\sigma=\overline\Pi\rho\overline\Pi$) discards the copy; outcome $\overline\Pi$ leaves $\sigma/\mathrm{tr}\,\sigma$, on which the uniform POVM on $\mathbb C^d$ returns a unit vector $u$ with density $d\langle u|\sigma/\mathrm{tr}\,\sigma|u\rangle$ against $U$. Recording a discarded copy as the zero vector, the outcome law is
--
--   $$\nu_\sigma=(1-\mathrm{tr}\,\sigma)\,\delta_0+d\,\langle u|\sigma|u\rangle\,U(du),$$
--
--   a probability measure on $\mathbb C^d$ whenever $\sigma\succeq0$ and $\mathrm{tr}\,\sigma\le1$.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §7.1 and §7.1.1, p. 20 (PDF p. 22)

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_uniformSphere

open MeasureTheory
open scoped Matrix

namespace OptimalSpectrum.Entangled

/-- **Outcome law of the conditioned uniform POVM on one copy.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §7.1, printed p. 20 (PDF p. 22): "Both schemes first measure each of the n fresh copies of ρ
with {Π̄, Π}. The outcome Π̄ occurs with probability tr(σ) and, when tr(σ) > 0, leaves the normalized
state σ/tr(σ) on the small-bucket subspace. The complementary outcome Π is discarded." §7.1.1: "On
each copy retained after outcome Π̄, we apply the uniform POVM on C^d."

The outcome is recorded as a vector of `ℂ^d`: `0` for a discarded copy (probability `1 − tr σ`), and
the measured unit vector `u` for a retained one, whose law is the uniform POVM's Born density
`d⟨u|σ/tr σ|u⟩` against the uniform sphere measure `U`, times `tr σ`. So the law is
`(1 − tr σ) δ₀ + d⟨u|σ|u⟩ U(du)`, a probability measure when `σ ⪰ 0` and `tr σ ≤ 1`.

**Formalization Note.** Encoding the discarded outcome as the zero vector keeps one outcome space;
the unit sphere does not contain `0`. This form also covers `tr σ = 0`. -/
noncomputable def condUniformLaw {d : ℕ} (σ : Matrix (Fin d) (Fin d) ℂ) :
    Measure (EuclideanSpace ℂ (Fin d)) :=
  ENNReal.ofReal (1 - (Matrix.trace σ).re) • Measure.dirac 0 +
    (uniformSphere d).withDensity fun u =>
      ENNReal.ofReal ((d : ℝ) * (star (WithLp.ofLp u) ⬝ᵥ (σ *ᵥ WithLp.ofLp u)).re)

end OptimalSpectrum.Entangled


