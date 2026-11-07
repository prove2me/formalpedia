-- Prove2me | Definitions.Def_PsdPermanent_gibbsDensity
-- name    : PsdPermanent_gibbsDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:47.120635+00:00
-- url     : https://prove2.me/theorems/bd819d3c-342f-477d-b45f-f37d42b367fb
-- title:
--   The constant $Z_U$ and the Gibbs density
-- statement:
--   For a measurable $U:\mathbb C^d\to\mathbb R\cup\{-\infty\}$, set
--   $$Z_U=\pi^{-d}\int_{\mathbb C^d}\exp(U(z)-z^\dagger z)\,dz .$$
--   When $Z_U$ is finite and positive, the **Gibbs density** is
--   $$z\longmapsto Z_U^{-1}\,\pi^{-d}\exp(U(z)-z^\dagger z).$$
--
--   **Formalization Note** $Z_U$ takes values in $[0,\infty]$, and $\exp(-\infty)=0$.
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 4, p.5

import Mathlib
import Definitions.Def_PsdPermanent_secondMoment
open MeasureTheory

namespace PsdPermanent

/-- **The normalizing constant Z_U.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 4, p.5: "Z_U = π^{−d} ∫_{C^d} exp(U(z) − z†z) dz".

**Formalization Note.** An element of `[0, ∞]`, so that "finite and positive" is a hypothesis. `U` takes
values in `EReal`; `EReal.exp ⊥ = 0`. -/
noncomputable def partitionZ {d : ℕ} (U : (Fin d → ℂ) → EReal) : ENNReal :=
  ENNReal.ofReal (Real.pi ^ d)⁻¹ * ∫⁻ z, EReal.exp (U z - ((zDaggerZ z : ℝ) : EReal))

/-- **The Gibbs density.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 4, p.5: "the Gibbs density proportional to exp(U(z) − z†z)", normalized in the proof as "the
probability density proportional to π^{−d} exp(U(z) − z†z)".

**Formalization Note.** Meaningful when `partitionZ U` is finite and positive, the hypotheses of Lemma 4.
`toReal` is harmless there, since the value is then finite for almost every `z`, and it is finite for every
`z` as soon as `U z ≠ ⊤`. -/
noncomputable def gibbsDensity {d : ℕ} (U : (Fin d → ℂ) → EReal) (z : Fin d → ℂ) : ℝ :=
  (ENNReal.ofReal (Real.pi ^ d)⁻¹ * EReal.exp (U z - ((zDaggerZ z : ℝ) : EReal)) / partitionZ U).toReal

end PsdPermanent


