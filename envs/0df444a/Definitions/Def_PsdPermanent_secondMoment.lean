-- Prove2me | Definitions.Def_PsdPermanent_secondMoment
-- name    : PsdPermanent_secondMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:53.35022+00:00
-- url     : https://prove2.me/theorems/d81247ed-ac76-4d74-952f-44093649c7c0
-- title:
--   The Hermitian second moment $M=\mathbb E_\mu[ZZ^\dagger]$
-- statement:
--   For a probability density $\mu$ on $\mathbb C^d$, the second moment is finite if $\mathbb E_\mu[Z^\dagger Z]<\infty$, and then
--   $$M=\mathbb E_\mu[ZZ^\dagger],\qquad M_{ab}=\int z_a\overline{z_b}\,\mu(z)\,dz .$$
--   It is the matrix the upper bound of Theorem 7 inserts into the relaxation.
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 3, p.4

import Mathlib
open MeasureTheory

namespace PsdPermanent

/-- `z†z = ∑_a |z_a|²`. -/
noncomputable def zDaggerZ {d : ℕ} (z : Fin d → ℂ) : ℝ := ∑ a, Complex.normSq (z a)

/-- Finite second moment of a density on `C^d`: `E_µ[Z†Z] < ∞`. -/
def FiniteSecondMoment {d : ℕ} (f : (Fin d → ℂ) → ℝ) : Prop :=
  Integrable (fun z => zDaggerZ z * f z)

/-- **The Hermitian second moment matrix.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 3, p.4: "M = E_µ[ZZ†]".

**Formalization Note.** The entry `(a, b)` is `∫ z_a conj(z_b) f(z) dz`. It is the paper's expectation
under `FiniteSecondMoment f`, which every statement using it carries or concludes. -/
noncomputable def secondMoment {d : ℕ} (f : (Fin d → ℂ) → ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun a b => ∫ z, z a * star (z b) * (f z : ℂ)

end PsdPermanent


