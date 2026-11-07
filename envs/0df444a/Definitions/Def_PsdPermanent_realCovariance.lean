-- Prove2me | Definitions.Def_PsdPermanent_realCovariance
-- name    : PsdPermanent_realCovariance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:51.281352+00:00
-- url     : https://prove2.me/theorems/db454c1c-6685-45e5-a5af-c90a7c03c031
-- title:
--   Mean and covariance of a density on $\mathbb R^k$
-- statement:
--   For a density on $\mathbb R^k$ with finite second moment, with $Y$ distributed according to it, the mean is $\mathbb E[Y]$ and the covariance matrix is
--   $$\Sigma=\mathbb E[(Y-\mathbb E[Y])(Y-\mathbb E[Y])^\top].$$
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 2, p.4

import Mathlib
open MeasureTheory

namespace PsdPermanent

/-- Finite second moment of a density on `R^k`. -/
def FiniteSecondMomentReal {k : ℕ} (f : (Fin k → ℝ) → ℝ) : Prop :=
  Integrable (fun y => (∑ a, y a ^ 2) * f y)

/-- The mean `E[Y]` of a density on `R^k`. -/
noncomputable def realMean {k : ℕ} (f : (Fin k → ℝ) → ℝ) : Fin k → ℝ :=
  fun a => ∫ y, y a * f y

/-- **The covariance matrix.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), Lemma 2, p.4: "Σ = E[(Y − E[Y])(Y − E[Y])^⊤]".

**Formalization Note.** Bochner integrals, the paper's expectations under `FiniteSecondMomentReal f`,
which every statement using them carries. -/
noncomputable def realCovariance {k : ℕ} (f : (Fin k → ℝ) → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun a b => ∫ y, (y a - realMean f a) * (y b - realMean f b) * f y

end PsdPermanent


