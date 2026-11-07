-- Prove2me | Definitions.Def_PsdPermanent_IsProbDensity
-- name    : PsdPermanent_IsProbDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:41.412816+00:00
-- url     : https://prove2.me/theorems/9ae9fea8-2be4-41ec-9cf1-6d07c1487277
-- title:
--   Probability density
-- statement:
--   A **probability density** on a measure space is a measurable nonnegative function with total integral $1$.
--
--   **Formalization Note** The function is Borel and nonnegative at every point. Every density has such a version, and the paper's quantities depend only on the almost-everywhere class.
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), §3, pp.3–4

import Mathlib
open MeasureTheory

namespace PsdPermanent

/-- **Probability density.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), §3, pp.3–4 ("a probability density µ on C^d").

**Formalization Note.** A Borel, everywhere nonnegative function of total mass one with respect to the
ambient `volume`. Every density has such a version, and every quantity of the paper depends only on
its almost-everywhere class. -/
def IsProbDensity {α : Type*} [MeasureSpace α] (f : α → ℝ) : Prop :=
  Measurable f ∧ (∀ x, 0 ≤ f x) ∧ ∫⁻ x, ENNReal.ofReal (f x) = 1

end PsdPermanent


