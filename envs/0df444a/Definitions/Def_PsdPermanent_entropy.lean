-- Prove2me | Definitions.Def_PsdPermanent_entropy
-- name    : PsdPermanent_entropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:30:42.887688+00:00
-- url     : https://prove2.me/theorems/af8df410-fd5c-4616-835e-77975e6ab43e
-- title:
--   Differential entropy $h(\mu)$, in the extended reals
-- statement:
--   For a probability density $\mu$, the **differential entropy** is
--   $$h(\mu)=-\int\mu(z)\log\mu(z)\,dz,$$
--   whenever it is well-defined. It is well-defined when the integrals of the positive part and of the negative part of $-\mu\log\mu$ are not both infinite, and its value lies in $[-\infty,+\infty]$.
--
--   **Formalization Note** The two parts are `lintegral`s, and their difference is taken in `EReal`. There $\top-\top=\bot$, so the value is the paper's only under the well-definedness predicate, which each statement carries or concludes. A Bochner integral would return $0$ where the paper has $-\infty$.
-- source:
--   N. Anari, F. Ebrahimnejad, Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive Semidefinite Matrices, arXiv:2605.21946 (held copy sha256 5e70fa63…), §3, p.4

import Mathlib
open MeasureTheory

namespace PsdPermanent

/-- The positive part of `−f log f`, integrated: the part of the differential entropy that can make it
`+∞`. -/
noncomputable def entropyPos {α : Type*} [MeasureSpace α] (f : α → ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (-(f x * Real.log (f x)))

/-- The negative part of `−f log f`, integrated: the part of the differential entropy that can make it
`−∞`. -/
noncomputable def entropyNeg {α : Type*} [MeasureSpace α] (f : α → ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (f x * Real.log (f x))

/-- The differential entropy is well-defined: its two parts are not both infinite. -/
def EntropyWellDefined {α : Type*} [MeasureSpace α] (f : α → ℝ) : Prop :=
  ¬ (entropyPos f = ⊤ ∧ entropyNeg f = ⊤)

/-- **Differential entropy, in the extended reals.**
Anari, Ebrahimnejad, *Optimal e^{(γ+o(1))n}-Approximation of the Permanent of Positive
Semidefinite Matrices*, arXiv:2605.21946 (held copy sha256 5e70fa63…), §3, p.4: "For a probability density µ on C^d, let h(µ) = −∫_{C^d} µ(z) log µ(z) dz denote
differential entropy, whenever it is well-defined."

`entropy f` is `entropyPos f − entropyNeg f` in `EReal`, for a density on any measure space (the paper
uses it on `C^d` and on `R^k`).

**Formalization Note.** A Bochner integral would return the junk value `0` at `h = −∞`, which a density
with finite second moment can attain. In `EReal`, `⊤ − ⊤ = ⊥`, so `entropy f` is the paper's `h` only
under `EntropyWellDefined f`; every statement using it carries or concludes that predicate. At
`f x = 0` the integrand is `0`, the usual `0 log 0 = 0`. -/
noncomputable def entropy {α : Type*} [MeasureSpace α] (f : α → ℝ) : EReal :=
  (entropyPos f : EReal) - (entropyNeg f : EReal)

end PsdPermanent


