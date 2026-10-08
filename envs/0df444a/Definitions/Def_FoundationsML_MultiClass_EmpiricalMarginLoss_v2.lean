-- Prove2me | Definitions.Def_FoundationsML_MultiClass_EmpiricalMarginLoss_v2
-- name    : FoundationsML_MultiClass_EmpiricalMarginLoss_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:32:25.115788+00:00
-- url     : https://prove2.me/theorems/9c1268c1-9f19-4bdf-b7a8-c1250ff56c58
-- title:
--   Multi-class empirical margin loss (Eq. 9.5) — re-issued on the corrected margin
-- statement:
--   **Empirical margin loss, multi-class (Eq. (9.5), p. 215, PDF p. 232).** $\hat R_{S,\rho}(h) = \frac1m\sum_{i=1}^m \Phi_\rho(\rho_h(x_i,y_i))$, with $\Phi_\rho$ the margin loss function of Definition 5.5 and $y_i = f(x_i)$.
--
--   **Formalization Note.** Identical to the retired module except that it is built on the corrected `MarginFunction` (`_v2`); for $m=0$ the value is `0`, outside the book's domain $m\ge1$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, Eq. (9.5), p. 215 (PDF p. 232)

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_MarginFunction_v2
import Definitions.Def_FoundationsML_MultiClass_MarginLossFunction

namespace FoundationsML.MultiClass

/-- The empirical margin loss of a multi-class scoring function `h : X × Y → ℝ` on a sample
`S : Fin m → X` against a target labeling function `f : X → Y` (Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, Eq. (9.5), p. 215, PDF
p. 232): `R̂_{S,ρ}(h) = (1/m) ∑_{i=1}^m Φ_ρ(ρ_h(x_i,y_i))`. Re-issued on top of the corrected
`MarginFunction` (module `..._MarginFunction_v2`, maximum over exactly the labels `y' ≠ y`);
for `m = 0` the value is `0` (Lean's `1/0 = 0`), outside the book's domain `m ≥ 1`. -/
noncomputable def EmpiricalMarginLoss {X Y : Type*} {m : ℕ}
    (ρ : ℝ) (S : Fin m → X) (f : X → Y) (h : X × Y → ℝ) : ℝ :=
  (1 / (m : ℝ)) * ∑ i, MarginLossFunction ρ (MarginFunction h (S i) (f (S i)))

end FoundationsML.MultiClass


