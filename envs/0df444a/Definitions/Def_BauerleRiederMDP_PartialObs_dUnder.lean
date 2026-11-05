-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_dUnder
-- name    : BauerleRiederMDP_PartialObs_dUnder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:02.705102+00:00
-- url     : https://prove2.me/theorems/3006c648-87a1-4e73-94a5-3187a1a9381d
-- title:
--   The averaged function $\underline d_n(\rho)$ of (6.7)
-- statement:
--   For a function $v$ on $\mathbb P(E_Y)$ (in (6.7), $v=d_n$) and a belief $\rho$,
--   $$
--   \underline d_n(\rho)=\int\!\!\int d_n\big(\Phi(\rho,z)\big)\,Q^R(dz\mid y)\,\rho(dy).
--   $$
--
--   **Formalization Note** Real (Bochner) integrals; in (6.7) the integrand is bounded, since $0<d_n\le1$ (Lemma 6.2.1).
-- source:
--   Bäuerle & Rieder (2011), §6.2, display after (6.7), p.185 (PDF 198)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_Phi

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The averaged function `d̲`** of the mean-variance recursion (6.7).
Bäuerle & Rieder (2011), §6.2, display after (6.7), p.185 (PDF 198):
`d̲_n(ρ) = ∫ ∫ d_n(Φ(ρ, z)) Q^R(dz|y) ρ(dy)`.
`dUnder M v ρ` is this integral for `v = d_n`.

**Formalization Note.** Real (Bochner) integrals; in (6.7) they are applied to `d_n`, which takes
values in `(0, 1]` (Lemma 6.2.1), so the integrals are of bounded functions. -/
noncomputable def dUnder {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d)
    (v : ProbabilityMeasure EY → ℝ) (ρ : ProbabilityMeasure EY) : ℝ :=
  ∫ y, ∫ z, v (M.Phi ρ z) ∂M.QR y ∂(ρ : Measure EY)

end BauerleRiederMDP.PartialObs


