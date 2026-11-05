-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_ell
-- name    : BauerleRiederMDP_PartialObs_ell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:01.702235+00:00
-- url     : https://prove2.me/theorems/a4d158d3-3a7f-4b88-a898-9e71021f1487
-- title:
--   The vector $\ell_n(\rho)$ of (6.7)
-- statement:
--   For a function $v$ on $\mathbb P(E_Y)$ (in (6.7), $v=d_n$) and a belief $\rho$,
--   $$
--   \ell_n(\rho)=\int\!\!\int d_n\big(\Phi(\rho,z)\big)\,z\,Q^R(dz\mid y)\,\rho(dy)\in\mathbb R^d,
--   $$
--   computed componentwise.
--
--   **Formalization Note** Real (Bochner) integrals of integrable functions under (FM).
-- source:
--   Bäuerle & Rieder (2011), §6.2, display after (6.7), p.185 (PDF 198)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_Phi

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The vector `ℓ`** of the mean-variance recursion (6.7).
Bäuerle & Rieder (2011), §6.2, display after (6.7), p.185 (PDF 198):
`ℓ_n(ρ) = ∫ ∫ d_n(Φ(ρ, z)) z Q^R(dz|y) ρ(dy) ∈ ℝ^d`.
`ell M v ρ` is this integral for `v = d_n`, componentwise.

**Formalization Note.** Real (Bochner) integrals; `d_n` is bounded (Lemma 6.2.1) and `R` has
finite moments under (FM), so they are integrals of integrable functions. -/
noncomputable def ell {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d)
    (v : ProbabilityMeasure EY → ℝ) (ρ : ProbabilityMeasure EY) : Fin d → ℝ :=
  fun j => ∫ y, ∫ z, v (M.Phi ρ z) * z j ∂M.QR y ∂(ρ : Measure EY)

end BauerleRiederMDP.PartialObs


