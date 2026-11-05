-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_Cmat
-- name    : BauerleRiederMDP_PartialObs_Cmat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:07.205279+00:00
-- url     : https://prove2.me/theorems/b63fa518-e645-4fd2-bf3f-5cf14fddc9e6
-- title:
--   The matrix $C_n(\rho)$ of (6.7)
-- statement:
--   For a function $v$ on $\mathbb P(E_Y)$ (in (6.7), $v=d_n$) and a belief $\rho$,
--   $$
--   C_n(\rho)=\int\!\!\int d_n\big(\Phi(\rho,z)\big)\,zz^\top\,Q^R(dz\mid y)\,\rho(dy)\in\mathbb R^{d\times d},
--   $$
--   computed entrywise.
--
--   **Formalization Note** Real (Bochner) integrals of integrable functions under (FM) (finite second moments, bounded $d_n$).
-- source:
--   Bäuerle & Rieder (2011), §6.2, display after (6.7), p.185 (PDF 198)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_Phi

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The matrix `C`** of the mean-variance recursion (6.7).
Bäuerle & Rieder (2011), §6.2, display after (6.7), p.185 (PDF 198):
`C_n(ρ) = ∫ ∫ d_n(Φ(ρ, z)) z zᵀ Q^R(dz|y) ρ(dy)`, a `d × d` matrix.
`Cmat M v ρ` is this integral for `v = d_n`, entrywise.

**Formalization Note.** Real (Bochner) integrals of integrable functions under (FM)
(finite second moments, `d_n` bounded). -/
noncomputable def Cmat {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d)
    (v : ProbabilityMeasure EY → ℝ) (ρ : ProbabilityMeasure EY) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun j k => ∫ y, ∫ z, v (M.Phi ρ z) * (z j * z k) ∂M.QR y ∂(ρ : Measure EY)

end BauerleRiederMDP.PartialObs


