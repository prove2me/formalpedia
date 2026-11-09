-- Prove2me | Definitions.Def_GevreyGibbsSep_qOutputLaw
-- name    : GevreyGibbsSep_qOutputLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:44:33.885064+00:00
-- url     : https://prove2.me/theorems/18f990d2-4869-4dda-ac1a-a612b660d302
-- title:
--   Output law $\eta$ of a first-order quantum algorithm
-- statement:
--   The **output law** $\eta$ on $\mathbb T^d$ of a first-order quantum algorithm on the instance $E$: the final state $|\psi_T\rangle$ is measured in the computational basis, giving outcome $z$ with probability $|\psi_T(z)|^2$, and the post-processing rule turns $z$ into a sample with law $\mathrm{post}(z)$:
--   $$\eta=\sum_z|\psi_T(z)|^2\,\mathrm{post}(z).$$
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Theorem 2, pp.10–11

import Mathlib
import Definitions.Def_GevreyGibbsSep_Torus
import Definitions.Def_GevreyGibbsSep_QReg
import Definitions.Def_GevreyGibbsSep_FirstOrderQAlg
import Definitions.Def_GevreyGibbsSep_finalState

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The output law `η` of a first-order quantum algorithm on the instance `E`: the final state is
measured in the computational basis, outcome `z` with probability `|ψ_T(z)|²`, and the
post-processing kernel turns `z` into a point of `T^d` (arXiv:2608.24527 (sha256 d4fd40eb…),
Theorem 2, pp.10–11: "returns a sample from a random variable X ∼ η"). -/
noncomputable def qOutputLaw {d : ℕ} {W : Type} {T : ℕ} (A : FirstOrderQAlg d W T)
    (E : (Fin d → ℝ) → ℝ) : Measure (Torus d) :=
  Measure.sum (fun z : QReg d W =>
    ENNReal.ofReal (‖(finalState A E : QReg d W → ℂ) z‖ ^ 2) • (A.post z : Measure (Torus d)))

end GevreyGibbsSep


