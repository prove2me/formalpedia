-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasurableEnormComposition
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasurableEnormComposition
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T05:12:08.492108+00:00
-- url     : https://prove2.me/theorems/664e716e-8bbe-532c-b0fd-9bc38d315735
-- title:
--   Measurable Enorm Composition
-- statement:
--   Definitions and structural lemmas for Measurable Enorm Composition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasurableEnormComposition.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousSandwichedProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
namespace Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
def abelian₂ (e0 : Mx k r → ℂ) (γ : Mx k r) (μp μq : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r))
    (x y : Formalism.QuantumDeterminants.Mt k r) : ℝ≥0∞ :=
  ∫⁻ p, ∫⁻ q, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * γ * (Matrix.of q.1 * Matrix.of q.2)⁻¹ *
    Matrix.of y)‖ₑ ∂μq ∂μp
def Lam1 (e0 : Mx k r → ℂ) (μp : Measure (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) (x y : Formalism.QuantumDeterminants.Mt k r) :
    ℝ≥0∞ :=
  ∫⁻ p, ‖e0 ((Matrix.of x)⁻¹ * (Matrix.of p.1 * Matrix.of p.2) * Matrix.of y)‖ₑ ∂μp
end Formalism.FourierDecayAlt.P.S3dx4


