-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:18:03.404406+00:00
-- url     : https://prove2.me/theorems/af509142-a5ed-4488-b9e1-1b71d0216467
-- title:
--   Unitary Invariant Gaussian
-- statement:
--   Definitions and structural lemmas for Unitary Invariant Gaussian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnitaryInvariantGaussian.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G Matrix MeasureTheory Filter Topology
namespace Formalism.FourierDecayAlt.P.G8
instance sigmaFinite_mu (β : ℂ) : SigmaFinite (mu β) := by unfold mu; infer_instance
noncomputable def gK (δ p q : ℝ) (z : ℝ × ℝ) : ℂ :=
  Complex.exp (-((δ : ℂ) + Complex.I * p) * (z.2 : ℂ) ^ 2 + (-2 * Complex.I * q * z.1) * (z.2 : ℂ) +
    -((δ : ℂ) - Complex.I * p) * (z.1 : ℂ) ^ 2)
noncomputable def diagF (β : ℂ) (d : ℕ) (σ : Fin d → ℝ) (t : ℂ) (δ : ℝ) (y : Fin d → ℂ) : ℂ :=
  ((Real.exp (-δ * ∑ k, ‖y k‖ ^ 2) : ℝ) : ℂ) *
    psi β ((y ⬝ᵥ (Matrix.diagonal (fun i => ((σ i : ℝ) : ℂ)) *ᵥ y)) / (2 * t))
end Formalism.FourierDecayAlt.P.G8
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


