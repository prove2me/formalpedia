-- Prove2me | Definitions.Def_NoHair_spatialRicciEnergyDensity
-- name    : NoHair_spatialRicciEnergyDensity
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-23T12:27:25.660446+00:00
-- url     : https://prove2.me/theorems/87675749-8041-47cd-9171-ff3d10a62a20
-- title:
--   Riemannian Ricci energy density in a coordinate chart
-- statement:
--   The Ricci tensor is contracted with two inverse metrics and multiplied by the square root of the metric determinant. Its integral against a coordinate bump is the corresponding localized squared Ricci norm integrated with Riemannian volume.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_scalarFlatMassDeformation
import Mathlib.Analysis.Matrix.Order

noncomputable section
open Matrix
open scoped Kronecker
namespace NoHair

/-- The density of the squared norm of the coordinate Ricci tensor with respect to Lebesgue measure. -/
def spatialRicciEnergyDensity (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (x : ADMPoint) : ℝ :=
  let v := fun a : Fin 3 × Fin 3 => spatialRicciTensor h x a.1 a.2
  Real.sqrt (h x).det * dotProduct v (((h x)⁻¹ ⊗ₖ (h x)⁻¹) *ᵥ v)

end NoHair


