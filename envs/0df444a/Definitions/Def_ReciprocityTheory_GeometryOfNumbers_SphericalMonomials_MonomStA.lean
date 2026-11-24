-- Prove2me | Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA
-- name    : ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonomStA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:56.727598+00:00
-- url     : https://prove2.me/theorems/79f0c4a9-5c52-4688-879d-fd36fe7526f5
-- title:
--   Monom St A
-- statement:
--   Definitions and structural lemmas for Monom St A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/SphericalMonomials/MonomStA.lean

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_GaussSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.GeometryOfNumbersTheory
open MeasureTheory Metric Set
section polar
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
end polar
section eucl
variable (N : ℕ)
def sphMonomL : (Fin N → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin N) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin N => ℂ)).symm
def sphMonomMu : Measure (EuclideanSpace ℂ (Fin N)) :=
  (volume : Measure (Fin N → ℂ)).map (sphMonomL N)
instance sphMonomMu_isAddHaar : (sphMonomMu N).IsAddHaarMeasure := by
  unfold sphMonomMu; infer_instance
end eucl
section key
variable {N : ℕ}
end key
end ReciprocityTheory.GeometryOfNumbersTheory


