-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_SphereTorusC
-- name    : ReciprocityTheory_SemistableReduction_SphereTorusC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:33.753127+00:00
-- url     : https://prove2.me/theorems/03fd3251-2b89-4cf6-a12b-41dbce3a2f5f
-- title:
--   Sphere Torus C
-- statement:
--   Definitions and structural lemmas for Sphere Torus C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/SphereTorusC.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
open scoped Pointwise
def rotLIE {n : ℕ} (u : Fin n → Circle) : EuclideanSpace ℂ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun j => rotation (u j)
def sphereRot {n : ℕ} (u : Fin n → Circle) (z : UnitSphereC n) : UnitSphereC n :=
  ⟨rotLIE u z, by simp⟩
def blockRot {B n : ℕ} (θ : Fin B × Fin n → ℝ) (z : BlockSphere B n) : BlockSphere B n :=
  fun b => sphereRot (fun j => Circle.exp (2 * Real.pi * θ (b, j))) (z b)
end ReciprocityTheory.MultiplicativeHeights


