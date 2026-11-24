-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineSemipositive
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualLineSemipositive
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:04:02.183734+00:00
-- url     : https://prove2.me/theorems/59d4f3fe-2510-4a58-8e8d-41e8a5548d56
-- title:
--   PDual Line Semipositive
-- statement:
--   Definitions and structural lemmas for PDual Line Semipositive, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualLineSemipositive.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLineDegreeDual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix NumberField
open scoped ComplexOrder
noncomputable section
namespace DualLineSemipositiveAlt
open scoped MatrixOrder in

theorem exists_conjTranspose_mul_self {n : Type} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
    (hM : M.PosSemidef) : ∃ B : Matrix n n ℂ, M = Bᴴ * B := by
  have h0 : 0 ≤ M := Matrix.nonneg_iff_posSemidef.mpr hM
  refine ⟨CFC.sqrt M, ?_⟩
  rw [← Matrix.star_eq_conjTranspose, (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self M h0]
variable {K : Type} [Field K] [NumberField K] {i : ℕ} {T : Type} [Fintype T] [DecidableEq T]
def factor (F : HermLattice K i) (σ : K →+* ℂ) : Matrix (Fin i) (Fin i) ℂ :=
  Classical.choose (exists_conjTranspose_mul_self (F.posDef σ).posSemidef)
def coordMap {F : HermLattice K i} (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    ((Σ _ : Unit, T) → ℂ) →ₗ[ℂ] ((K →+* ℂ) × Fin i → ℂ) :=
  (LinearMap.pi fun p : (K →+* ℂ) × Fin i => (LinearMap.proj p.2) ∘ₗ (factor F p.1).mulVecLin ∘ₗ
      (LinearMap.pi fun k => LinearMap.proj (p.1, k))) ∘ₗ (dualRecover b hb).toLinearMap ∘ₗ
    (LinearMap.pi fun t => LinearMap.proj (⟨(), t⟩ : Σ _ : Unit, T))
end DualLineSemipositiveAlt
end
end GroundTheory.Heights₂.Heights


