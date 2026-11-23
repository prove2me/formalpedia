-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_HasFDerivAtNmat
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_HasFDerivAtNmat
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:14.989558+00:00
-- url     : https://prove2.me/theorems/602d7e57-eb06-47f5-9f27-413b52d091e8
-- title:
--   Has FDeriv At Nmat
-- statement:
--   Definitions and structural lemmas for Has FDeriv At Nmat, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/HasFDerivAtNmat.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_DetOfBlockDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates Matrix Topology Filter
open scoped Classical
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
def vecOf (z : V (nd X)) : Ent X → ℂ := fun e => z (Fintype.equivFin (Ent X) e)
def Lin (τ : X.Ψ) : V (nd X) →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ where
  toFun z := Matrix.of (embF X (vecOf X z) τ)
  map_add' z w := by
    ext a c
    simp only [Matrix.of_apply, Matrix.add_apply, embF, vecOf]
    split_ifs
    · rfl
    · simp
  map_smul' t z := by
    ext a c
    simp only [Matrix.of_apply, Matrix.smul_apply, embF, vecOf, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · rfl
    · simp
def entryL (a c : Fin r) : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] ℂ where
  toFun M := M a c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end ReciprocityTheory.ChartRestriction.G.AR.Inst.KapPf


