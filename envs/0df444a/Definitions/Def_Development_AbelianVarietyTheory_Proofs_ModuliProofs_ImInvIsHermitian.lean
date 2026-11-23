-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImInvIsHermitian
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImInvIsHermitian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:23:02.487141+00:00
-- url     : https://prove2.me/theorems/c6ad32e6-5feb-4b5d-bd23-d84db2b8eee5
-- title:
--   Im Inv Is Hermitian
-- statement:
--   Definitions and structural lemmas for Im Inv Is Hermitian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImInvIsHermitian.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.SharpObj
variable {h : ℕ}
def per (τ : Matrix (Fin h) (Fin h) ℂ) : (Fin h ⊕ Fin h → ℤ) →ₗ[ℤ] (Fin h → ℂ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun x i => τ.mulVec (fun i' => (x (.inl i') : ℂ)) i + (x (.inr i) : ℂ)
      map_zero' := by ext i; simp [Matrix.mulVec, dotProduct]
      map_add' := fun x y => by
        ext i
        simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]
        ring }
def imInv (τ : Matrix (Fin h) (Fin h) ℂ) : Matrix (Fin h) (Fin h) ℂ :=
  (τ.map Complex.im)⁻¹.map fun x : ℝ => (x : ℂ)
variable {τ : Matrix (Fin h) (Fin h) ℂ}
def turn (h : ℕ) : (Fin h ⊕ Fin h → ℤ) ≃ₗ[ℤ] (Fin h ⊕ Fin h → ℤ) where
  toFun x := Sum.elim (fun i => -x (.inr i)) (fun i => x (.inl i))
  invFun x := Sum.elim (fun i => x (.inr i)) (fun i => -x (.inl i))
  map_add' x y := by ext (i | i) <;> simp [add_comm]
  map_smul' c x := by ext (i | i) <;> simp
  left_inv x := by ext (i | i) <;> simp
  right_inv x := by ext (i | i) <;> simp
end GlobalTheory.SharpObj
end


