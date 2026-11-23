-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsE8IsSharpBasis
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsE8IsSharpBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:09:10.025795+00:00
-- url     : https://prove2.me/theorems/8b666c7b-026b-4721-88a6-a1bb71470be9
-- title:
--   Exists Is E8 Is Sharp Basis
-- statement:
--   Definitions and structural lemmas for Exists Is E8 Is Sharp Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIsE8IsSharpBasis.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_W8AddTransposeEqE8
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.ZM
def twistSnd {h : ℕ} (A : Matrix (Fin 8) (Fin 8) ℤ) :
    (Fin 8 → (Fin h ⊕ Fin h → ℤ)) →ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) where
  toFun y := fun u => Sum.elim (fun a => y u (.inl a)) (fun a => A.mulVec (fun w => y w (.inr a)) u)
  map_add' y y' := by
    funext u c
    rcases c with a | a
    · simp
    · simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' r y := by
    funext u c
    rcases c with a | a
    · simp
    · simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
def sharpIndex (h : ℕ) : Fin 8 × (Fin h ⊕ Fin h) ≃ Fin (2 * (8 * h)) :=
  (Equiv.prodSumDistrib _ _ _).trans <|
    (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans <|
      finSumFinEquiv.trans (finCongr (two_mul _).symm)
def sharpReindex (h : ℕ) : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) where
  toFun x := fun u c => x (sharpIndex h (u, c))
  invFun y := fun i => y ((sharpIndex h).symm i).1 ((sharpIndex h).symm i).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by funext i; simp
  right_inv y := by funext u c; simp
end GlobalTheory.ZM
end


