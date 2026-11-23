-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchrodingerIntertwinerIntegralMatrices
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchrodingerIntertwinerIntegralMatrices
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:07.532841+00:00
-- url     : https://prove2.me/theorems/cf7ccea9-a565-464e-95be-4afd2ae56da8
-- title:
--   Exists Schrodinger Intertwiner Integral Matrices
-- statement:
--   Definitions and structural lemmas for Exists Schrodinger Intertwiner Integral Matrices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsSchrodingerIntertwinerIntegralMatrices.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
noncomputable section
namespace GlobalTheory.SchrodExist
open GlobalTheory.PlaceModel
def intLat (k : Type) [Field k] [ValuativeRel k] (Y Y' : Type) : AddSubgroup (Matrix Y Y' k) where
  carrier := {x | ∀ r q, x r q ∈ 𝒪[k]}
  add_mem' := by
    intro a b ha hb r q
    rw [Matrix.add_apply]
    exact add_mem (ha r q) (hb r q)
  zero_mem' := by
    intro r q
    rw [Matrix.zero_apply]
    exact zero_mem _
  neg_mem' := by
    intro a ha r q
    rw [Matrix.neg_apply]
    exact neg_mem (ha r q)
def annLat {k : Type} [Field k] [ValuativeRel k] {Y Y' Z : Type} [AddCommGroup Z]
    (χ : Matrix Y Y' k → Z → ℂ) (hr : ∀ a z z', χ a (z + z') = χ a z * χ a z') (h0 : ∀ a, χ a 0 = 1) :
    AddSubgroup Z where
  carrier := {z | ∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → χ u z = 1}
  add_mem' := by
    intro a b ha hb u hu
    rw [hr, ha u hu, hb u hu, one_mul]
  zero_mem' := fun u _ => h0 u
  neg_mem' := by
    intro z hz u hu
    have e := hr u (-z) z
    rw [neg_add_cancel, h0, hz u hu, mul_one] at e
    exact e.symm
open Classical in

def liftZ {A Z : Type} [AddCommGroup Z] [TopologicalSpace A] : SB A →ₗ[ℂ] (A × Z → ℂ) where
  toFun := fun Φ g => if g.2 = 0 then Φ.1 g.1 else 0
  map_add' := by
    intro a b
    funext g
    by_cases h : g.2 = 0 <;> simp [h]
  map_smul' := by
    intro c a
    funext g
    by_cases h : g.2 = 0 <;> simp [h]
end GlobalTheory.SchrodExist


