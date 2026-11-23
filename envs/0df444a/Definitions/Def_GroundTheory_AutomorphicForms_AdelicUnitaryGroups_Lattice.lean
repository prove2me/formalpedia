-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Lattice
-- name    : GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Lattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:25.024449+00:00
-- url     : https://prove2.me/theorems/12335b98-8ccb-4493-a585-685077ed052e
-- title:
--   Lattice
-- statement:
--   Definitions and structural lemmas for Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Lattice.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply


set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace GroundTheory.Automorphic
open Module Matrix TensorProduct
noncomputable section
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {R : Type*} [CommRing R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable (ι R) in

def stdLattice (O : Subring R) : Set (ι → R ⊗[K] E) :=
  {x | ∀ i k, (Algebra.TensorProduct.basis R b).repr (x i) k ∈ O}
variable (R) in

def latticeStabilizer (O : Subring R) : Subgroup (unitaryPoints K E H R) where
  carrier := {g | ∀ x ∈ stdLattice ι R b O, unitaryMat g *ᵥ x ∈ stdLattice ι R b O ∧
    unitaryMat g⁻¹ *ᵥ x ∈ stdLattice ι R b O}
  one_mem' x hx := by
    have h1 : unitaryMat (1 : unitaryPoints K E H R) = 1 := rfl
    simp only [inv_one, h1, Matrix.one_mulVec]
    exact ⟨hx, hx⟩
  mul_mem' {g h} hg hh x hx := by
    refine ⟨?_, ?_⟩
    · have : unitaryMat (g * h) = unitaryMat g * unitaryMat h := rfl
      rw [this, ← Matrix.mulVec_mulVec]
      exact (hg _ (hh x hx).1).1
    · have : unitaryMat (g * h)⁻¹ = unitaryMat h⁻¹ * unitaryMat g⁻¹ := by
        rw [_root_.mul_inv_rev]
        rfl
      rw [this, ← Matrix.mulVec_mulVec]
      exact (hh _ (hg x hx).2).2
  inv_mem' {g} hg x hx := by
    rw [inv_inv]
    exact ⟨(hg x hx).2, (hg x hx).1⟩
variable {H b}
variable (b) in

def IsAdapted (O : Subring R) : Prop :=
  (∀ k, algebraMap K R (b.repr 1 k) ∈ O) ∧ ∀ k l m, algebraMap K R (b.repr (b k * b l) m) ∈ O
end
end GroundTheory.Automorphic


