-- Prove2me | Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
-- name    : SharpIntermediateSubgroupBounds_Gaussian
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:40:59.450432+00:00
-- url     : https://prove2.me/theorems/ae9aec54-6149-5795-90be-8006732739f5
-- title:
--   Gaussian
-- statement:
--   Definitions and structural lemmas for Gaussian, from Sébastien Palcoux (sebastienpalcoux/sharp-intermediate-subgroup-bounds; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sharp bounds for intervals in finite subgroup lattices development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Gaussian.lean

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
set_option autoImplicit true
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
@[simp] theorem gammaR_zero (p : ℝ) : gammaR p 0 = 1 := by
  simp [gammaR]
def qWeight (r : ℕ) : ℕ := ∑ j ∈ Finset.range r, (j + 1)
@[simp] theorem qWeight_zero : qWeight 0 = 0 := by simp [qWeight]
def frameWeight (r : ℕ) : ℕ :=
  ∑ j ∈ Finset.range r, j
@[simp] theorem frameWeight_zero : frameWeight 0 = 0 := by
  simp [frameWeight]
theorem span_eq_top_iff_linearIndependent_fin_zmod (p r : ℕ) [Fact p.Prime]
    (s : Fin r → (Fin r → ZMod p)) :
    Submodule.span (ZMod p) (Set.range s) = ⊤ ↔
      LinearIndependent (ZMod p) s := by
  constructor
  · intro hspan
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · rw [hspan]
    · simp
  · intro hs
    exact hs.span_eq_top_of_card_eq_finrank' (by simp)
def addSubgroupAsZModSubmodule {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (A : AddSubgroup V) :
    Submodule (ZMod p) V where
  carrier := A
  zero_mem' := A.zero_mem
  add_mem' := A.add_mem
  smul_mem' c x hx := by
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    exact A.nsmul_mem hx _
theorem span_toAddSubgroup_eq_addClosure_zmod {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (s : Set V) :
    (Submodule.span (ZMod p) s).toAddSubgroup = AddSubgroup.closure s := by
  apply le_antisymm
  · have hspan : Submodule.span (ZMod p) s ≤
        addSubgroupAsZModSubmodule (AddSubgroup.closure s) :=
      Submodule.span_le.mpr AddSubgroup.subset_closure
    intro x hx
    exact hspan hx
  · rw [AddSubgroup.closure_le]
    intro x hx
    exact Submodule.subset_span hx
theorem addClosure_eq_top_iff_span_eq_top_zmod {p : ℕ} [Fact p.Prime]
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (s : Set V) :
    AddSubgroup.closure s = ⊤ ↔ Submodule.span (ZMod p) s = ⊤ := by
  rw [← span_toAddSubgroup_eq_addClosure_zmod (p := p) s]
  constructor
  · intro h
    apply Submodule.toAddSubgroup_injective
    simpa using h
  · intro h
    rw [h]
    rfl
theorem addClosure_eq_top_iff_linearIndependent_fin_zmod
    (p r : ℕ) [Fact p.Prime] (s : Fin r → (Fin r → ZMod p)) :
    AddSubgroup.closure (Set.range s) = ⊤ ↔ LinearIndependent (ZMod p) s := by
  rw [addClosure_eq_top_iff_span_eq_top_zmod (p := p) (Set.range s),
    span_eq_top_iff_linearIndependent_fin_zmod p r s]
abbrev GeneratingFramesFinZMod (p r : ℕ) :=
  {s : Fin r → (Fin r → ZMod p) //
    AddSubgroup.closure (Set.range s) = ⊤}
def generatingFramesEquivOrderedBasesFinZMod (p r : ℕ) [Fact p.Prime] :
    GeneratingFramesFinZMod p r ≃
      LinearIndependentFrames (ZMod p) (Fin r → ZMod p) r :=
  Equiv.subtypeEquiv (Equiv.refl _) fun s ↦
    addClosure_eq_top_iff_linearIndependent_fin_zmod p r s
noncomputable def normalizedGaussianRight (p a j : ℕ) : ℝ :=
  if j ≤ a then (p : ℝ)⁻¹ ^ (a * a) * (qBinom p (2 * a) (a + j) : ℝ) else 0
noncomputable def normalizedGaussianCentered (p a : ℕ) (j : ℤ) : ℝ :=
  normalizedGaussianRight p a j.natAbs
def centerMultiplicity (j : ℕ) : ℕ := if j = 0 then 1 else 2
noncomputable def evenGaussianSummand (p a j : ℕ) : ℝ :=
  (centerMultiplicity j : ℝ) * normalizedGaussianRight p a j
noncomputable def evenGaussianLimitSummand (p j : ℕ) : ℝ :=
  (centerMultiplicity j : ℝ) *
    (eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j))
noncomputable def quarterShiftScale (p : ℝ) : ℝ :=
  Real.exp (-Real.log p / 4)
noncomputable def oddGaussianConstant (p : ℝ) : ℝ :=
  eulerC p * shiftedTheta p (1 / 2)
noncomputable def normalizedOddGaussianRight (p a j : ℕ) : ℝ :=
  if j ≤ a then
    (p : ℝ)⁻¹ ^ (a * (a + 1)) *
      (qBinom p (2 * a + 1) (a + 1 + j) : ℝ)
  else 0
noncomputable def oddGaussianSummand (p a j : ℕ) : ℝ :=
  2 * quarterShiftScale (p : ℝ) * normalizedOddGaussianRight p a j
noncomputable def oddGaussianLimitSummand (p j : ℕ) : ℝ :=
  2 * quarterShiftScale (p : ℝ) *
    (eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * (j + 1)))
noncomputable def primePowerU (p n : ℕ) : ℝ :=
  ∑ r : Fin (n + 1),
    (p : ℝ) ^ (r.val * (n - r.val)) * (gammaR (p : ℝ) r.val)⁻¹
noncomputable def evenUSummand (p a j : ℕ) : ℝ :=
  if j = 0 then (gammaR (p : ℝ) a)⁻¹
  else if j ≤ a then
    (p : ℝ)⁻¹ ^ (j * j) *
      ((gammaR (p : ℝ) (a + j))⁻¹ + (gammaR (p : ℝ) (a - j))⁻¹)
  else 0
end SharpIntermediateSubgroupBounds


