-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDoubleCosetCovolume
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDoubleCosetCovolume
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:18.146633+00:00
-- url     : https://prove2.me/theorems/816d82ec-5ee9-47dc-a7f3-1e5c73904d24
-- title:
--   PDouble Coset Covolume
-- statement:
--   Definitions and structural lemmas for PDouble Coset Covolume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PDoubleCosetCovolume.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise
set_option linter.unusedSectionVars false
noncomputable section
section Setup
variable {G G₁ G₂ : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
def doubleCosetSetoid (Φ : G ≃ₜ* G₁ × G₂) (Γ : Subgroup G) (K : Subgroup G₂) : Setoid G₂ where
  r y y' := ∃ γ ∈ Γ, ∃ k ∈ K, y' = (Φ γ).2 * y * k
  iseqv :=
    { refl := fun y => ⟨1, Γ.one_mem, 1, K.one_mem, by simp⟩
      symm := by
        rintro y y' ⟨γ, hγ, k, hk, rfl⟩
        refine ⟨γ⁻¹, Γ.inv_mem hγ, k⁻¹, K.inv_mem hk, ?_⟩
        simp [mul_assoc]
      trans := by
        rintro y y' y'' ⟨γ, hγ, k, hk, rfl⟩ ⟨γ', hγ', k', hk', rfl⟩
        refine ⟨γ' * γ, Γ.mul_mem hγ' hγ, k * k', K.mul_mem hk hk', ?_⟩
        simp [mul_assoc] }
def leftCosetSet (K : Subgroup G₂) (s : G₂) : Set G₂ := {y | s⁻¹ * y ∈ K}
def sliceMeasure (Φ : G ≃ₜ* G₁ × G₂) (μ : Measure G) (V : Set G₂) : Measure G₁ :=
  (μ.restrict (Φ ⁻¹' (univ ×ˢ V))).map fun x => (Φ x).1
variable {Φ : G ≃ₜ* G₁ × G₂} {μ : Measure G} {V : Set G₂}
variable [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁] [μ.IsHaarMeasure]
end Setup
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


