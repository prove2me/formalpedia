-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
-- name    : GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:17.820041+00:00
-- url     : https://prove2.me/theorems/0ad7e3af-0703-4caa-a83d-073fa07aa62e
-- title:
--   Anisotropic
-- statement:
--   Definitions and structural lemmas for Anisotropic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Anisotropic.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace GroundTheory.Automorphic
open Module Matrix TensorProduct Topology Metric
noncomputable section
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
section Form
variable (K) (H : Matrix ι ι E) (R : Type*) [CommRing R] [Algebra K R]
def hermValue (x : ι → R ⊗[K] E) : R ⊗[K] E :=
  (fun i => conjBase K E R (x i)) ⬝ᵥ (baseMatrix K H R *ᵥ x)
variable {K H R}
end Form
section Compact
attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor
variable (H : Matrix ι ι E)
variable (R : Type*) [NontriviallyNormedField R] [ProperSpace R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
def anisoVecCoords (x : ι → R ⊗[K] E) : ι × κ → R :=
  fun p => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2
def anisoVecOfCoords (y : ι × κ → R) : ι → R ⊗[K] E :=
  fun i => (tensorCoordsHomeomorph R b).symm fun k => y (i, k)
variable {R b}
variable (R b)
def anisoForm (y : ι × κ → R) : κ → R :=
  tensorCoordsHomeomorph R b (hermValue K H R (anisoVecOfCoords R b y))
variable {H R b}
variable (H R)
end Compact
section RealPlace
open NumberField
variable (H : Matrix ι ι E)
abbrev completionNontriviallyNormedField (w : InfinitePlace K) :
    NontriviallyNormedField w.Completion :=
  { (inferInstance : NormedField w.Completion) with
    non_trivial := ⟨2, by
      have := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) 2
      rw [← this, map_ofNat]
      norm_num⟩ }
def IsHermDefiniteAt (w : InfinitePlace K) (hw : w.IsReal) : Prop :=
  (∀ x : ι → w.Completion ⊗[K] E, x ≠ 0 → ∃ t : w.Completion,
      hermValue K H w.Completion x = algebraMap w.Completion (w.Completion ⊗[K] E) t ∧
        0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal hw t) ∨
    ∀ x : ι → w.Completion ⊗[K] E, x ≠ 0 → ∃ t : w.Completion,
      hermValue K H w.Completion x = algebraMap w.Completion (w.Completion ⊗[K] E) t ∧
        InfinitePlace.Completion.extensionEmbeddingOfIsReal hw t < 0
variable {H}
variable (H)
end RealPlace
end
end GroundTheory.Automorphic


