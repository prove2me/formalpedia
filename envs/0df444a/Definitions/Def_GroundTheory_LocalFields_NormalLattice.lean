-- Prove2me | Definitions.Def_GroundTheory_LocalFields_NormalLattice
-- name    : GroundTheory_LocalFields_NormalLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:07.166322+00:00
-- url     : https://prove2.me/theorems/58608c6d-e53c-49b7-a044-00f1eca2302c
-- title:
--   Normal Lattice
-- statement:
--   Definitions and structural lemmas for Normal Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
section Lattice
def normalLattice (π : 𝒪[K]) (θ : L) (s : ℕ) : Submodule 𝒪[K] L :=
  Submodule.span 𝒪[K] (Set.range fun σ : Gal(L/K) => π ^ s • σ θ)
variable (π : 𝒪[K]) (θ : L)
end Lattice
section Integral
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [ValuativeExtension K L]
variable (π : 𝒪[K]) (θ : L)
variable [IsGalois K L]
end Integral
section Product
variable (π : 𝒪[K]) (θ : L)
end Product
section Complete
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (π : 𝒪[K]) (θ : L)
variable {π θ}
end Complete
section Existence
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
variable [IsGalois K L]
end Existence
section Open
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L]
variable (π : 𝒪[K]) (θ : L)
end Open
end GroundTheory.LocalField


