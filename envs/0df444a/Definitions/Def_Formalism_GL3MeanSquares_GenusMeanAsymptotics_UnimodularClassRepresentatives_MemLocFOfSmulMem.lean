-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemLocFOfSmulMem
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemLocFOfSmulMem
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T09:33:22.4595+00:00
-- url     : https://prove2.me/theorems/22382fea-9dac-47ec-b6ea-77cc532622c5
-- title:
--   Mem Loc FOf Smul Mem
-- statement:
--   Definitions and structural lemmas for Mem Loc FOf Smul Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemLocFOfSmulMem.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsDualBound
import Definitions.Def_Lemmata_GeneralBFactLeftRest_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace RedC
def redEnd (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : V ≃ₗ[K] V) (hX : X ∈ glSub A) :
    Module.End (𝓞 K) (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)) :=
  Submodule.mapQ _ _ (((X : V →ₗ[K] V).restrictScalars (𝓞 K)).restrict fun _ hx => apply_mem hX hx)
    (fun x hx => by
      rw [Submodule.mem_comap, Submodule.mem_smul_top_iff]
      rw [Submodule.mem_smul_top_iff] at hx
      exact apply_mem_smul hX _ hx)
end RedC
end Formalism.HermitianLattices.Ext.L3.D2


