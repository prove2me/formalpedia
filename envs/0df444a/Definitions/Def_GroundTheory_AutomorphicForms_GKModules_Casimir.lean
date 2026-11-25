-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
-- name    : GroundTheory_AutomorphicForms_GKModules_Casimir
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T00:09:19.545193+00:00
-- url     : https://prove2.me/theorems/1d0f99bf-37e7-48bc-ace9-8b5dfeae7917
-- title:
--   Casimir
-- statement:
--   Definitions and structural lemmas for Casimir, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GKModules/Casimir.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ZKFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Automorphic
open Set Filter Topology
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
section Casimir
variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
variable (B : LinearMap.BilinForm ℝ L)
variable {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ L) (ε : ι → ℝ)
noncomputable def casimir : UniversalEnvelopingAlgebra ℝ L :=
  ∑ i, ε i • (UniversalEnvelopingAlgebra.ι ℝ (b i) * UniversalEnvelopingAlgebra.ι ℝ (b i))
variable {B b ε}
end Casimir
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
namespace IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {ι : Type*} [Fintype ι]
noncomputable def laplacian (b : Module.Basis ι ℝ h.lieSubalgebra) :
    Module.End ℂ (h.smoothFuns (F := F)) :=
  ∑ i, h.rightDerivEnd (h.ofLie (b i)) * h.rightDerivEnd (h.ofLie (b i))
end IsExpLieAlgebra
end GroundTheory.Automorphic


