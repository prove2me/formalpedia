-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsomFixOfExp
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsomFixOfExp
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:25:48.549616+00:00
-- url     : https://prove2.me/theorems/8ce16764-784f-58ab-bab2-992344d62c45
-- title:
--   Isom Fix Of Exp
-- statement:
--   Definitions and structural lemmas for Isom Fix Of Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/IsomFixOfExp.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
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
namespace Formalism.L2.SG.Pf.G8
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
def IsomFixOfExp : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    ∀ T T' : Submodule (𝓞 K) V, IsLatIn (orthK h U) T → IsLatIn (orthK h U) T' →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a b' a',
      IsJordanIn h (orthK h U) T 𝔭 b a → IsJordanIn h (orthK h U) T' 𝔭 b' a' →
      (∀ i, vF 𝔭 (a i) = vF 𝔭 (a' i)) →
      ∃ g ∈ isomFix h U, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 T) = locF 𝔭 T'
end Formalism.L2.SG.Pf.G8


