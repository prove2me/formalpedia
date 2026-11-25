-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegenerateOnOrthCompl
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T10:18:23.107481+00:00
-- url     : https://prove2.me/theorems/cb559140-bc63-5a10-8162-0c72806d8683
-- title:
--   Nondegenerate On Orth Compl
-- statement:
--   Definitions and structural lemmas for Nondegenerate On Orth Compl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NondegenerateOnOrthCompl.lean

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_JordanExists
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsRepsOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCA_InL_smul

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
namespace Formalism.L2.SG.Pf.Cnt
open Formalism.HermitianLattices.Ext.L3
def GenusMassW : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    ∀ T₀ : Submodule (𝓞 K) V, IsLatIn (orthK h U) T₀ → Formalism.HermitianLatticesTheory.IsIntegralLat h T₀ →
    ∀ c : ℝ, MassConst K F (finrank K (orthK h U)) c →
      ∃ s : Finset (Submodule (𝓞 K) V),
        (∀ T ∈ s, IsLatIn (orthK h U) T ∧ SameGenusFix (F := F) h U T₀ T) ∧
        (∀ T, IsLatIn (orthK h U) T → SameGenusFix (F := F) h U T₀ T →
          ∃! T₁, T₁ ∈ s ∧ ∃ g ∈ isomFix h U, Formalism.HermitianLatticesTheory.gmap g T₁ = T) ∧
        (∀ T, IsLatIn (orthK h U) T → SameGenusFix (F := F) h U T₀ T → (stabFix h U T).Finite) ∧
        ((∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, discAut h (orthK h U) T₀ 𝔭.1 : ℕ) : ℝ) *
            ∑ T ∈ s, ((Nat.card (stabFix h U T) : ℕ) : ℝ)⁻¹ =
          c * nM F h (orthK h U) T₀ ^ finrank K (orthK h U) *
            ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, alphaStd K 𝔭.1 (finrank K (orthK h U)) /
              alphaStd K 𝔭.1 (finrank K (orthK h U) - cJ h (orthK h U) T₀ 𝔭.1)
end Formalism.L2.SG.Pf.Cnt
namespace Formalism.L2.SG.Pf.G9
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
scoped instance fixAct (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) :
    MulAction (isomFix h U) (Submodule (𝓞 K) V) where
  smul g Λ := Formalism.HermitianLatticesTheory.gmap g.1 Λ
  one_smul := autSub_gmap_one
  mul_smul a b Λ := autSub_gmap_mul a.1 b.1 Λ
def stabEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (Λ : Submodule (𝓞 K) V) :
    MulAction.stabilizer (isomFix h U) Λ ≃ stabFix h U Λ where
  toFun a := ⟨a.1.1, a.1.2, MulAction.mem_stabilizer_iff.mp a.2⟩
  invFun b := ⟨⟨b.1, b.2.1⟩, MulAction.mem_stabilizer_iff.mpr b.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
end Formalism.L2.SG.Pf.G9
namespace Formalism.L2.SG.Pf.Cnt
open Formalism.HermitianLattices.Ext.L3
open scoped Formalism.L2.SG.Pf.G9
end Formalism.L2.SG.Pf.Cnt


