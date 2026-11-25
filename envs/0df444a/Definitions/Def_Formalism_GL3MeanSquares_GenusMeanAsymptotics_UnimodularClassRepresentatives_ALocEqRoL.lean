-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ALocEqRoL
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ALocEqRoL
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T06:19:58.589088+00:00
-- url     : https://prove2.me/theorems/8c0786ab-1d62-5062-9885-8812c2d08c5d
-- title:
--   ALoc Eq Ro L
-- statement:
--   Definitions and structural lemmas for ALoc Eq Ro L, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ALocEqRoL.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormLeOfMemBoxSet
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_A5_exists_vF_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.A5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
def aLoc (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (n : 𝓞 F) : ℝ :=
  alphaN h L 𝔭.1 n / eFac K (finrank K V) 𝔭.1
open scoped Classical in

def roL (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (j : ℕ) : ℝ :=
  if 𝔭 ∈ S then 1 else aLoc h L 𝔭 (exists_vF_eq 𝔭.2 j).choose
variable (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
  {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
  (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
  {S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}}
  (hS : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, vd h L 𝔭.1 ≠ 0 → 𝔭 ∈ S)
include hK hF hs hd hL hLi hS
include hm
end Formalism.HermitianLattices.Ext.L3.A5


