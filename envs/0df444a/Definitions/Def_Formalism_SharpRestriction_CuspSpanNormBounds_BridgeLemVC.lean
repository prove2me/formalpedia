-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVC
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVC
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T09:26:42.651696+00:00
-- url     : https://prove2.me/theorems/0ff491d8-1d24-48f2-8ac2-fc6637a82e76
-- title:
--   Bridge Lem VC
-- statement:
--   Definitions and structural lemmas for Bridge Lem VC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVC.lean

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVR
import Definitions.Def_Formalism_FlagUnipotentLattices_ArithmeticIdentityEntries
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_exists_ne_zero_of_isLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.BridgeLemVC
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]
theorem isFrac {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) : IsFractional (𝓞 K)⁰ M :=
  FractionalIdeal.isFractional_of_fg hM.fg
def fracI {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) : FractionalIdeal (𝓞 K)⁰ K :=
  ⟨M, isFrac hM⟩
theorem coe_fracI {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) :
    ((fracI hM : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) = M := FractionalIdeal.coe_mk _ _
theorem frac_ne_zero {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) : fracI hM ≠ 0 := by
  obtain ⟨a, ha, h0⟩ := exists_ne_zero_of_isLattice hM
  intro e
  have h1 : a ∈ fracI hM := by rw [← FractionalIdeal.mem_coe, coe_fracI]; exact ha
  rw [e] at h1
  exact h0 ((FractionalIdeal.mem_zero_iff _).1 h1)
def fracU {M : Submodule (𝓞 K) K} (hM : Submodule.IsLattice K M) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 _ (frac_ne_zero hM)
def iota (K : Type) [Field K] [NumberField K] [StarRing K] : (𝓞 (cmF K))ˣ →* K :=
  ((cmF K).val.toRingHom.comp (algebraMap (𝓞 (cmF K)) (cmF K))).toMonoidHom.comp (Units.coeHom _)
end Formalism.MainNotions.BridgeLemVC
end


