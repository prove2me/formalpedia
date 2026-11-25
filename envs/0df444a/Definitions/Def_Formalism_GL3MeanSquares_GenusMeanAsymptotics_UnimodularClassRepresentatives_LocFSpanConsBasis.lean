-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocFSpanConsBasis
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocFSpanConsBasis
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T07:58:16.137296+00:00
-- url     : https://prove2.me/theorems/5915e030-3b79-5f84-b6a8-5b186752523e
-- title:
--   Loc FSpan Cons Basis
-- statement:
--   Definitions and structural lemmas for Loc FSpan Cons Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocFSpanConsBasis.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocFEqLocFAdjoinCut
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EqBlockOfFix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsExactLift
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RedEqOfSubMem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_VecSplit_comb_eq_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_succ_zero
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_succ
attribute [local simp] Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.emb_zero_zero


set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.PinB
open idealPowerSpanBounds integralBasisSpans
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
omit [NumberField K] [FiniteDimensional K V] [FiniteDimensional K V'] in

def prodEquiv (S : VecSplit h h') : (K × V') ≃ₗ[K] V :=
  LinearEquiv.ofBijective ((LinearMap.toSpanSingleton K V S.x₀).coprod S.ι) (by
    constructor
    · rintro ⟨c, a⟩ ⟨c', a'⟩ e
      simp only [LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply] at e
      obtain ⟨rfl, rfl⟩ := S.comb_eq_iff.1 e
      rfl
    · intro v
      obtain ⟨c, a, rfl⟩ := S.cover v
      exact ⟨(c, a), by simp only [LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply]⟩)
def consBasis (S : VecSplit h h') {κ : Type} (b' : Basis κ K V') : Basis (Unit ⊕ κ) K V :=
  ((Basis.singleton Unit K).prod b').map (prodEquiv S)
end Formalism.HermitianLattices.Ext.L3.PinB


