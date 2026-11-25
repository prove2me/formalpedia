-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IncOInjective
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IncOInjective
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T10:39:45.782001+00:00
-- url     : https://prove2.me/theorems/e0f336a0-a8b6-540d-898c-cbe4f5772962
-- title:
--   Inc OInjective
-- statement:
--   Definitions and structural lemmas for Inc OInjective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/IncOInjective.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsomFixOfExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LocFMapSubtype
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GmapEqSelfOfFix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InvMemLocROfUnimod
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
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
open NumberField Module
noncomputable section
namespace Formalism.L2.SG.Pf.G8
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt
section Transport
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
def resF (h : V →ₗ⋆[K] V →ₗ[K] K) (W : Submodule K V) : W →ₗ⋆[K] W →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => h x y)
    (fun x x' y => by simp) (fun c x y => by simp) (fun x y y' => by simp) (fun c x y => by simp)
abbrev incO (W : Submodule K V) : W →ₗ[𝓞 K] V := W.subtype.restrictScalars (𝓞 K)
abbrev latW (W : Submodule K V) (T : Submodule (𝓞 K) V) : Submodule (𝓞 K) W := T.comap (incO W)
end Transport
end Formalism.L2.SG.Pf.G8


