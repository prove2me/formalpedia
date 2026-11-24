-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZPlane
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZPlane
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:25:40.907584+00:00
-- url     : https://prove2.me/theorems/fb731a91-e54e-4750-b419-8e8c950908c4
-- title:
--   Lat Dict ZPlane
-- statement:
--   Definitions and structural lemmas for Lat Dict ZPlane, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZPlane.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
noncomputable section
open NumberField
namespace Formalism.L2.SG.Pf.LatDictZ.Z2
open ReciprocityTheory.ChartRestriction.L3.WA
section Generic
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
def IdealLike (S : Subring K) (P : K → Prop) : Prop :=
  (∀ a b, P a → P b → P (a - b)) ∧ (∀ x ∈ S, ∀ a, P a → P (x * a)) ∧ ¬ P 1
def planeForm (h : V →ₗ⋆[K] V →ₗ[K] K) (z : V) (b : K) : V →ₗ⋆[K] V →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => h x y - b * h x z * h z y)
    (by intros; simp only [map_add, LinearMap.add_apply]; ring)
    (by intros; simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [map_add]; ring)
    (by intros; simp only [map_smul, smul_eq_mul, RingHom.id_apply]; ring)
end Generic
section Ring
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def InI (p I : Ideal (𝓞 K)) (a : K) : Prop :=
  ∃ r s : 𝓞 K, s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p ∧ r ∈ I ∧
    a = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s
end Ring
end Formalism.L2.SG.Pf.LatDictZ.Z2


