-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_FibreCountingDataBis
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_FibreCountingDataBis
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T12:19:28.544639+00:00
-- url     : https://prove2.me/theorems/ae59fec6-e48f-51ba-a7d8-c61b90bdcfae
-- title:
--   Fibre Counting Data Bis
-- statement:
--   Definitions and structural lemmas for Fibre Counting Data Bis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/FibreCountingDataBis.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CondZIff
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_succ_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_succ
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_emb_zero_zero
import Theorems.Thm_Formalism_L2_SG_Pf_G2_smul_eq_jK
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
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
namespace Formalism.L2.SG.Pf.fibreCountingData
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G2 Formalism.L2.SG.Pf.G5
variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
def crd (h : V →ₗ⋆[K] V →ₗ[K] K) {m : ℕ} (b : Fin m → V) (a : Fin m → 𝓞 F) (x : V) (j : Fin m) : K :=
  h (b j) x / jK (ι (a j))
def gmap (h : V →ₗ⋆[K] V →ₗ[K] K) {m : ℕ} (b : Fin m → V) (a : Fin m → 𝓞 F)
    (Y : Matrix (Fin m) (Fin m) (𝓞 K)) : V →ₗ[𝓞 K] V where
  toFun x := ∑ i, (∑ j, jK (Y i j) * crd h b a x j) • b i
  map_add' x y := by
    simp only [crd, map_add, add_div, mul_add, Finset.sum_add_distrib, add_smul]
  map_smul' c x := by
    simp only [crd, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_jK c x, smul_eq_jK c, smul_smul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smul, smul_eq_mul]; ring
section
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {m : ℕ}
  {b : Fin m → V} {a : Fin m → 𝓞 F}
variable (horth : ∀ i j, i ≠ j → h (b i) (b j) = 0)
  (hdiag : ∀ i, h (b i) (b i) = algebraMap F K ((a i : 𝓞 F) : F)) (ha : ∀ i, a i ≠ 0)
include horth hdiag ha
variable (hbX : ∀ i, b i ∈ (⊤ : Submodule K V))
  (hloc : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L)
include hbX hloc
end
end Formalism.L2.SG.Pf.fibreCountingData


