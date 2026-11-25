-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapesTer
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscriminantNormShapesTer
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T12:05:21.403941+00:00
-- url     : https://prove2.me/theorems/0c45a310-01ca-51c3-985f-e04b788e3cce
-- title:
--   Discriminant Norm Shapes Ter
-- statement:
--   Definitions and structural lemmas for Discriminant Norm Shapes Ter, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/DiscriminantNormShapesTer.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiscOntoOfShape
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_exists_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
open scoped Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
noncomputable section
namespace Formalism.L2.SG.Pf.discriminantNormShapes
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds Formalism.HermitianLattices.Ext.L3.traceDeterminantCongruences Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
  Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G5
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
  [Fact (IsFixF K F)] {m : ℕ}
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
theorem exists_inv_unit {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {b : 𝓞 F} (hb : b ∉ 𝔭) (k : ℕ) :
    ∃ g : 𝓞 K ⧸ extP K 𝔭 ^ k, g * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι b) = 1 := by
  obtain ⟨y, i, hi, hyi⟩ := h𝔭.exists_inv hb

  have hnil : IsNilpotent (Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι i)) := by
    refine ⟨k, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hi) k
  obtain ⟨u, hu⟩ := hnil.isUnit_one_sub
  refine ⟨↑u⁻¹ * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι y), ?_⟩
  have h : Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι y) * Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι b) = 1 - Ideal.Quotient.mk (extP K 𝔭 ^ k) (ι i) := by
    rw [← map_mul, ← map_mul, eq_sub_iff_add_eq, ← map_add, ← map_add, hyi, map_one, map_one]
  rw [mul_assoc, h, ← hu, Units.inv_mul]
open Classical in

def gQ (K : Type) {F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] [Fact (IsFixF K F)] {m : ℕ} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (a : Fin m → 𝓞 F) : Matrix (Fin m) (Fin m) (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Matrix.diagonal fun j => if h : a j ∈ 𝔭 then 0 else (exists_inv_unit (K := K) h𝔭 h k).choose
end Formalism.L2.SG.Pf.discriminantNormShapes


