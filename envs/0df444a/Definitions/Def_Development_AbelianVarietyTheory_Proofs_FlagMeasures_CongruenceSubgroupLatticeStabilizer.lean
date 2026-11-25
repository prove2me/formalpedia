-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizer
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_CongruenceSubgroupLatticeStabilizer
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:14:55.655094+00:00
-- url     : https://prove2.me/theorems/86b5b3f5-391e-4cd1-b524-76cef8bb53dc
-- title:
--   Congruence Subgroup Lattice Stabilizer
-- statement:
--   Definitions and structural lemmas for Congruence Subgroup Lattice Stabilizer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CongruenceSubgroupLatticeStabilizer.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsPowSmulMem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.HL.CongFin
section Abstract
variable {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] {O : Subring E}
theorem mem_stab_iff (Λ : Submodule O V) (g : V ≃ₗ[E] V) :
    g ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ ↔ ∀ v, g v ∈ Λ ↔ v ∈ Λ := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h v
    constructor
    · intro hv
      rw [← h, Submodule.mem_smul_pointwise_iff_exists] at hv
      obtain ⟨w, hw, hwv⟩ := hv
      have : w = v := g.injective hwv
      exact this ▸ hw
    · intro hv
      rw [← h, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨v, hv, rfl⟩
  · intro h
    ext v
    rw [Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (h w).2 hw
    · intro hv
      refine ⟨g.symm v, (h _).1 (by simpa using hv), ?_⟩
      exact g.apply_symm_apply v
def congSub (Λ : Submodule O V) (c : E) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | g ∈ MulAction.stabilizer (V ≃ₗ[E] V) Λ ∧ ∀ v ∈ Λ, ∃ w ∈ Λ, g v - v = c • w}
  one_mem' := ⟨one_mem _, fun v _ => ⟨0, Λ.zero_mem, by simp⟩⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun v hv => ?_⟩
    obtain ⟨w, hw, h⟩ := hb' v hv
    obtain ⟨w', hw', h'⟩ := ha' (b v) (((mem_stab_iff Λ b).1 hb v).2 hv)
    refine ⟨w' + w, Λ.add_mem hw' hw, ?_⟩
    rw [smul_add, ← h, ← h']
    simp
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun v hv => ?_⟩
    obtain ⟨w, hw, h⟩ := ha' (a⁻¹ v) (((mem_stab_iff Λ _).1 (inv_mem ha) v).2 hv)
    refine ⟨-w, Λ.neg_mem hw, ?_⟩
    have : a (a⁻¹ v) = v := a.apply_symm_apply v
    rw [smul_neg, ← h, this, neg_sub]
end Abstract
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
end GlobalTheory.HL.CongFin


