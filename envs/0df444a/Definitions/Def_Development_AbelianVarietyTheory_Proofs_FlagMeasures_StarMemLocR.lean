-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_StarMemLocR
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_StarMemLocR
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T04:33:54.474841+00:00
-- url     : https://prove2.me/theorems/b92fa7ce-09a3-5dc4-aa3a-166fafbe18fa
-- title:
--   Star Mem Loc R
-- statement:
--   Definitions and structural lemmas for Star Mem Loc R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/StarMemLocR.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
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
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
namespace GlobalTheory.Mass.Hyperplane
section Refl
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
end Refl
section Local
variable {K : Type} [Field K] [StarRing K]
noncomputable def cj (K : Type) [Field K] [StarRing K] : 𝓞 K →+* 𝓞 K := RingOfIntegers.mapRingHom (starRingEnd K)
theorem mem_locR {P : Ideal (𝓞 K)} {x : K} :
    x ∈ locR (K := K) P ↔ ∃ s ∈ hcompl (K := K) P, ∃ r : 𝓞 K, algebraMap _ K r = algebraMap _ K s * x := by
  change (∃ s ∈ hcompl (K := K) P, s • x ∈ (1 : Submodule (𝓞 K) K)) ↔ _
  simp only [Submodule.mem_one, Algebra.smul_def]
def locRing (P : Ideal (𝓞 K)) : Subring K where
  carrier := locR (K := K) P
  zero_mem' := Submodule.zero_mem _
  add_mem' := Submodule.add_mem _
  neg_mem' := Submodule.neg_mem _
  one_mem' := mem_locR.2 ⟨1, Submonoid.one_mem _, 1, by simp⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨s, hs, r, hr⟩ := mem_locR.1 ha
    obtain ⟨t, ht, q, hq⟩ := mem_locR.1 hb
    refine mem_locR.2 ⟨s * t, Submonoid.mul_mem _ hs ht, r * q, ?_⟩
    rw [map_mul, map_mul, hr, hq]
    ring
def locId (P : Ideal (𝓞 K)) : Submodule (𝓞 K) K := loc (K := K) P (Submodule.map (Algebra.linearMap (𝓞 K) K) P)
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable [NumberField K]
end Local
end GlobalTheory.Mass.Hyperplane


