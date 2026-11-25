-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsMemSupport
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsMemSupport
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:33:02.098956+00:00
-- url     : https://prove2.me/theorems/91bb490a-4933-42f3-86ed-7b37ff9d51a0
-- title:
--   Exists Mem Support
-- statement:
--   Definitions and structural lemmas for Exists Mem Support, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsMemSupport.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_CechH0SectionsHypothesesLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
noncomputable section
universe u v w
namespace CechZerothCohomologySections
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
def pt {i : Fin (N + 1)} (hi : i ∈ support x) : Cech.Idx (support x) 0 :=
  ⟨⟨{i}, Finset.singleton_nonempty i, Finset.singleton_subset_iff.mpr hi⟩, Finset.card_singleton i⟩
theorem mem_sub_of_mem_secs (F : SubSystem S x E) {z : E} (hz : z ∈ F.secs) (I : Chart x) :
    z ∈ F.sub I :=
  (Submodule.mem_iInf _).mp hz I
def constC (F : SubSystem S x E) : F.secs →ₗ[S] Cech.Cochain (fun I => F.sub I) 0 where
  toFun z K := ⟨z, mem_sub_of_mem_secs F z.2 K.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem constC_cocycle (F : SubSystem S x E) (z : F.secs) :
    Cech.d (fun I => F.sub I) F.res 0 (constC F z) = 0 :=
  Cech.d_zero_of_compat (v := fun I => (⟨z, mem_sub_of_mem_secs F z.2 I⟩ : F.sub I))
    (fun _ _ _ => rfl)
def toKer (F : SubSystem S x E) :
    F.secs →ₗ[S] LinearMap.ker (Cech.d (fun I => F.sub I) F.res 0) :=
  (constC F).codRestrict _ fun z => LinearMap.mem_ker.mpr (constC_cocycle F z)
end CechZerothCohomologySections
end
end GroundTheory.Heights₂.Heights.Kleiman


