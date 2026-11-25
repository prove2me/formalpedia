-- Prove2me | Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
-- name    : GroundTheory_LocalFields_AbstractLocalReciprocity_KeyLemma
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:35:03.284965+00:00
-- url     : https://prove2.me/theorems/37fe535f-06bb-4502-9860-dfb0b8aa11a9
-- title:
--   Key Lemma
-- statement:
--   Definitions and structural lemmas for Key Lemma, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/KeyLemma.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Theorems.Thm_GroundTheory_LocalField_Abstract_smul_mem_fixedModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.LocalField.Abstract
open ProfiniteInteger
namespace ClassFieldData
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}
section SlopeTestRemainingChoices
omit [TotallyDisconnectedSpace G] in

def powLift {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂)) (m : ℕ) (hm : 0 < m) :
    D.FrobeniusLift K where
  elt := φ ^ m
  mem := K.pow_mem hφK m
  deg := m
  deg_pos := hm
  deg_eq := by
    rw [map_pow, hdφ, ← ofAdd_nsmul]
    congr 1
    push_cast
    rw [nsmul_eq_mul]
omit [TotallyDisconnectedSpace G] in

theorem map_conj_inf_ker (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] {g : G}
    (hg : g ∈ (K : Subgroup G)) :
    ((L : Subgroup G) ⊓ D.deg.ker).map (MulAut.conj g).toMonoidHom = (L : Subgroup G) ⊓ D.deg.ker :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 (FrobeniusLift.mem_normalizer hLK hg)
omit [TotallyDisconnectedSpace G] in

theorem smul_mem_fixedModule_inf_ker (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] {g : G}
    (hg : g ∈ (K : Subgroup G)) {y : A} (hy : y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    g • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) := by
  have := smul_mem_fixedModule hy g
  rwa [map_conj_inf_ker hLK hg] at this
end SlopeTestRemainingChoices
section Helpers
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
end Helpers
section Key
variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
end Key
end ClassFieldData
end GroundTheory.LocalField.Abstract


