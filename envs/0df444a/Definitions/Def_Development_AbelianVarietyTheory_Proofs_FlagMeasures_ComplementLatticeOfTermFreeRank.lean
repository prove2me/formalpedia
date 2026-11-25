-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ComplementLatticeOfTermFreeRank
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_ComplementLatticeOfTermFreeRank
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T05:54:34.307144+00:00
-- url     : https://prove2.me/theorems/67faaccc-250c-50ac-9a10-ebae2e0c2a3b
-- title:
--   Complement Lattice Of Term Free Rank
-- statement:
--   Definitions and structural lemmas for Complement Lattice Of Term Free Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ComplementLatticeOfTermFreeRank.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianDoubleCosetTermBasicFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsBasisFgMaximalOrderSpanningFree
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
namespace GlobalTheory.HL.CompLat
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)
def diagGraph (Λ : Submodule L.O S.V) : Submodule L.O S.V where
  carrier := {w | (w, w) ∈ S.graphOf Λ}
  zero_mem' := ⟨0, Λ.zero_mem, 0, Λ.zero_mem, Submodule.zero_mem _, Submodule.zero_mem _,
    by simp, by simp, 0, Λ.zero_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨y', hy', y, hy, p', p, x', x, t, ht, e⟩ ⟨z', hz', z, hz, q', q, u', u, s, hs, e'⟩
    refine ⟨y' + z', Λ.add_mem hy' hz', y + z, Λ.add_mem hy hz, Submodule.add_mem _ p' q',
      Submodule.add_mem _ p q, ?_, ?_, t + s, Λ.add_mem ht hs, ?_⟩
    · have := S.X'.add_mem x' u'
      rwa [sub_add_sub_comm] at this
    · have := S.X.add_mem x u
      rwa [sub_add_sub_comm] at this
    · rw [smul_add, ← e, ← e', sub_add_sub_comm]
  smul_mem' := by
    rintro c a ⟨y', hy', y, hy, p', p, x', x, t, ht, e⟩
    refine ⟨c • y', Λ.smul_mem c hy', c • y, Λ.smul_mem c hy, Submodule.smul_mem _ (c : E) p',
      Submodule.smul_mem _ (c : E) p, ?_, ?_, c • t, Λ.smul_mem c ht, ?_⟩
    · have := S.X'.smul_mem (c : E) x'
      rwa [smul_sub] at this
    · have := S.X.smul_mem (c : E) x
      rwa [smul_sub] at this
    · rw [← smul_sub, e]
      exact smul_comm (c : E) _ t
end GlobalTheory.HL.CompLat


