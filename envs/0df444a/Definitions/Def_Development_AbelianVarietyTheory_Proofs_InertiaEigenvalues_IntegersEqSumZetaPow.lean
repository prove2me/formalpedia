-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPow
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:38.387803+00:00
-- url     : https://prove2.me/theorems/f09554fc-87d0-4d86-aba5-29d30fe54f85
-- title:
--   Integers Eq Sum Zeta Pow
-- statement:
--   Definitions and structural lemmas for Integers Eq Sum Zeta Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IntegersEqSumZetaPow.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMemCyclotomicLayerPrimeRpowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
namespace GlobalTheory.Cyc.IntBasis
variable {l : ℕ} [Fact l.Prime]
def intRing (F : IntermediateField ℚ_[l] (Om l)) : Subring (Om l) where
  carrier := {y | y ∈ F ∧ ‖y‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => ⟨mul_mem ha.1 hb.1, by
    rw [norm_mul]; exact mul_le_one₀ ha.2 (norm_nonneg _) hb.2⟩
  one_mem' := ⟨one_mem _, by simp⟩
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1,
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha.2 hb.2)⟩
  zero_mem' := ⟨zero_mem _, by simp⟩
  neg_mem' := fun {a} ha => ⟨neg_mem ha.1, by simpa using ha.2⟩
end GlobalTheory.Cyc.IntBasis


