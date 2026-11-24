-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOneInduction
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T21:43:11.746328+00:00
-- url     : https://prove2.me/theorems/ec7c8e62-2a26-40d4-a402-02fa3f3cf31d
-- title:
--   Lattice From Norm One Induction
-- statement:
--   Definitions and structural lemmas for Lattice From Norm One Induction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/LatticeFromNormOneInduction.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_IndBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
namespace PI.KLW.Ind
open PI.KLW
def extL {K : Type} [Field K] {ι : Type} [DecidableEq ι] (i0 : ι) :
    ({i // i ≠ i0} → K) →ₗ[K] (ι → K) where
  toFun w i := if h : i = i0 then 0 else w ⟨i, h⟩
  map_add' a b := by
    funext i
    by_cases h : i = i0 <;> simp [h]
  map_smul' k a := by
    funext i
    by_cases h : i = i0 <;> simp [h]
def resL {K : Type} [Field K] {ι : Type} (i0 : ι) : (ι → K) →ₗ[K] ({i // i ≠ i0} → K) :=
  LinearMap.funLeft K K Subtype.val
end PI.KLW.Ind
namespace PI.KLW
end PI.KLW


