-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairOfEps
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairOfEps
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:44:04.76083+00:00
-- url     : https://prove2.me/theorems/b9a494f6-6d46-4bae-9392-9baac6761f9a
-- title:
--   Pair Of Eps
-- statement:
--   Definitions and structural lemmas for Pair Of Eps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/PairOfEps.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneA
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
namespace PI.KLW.Pair
open PI.KLW
def EpsSplit : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ),
    Module.finrank ℚ K = 2 → (∀ x, c (c x) = x) → p.Prime → SplitK c p →
      ∀ k : ℕ, ∃ ε : K, Rp K p ε ∧ ε + c ε = 1 ∧ Rp K p (ε * c ε / (p : K) ^ k)
end PI.KLW.Pair
namespace PI.KLW
end PI.KLW


