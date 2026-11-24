-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneP
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T21:32:33.495817+00:00
-- url     : https://prove2.me/theorems/791ed8ba-b879-48a6-8504-e9e3654ff5c6
-- title:
--   Norm One P
-- statement:
--   Definitions and structural lemmas for Norm One P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeIsomorphism/NormOneP.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
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
namespace PI.KLW
def PairOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) (ι : Type) [Fintype ι] [Nonempty ι]
    (L : Set (ι → K)),
    Module.finrank ℚ K = 2 → (∀ x, c (c x) = x) → p.Prime → SplitK c p →
      Unimod K c p L → Spans K L → ∃ x ∈ L, ∃ y ∈ L, hf c x y = 1
end PI.KLW


