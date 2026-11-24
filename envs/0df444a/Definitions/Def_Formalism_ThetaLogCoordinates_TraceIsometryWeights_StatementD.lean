-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:59.085797+00:00
-- url     : https://prove2.me/theorems/2ad23216-046a-4047-9f93-4e8ccb61b010
-- title:
--   Statement D
-- statement:
--   Definitions and structural lemmas for Statement D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/StatementD.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_HasLatBasis
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.PW
open MvPolynomial Finset Formalism.GM.M
def DivInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (j : ℕ) (c d : Fin r), c ≠ d → ∀ (k : ℕ),
    ∀ x ∈ IntPol p (Fin N × Fin r), ((k.factorial : ℚ_[p]))⁻¹ • ((glAct p LL j c d) ^ k) x ∈ IntPol p (Fin N × Fin r)
def LatBasisPol : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (U : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])), FiniteDimensional ℚ_[p] U →
    HasLatBasis p (IntPol p σ).toAddSubgroup U
end Formalism.InvariantFactorPaths.PW


