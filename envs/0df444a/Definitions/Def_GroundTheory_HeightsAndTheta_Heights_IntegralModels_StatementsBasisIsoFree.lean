-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsBasisIsoFree
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsBasisIsoFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:22.403807+00:00
-- url     : https://prove2.me/theorems/ae196b80-8fa0-4057-ab46-0bb7adc62e9a
-- title:
--   Statements Basis Iso Free
-- statement:
--   Definitions and structural lemmas for Statements Basis Iso Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsBasisIsoFree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsFreeSheafBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
def BasisIsoFree.Statement : Prop :=
  ∀ (Y : Scheme.{u}) (M : Y.Modules) (n : ℕ) (s : Fin n → Γ(M, ⊤)), IsBasisOn M ⊤ s →
    Nonempty (M ≅ freeModule Y n)
end
end GroundTheory.Heights₂.Heights.Model


