-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsDerivSpanTrdeg
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsDerivSpanTrdeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:44:42.188562+00:00
-- url     : https://prove2.me/theorems/eecdda6c-2fa9-41f7-895f-e2e1e039b699
-- title:
--   Statements Deriv Span Trdeg
-- statement:
--   Definitions and structural lemmas for Statements Deriv Span Trdeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/StatementsDerivSpanTrdeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
noncomputable section
def DerivSpanTrdeg.Statement : Prop :=
  ∀ (k L : Type) [Field k] [PerfectField k] [Field L] [Algebra k L] (ι : Type) [Fintype ι]
    (z : ι → L) (e : ℕ),
    Algebra.trdeg k (Algebra.adjoin k (Set.range z)) ≤ (e : Cardinal) →
    ∃ r ≤ e, ∃ b : Fin r → ι → IntermediateField.adjoin k (Set.range z),
      ∀ D : Derivation k L L, ∃ c : Fin r → L, ∀ j, D (z j) = ∑ m, c m * (b m j : L)
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights.Vertical


