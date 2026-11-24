-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenericFormsKer
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenericFormsKer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:40.352798+00:00
-- url     : https://prove2.me/theorems/cef5414f-ced7-4ba3-abad-eca9e8b4b17a
-- title:
--   Statements Generic Forms Ker
-- statement:
--   Definitions and structural lemmas for Statements Generic Forms Ker, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/StatementsGenericFormsKer.lean

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
open MvPolynomial
noncomputable section
def GenericFormsKer.Statement : Prop :=
  ∀ (F L : Type) [Field F] [Field L] [Algebra F L] (ι : Type) [Fintype ι] (e r : ℕ), r ≤ e →
    ∀ (u : Fin e × ι → L), AlgebraicIndependent F u →
    ∀ (b : Fin r → ι → F) (c : Fin r → L),
      (∀ i : Fin e, ∑ j, u (i, j) * ∑ m, c m * algebraMap F L (b m j) = 0) →
      ∀ j, ∑ m, c m * algebraMap F L (b m j) = 0
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights.Vertical


