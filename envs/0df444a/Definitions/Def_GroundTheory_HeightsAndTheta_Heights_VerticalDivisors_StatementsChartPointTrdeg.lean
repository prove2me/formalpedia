-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChartPointTrdeg
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChartPointTrdeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:43:54.172317+00:00
-- url     : https://prove2.me/theorems/a47ced2b-1289-49fe-8ae8-96ecb04ba854
-- title:
--   Statements Chart Point Trdeg
-- statement:
--   Definitions and structural lemmas for Statements Chart Point Trdeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/StatementsChartPointTrdeg.lean

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
def ChartPointTrdeg.Statement : Prop :=
  ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (n e : ℕ) (Q : Ideal (MvPolynomial (Fin n) k))
    (g : MvPolynomial (Fin (e + 1) × Fin n) k), IsProjPrime Q → IsChowForm Q (e + 1) g →
      ∀ (x : Fin n → L) (j₀ : Fin n), (∀ f ∈ Q, aeval x f = 0) → x j₀ ≠ 0 →
        Algebra.trdeg k (Algebra.adjoin k (Set.range fun m => x m * (x j₀)⁻¹)) ≤ (e : Cardinal)
end
end GroundTheory.Heights₂.Heights.Vertical


