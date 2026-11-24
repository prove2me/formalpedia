-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughTwoPointsTrdeg
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsThroughTwoPointsTrdeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:53.335205+00:00
-- url     : https://prove2.me/theorems/4135d7c5-0b81-441d-8531-abd4d6c1d411
-- title:
--   Statements Through Two Points Trdeg
-- statement:
--   Definitions and structural lemmas for Statements Through Two Points Trdeg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsThroughTwoPointsTrdeg.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
def ThroughTwoPointsTrdeg.Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] (n k : ℕ) [Algebra K Ω]
    [Algebra (MvPolynomial (Fin k × Fin n) K) Ω] [IsScalarTower K (MvPolynomial (Fin k × Fin n) K) Ω],
    Function.Injective (algebraMap (MvPolynomial (Fin k × Fin n) K) Ω) →
    ∀ x c : Fin n → K, ∑ j, c j * x j = 1 →
    ∀ (y : Fin n → Ω) (j : Fin n), y j ≠ 0 → (∀ t : Ω, y ≠ fun m => t * algebraMap K Ω (x m)) →
      (∀ i, ∑ m, algebraMap (MvPolynomial (Fin k × Fin n) K) Ω (genSubst x c (i, m)) * y m = 0) →
        (k : Cardinal) ≤ Algebra.trdeg K (Algebra.adjoin K (Set.range fun m => y m * (y j)⁻¹))
section Inhabitants
def pointOffFirstAxis : Fin 3 → FractionRing (MvPolynomial (Fin 1 × Fin 3) ℚ) :=
  fun m => algebraMap (MvPolynomial (Fin 1 × Fin 3) ℚ) _
    (![0, X (0, 2), -X (0, 1)] m)
end Inhabitants
end
end GroundTheory.Heights₂.Heights


