-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolyLine
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolyLine
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:01.403948+00:00
-- url     : https://prove2.me/theorems/ae77b85a-3ce8-46ec-897f-1e244a12f3a6
-- title:
--   Statements Eventual Poly Line
-- statement:
--   Definitions and structural lemmas for Statements Eventual Poly Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsEventualPolyLine.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
def EventualPolyLine.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (D : ℕ) (f : (K → ℤ) → ℤ) (p : MvPolynomial K ℚ) (a₀ : ℕ)
    (a m : K → ℤ),
    p.totalDegree ≤ D →
    (∀ b : K → ℕ, (∀ k, a₀ ≤ b k) →
      (f (fun k => (b k : ℤ)) : ℚ) = MvPolynomial.eval (fun k => (b k : ℚ)) p) →
    ∃ r : Polynomial ℝ, r.natDegree ≤ D ∧
      r.coeff D = (eventualValue (mixedDiff (fun _ : Fin D => a) f) : ℝ) / (D.factorial : ℝ) ∧
      ∀ n : ℕ, ((MvPolynomial.eval (fun k => ((((n : ℤ) • a + m) k : ℤ) : ℚ)) p : ℚ) : ℝ) = r.eval (n : ℝ)
end
end GroundTheory.Heights₂.Heights.HilbertSamuel


