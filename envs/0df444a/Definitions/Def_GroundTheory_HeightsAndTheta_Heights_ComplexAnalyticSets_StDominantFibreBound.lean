-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDominantFibreBound
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDominantFibreBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:33:40.141802+00:00
-- url     : https://prove2.me/theorems/6405f6e1-13d3-4a78-b741-d07fb1e94e46
-- title:
--   St Dominant Fibre Bound
-- statement:
--   Definitions and structural lemmas for St Dominant Fibre Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StDominantFibreBound.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
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
open MvPolynomial ComplexSets
noncomputable section
def DominantFibreBound.Statement : Prop :=
  ∀ (n d : ℕ) (P : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ),
    P.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) = (d : ℕ) →
    Function.Injective ((Ideal.Quotient.mkₐ ℂ P).comp (aeval p)) →
    ∃ (e : ℕ) (Δ : MvPolynomial (Fin d) ℂ), Δ ≠ 0 ∧ ∀ w : Fin d → ℂ, eval w Δ ≠ 0 →
      {x | x ∈ zeroSet P ∧ ∀ i, eval x (p i) = w i}.encard ≤ e
end
end GroundTheory.Heights₂.Heights


