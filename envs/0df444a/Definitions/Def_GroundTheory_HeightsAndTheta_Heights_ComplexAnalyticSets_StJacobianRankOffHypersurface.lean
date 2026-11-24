-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StJacobianRankOffHypersurface
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StJacobianRankOffHypersurface
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:46.624772+00:00
-- url     : https://prove2.me/theorems/a8a46c15-b9aa-4226-96cf-afd52aa9d382
-- title:
--   St Jacobian Rank Off Hypersurface
-- statement:
--   Definitions and structural lemmas for St Jacobian Rank Off Hypersurface, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StJacobianRankOffHypersurface.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalCodimOneCompleteIntersection
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
def JacobianRankOffHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Q : Ideal (MvPolynomial σ ℂ)) (d r : ℕ) (q : Fin r → MvPolynomial σ ℂ)
    (t : MvPolynomial σ ℂ), Q.IsPrime → ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = (d : ℕ) →
    (∀ j, q j ∈ Q) → t ∉ Q → (∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ Ideal.span (Set.range q)) →
      ∃ μ : MvPolynomial σ ℂ, μ ∉ Q ∧ ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn Q, eval w μ ≠ 0 →
        Module.finrank ℂ (Submodule.span ℂ (Set.range fun j s ↦ eval w (pderiv s (q j)))) + d =
          Fintype.card σ
end
end GroundTheory.Heights₂.Heights


