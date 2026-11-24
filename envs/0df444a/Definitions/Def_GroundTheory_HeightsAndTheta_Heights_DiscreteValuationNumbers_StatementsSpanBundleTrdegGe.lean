-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSpanBundleTrdegGe
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSpanBundleTrdegGe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:38.219827+00:00
-- url     : https://prove2.me/theorems/1fc5fac6-ba7c-4867-99fc-a0d3c3a1f251
-- title:
--   Statements Span Bundle Trdeg Ge
-- statement:
--   Definitions and structural lemmas for Statements Span Bundle Trdeg Ge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsSpanBundleTrdegGe.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSpanBundleDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
def SpanBundleTrdegGe.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) (ι : K → Type) (y : (Σ k, ι k) → Ω) (M i : ℕ) (G : Fin M → Fin i → Ω),
    LinearIndependent Ω (fun j l => G l j) →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (s : Fin i → Φ), AlgebraicIndependent Ω s →
      Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) + i ≤
        Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s)
end
end GroundTheory.Heights₂.Heights.NumbersDVR


