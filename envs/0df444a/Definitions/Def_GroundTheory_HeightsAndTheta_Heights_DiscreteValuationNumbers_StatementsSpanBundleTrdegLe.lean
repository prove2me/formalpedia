-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSpanBundleTrdegLe
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSpanBundleTrdegLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:18.759805+00:00
-- url     : https://prove2.me/theorems/dbf5152b-e260-4e37-af06-b2429ce07aa6
-- title:
--   Statements Span Bundle Trdeg Le
-- statement:
--   Definitions and structural lemmas for Statements Span Bundle Trdeg Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsSpanBundleTrdegLe.lean

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def SpanBundleTrdegLe.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] (ι : K → Type) (y : (Σ k, ι k) → Ω) (M i : ℕ) (G : Fin M → Fin i → Ω)
    (c : ∀ k, ι k) (a : K → ℤ) (H : Matrix (Fin i) (Fin i) Ω), segreVec y c ≠ 0 → IsUnit H.det →
      (∀ l m, (Matrix.of G * H) l m ∈ degLat F y a c) →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (s : Fin i → Φ),
      Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) ≤
        Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) + i
end
end GroundTheory.Heights₂.Heights.NumbersDVR


