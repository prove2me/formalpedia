-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSpanBundleDim
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSpanBundleDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:24.892289+00:00
-- url     : https://prove2.me/theorems/3f2defff-f83a-4743-96e8-f2fd836129be
-- title:
--   Statements Span Bundle Dim
-- statement:
--   Definitions and structural lemmas for Statements Span Bundle Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/StatementsSpanBundleDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
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
def SpanBundleDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (M i : ℕ) (G : Fin M → Fin i → Ω), 0 < i → LinearIndependent Ω (fun j l => G l j) →
    ∀ (c : ∀ k, ι k) (a : K → ℤ) (H : Matrix (Fin i) (Fin i) Ω), segreVec y c ≠ 0 → IsUnit H.det →
      (∀ l m, (Matrix.of G * H) l m ∈ degLat F y a c) →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (s : Fin i → Φ), AlgebraicIndependent Ω s →
      IsMultiProjPrime (projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) ∧
        FieldNumbers.relDim (projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) =
          ((e + i - 1 : ℕ) : WithBot (WithTop ℤ))
end
end GroundTheory.Heights₂.Heights.NumbersDVR


