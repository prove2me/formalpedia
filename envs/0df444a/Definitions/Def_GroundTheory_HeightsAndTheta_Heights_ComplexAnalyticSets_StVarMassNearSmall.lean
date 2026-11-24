-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarMassNearSmall
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarMassNearSmall
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:32.820721+00:00
-- url     : https://prove2.me/theorems/8e6a12db-e593-425a-ad7d-93c39bca2059
-- title:
--   St Var Mass Near Small
-- statement:
--   Definitions and structural lemmas for St Var Mass Near Small, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StVarMassNearSmall.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CutOffNear
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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
def VarMassNearSmall.Statement : Prop :=
  ∀ (n d : ℕ) (W I : Ideal (MvPolynomial (Fin n) ℂ)) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (f : (Fin n → ℂ) → ℝ),
    W.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) →
    (∀ i, SmoothNear (zeroSet W) (φ i)) → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) →
    Continuous f → HasCompactSupport f →
      ∀ δ > 0, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet I ⊆ U ∧
        ∀ χ : (Fin n → ℂ) → ℝ, Continuous χ → (∀ x, |χ x| ≤ 1) → tsupport χ ⊆ U →
          |varInt W d (fun x => χ x * f x) φ| ≤ δ
end
end GroundTheory.Heights₂.Heights


