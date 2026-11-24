-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegMassNearSmall
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegMassNearSmall
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:27:07.544171+00:00
-- url     : https://prove2.me/theorems/0c84109c-b63a-4a8e-8923-f68573fb28ae
-- title:
--   St Reg Mass Near Small
-- statement:
--   Definitions and structural lemmas for St Reg Mass Near Small, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegMassNearSmall.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLelongRegularise
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
def RegMassNearSmall.Statement : Prop :=
  ∀ (n d : ℕ) (J I : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (f : (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    (∀ i, SmoothNear (zeroSet J) (φ i)) → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ) →
    Continuous f → HasCompactSupport f →
      ∀ δ > 0, ∃ U : Set (Fin n → ℂ), IsOpen U ∧ zeroSet I ⊆ U ∧
        ∀ χ : (Fin n → ℂ) → ℝ, Continuous χ → (∀ x, |χ x| ≤ 1) → tsupport χ ⊆ U →
          ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
            |varInt J (d + 1) (fun x => χ x * f x) (vecCons (logReg u ε) φ)| ≤ δ
end
end GroundTheory.Heights₂.Heights


