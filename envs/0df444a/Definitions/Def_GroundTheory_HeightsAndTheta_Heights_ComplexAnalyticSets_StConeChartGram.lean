-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeChartGram
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeChartGram
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:48.009685+00:00
-- url     : https://prove2.me/theorems/bb1d3d8e-5da0-4e9b-823d-db8740ca3b51
-- title:
--   St Cone Chart Gram
-- statement:
--   Definitions and structural lemmas for St Cone Chart Gram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StConeChartGram.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConePolar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsChartGram
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
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
def ConeChartGram.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (g : (Fin n → ℂ) → ℝ) (A : Matrix (Fin e) (Fin n) ℂ),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J → (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → g (t • x) = g x) →
    ContinuousOn g {x | x ≠ 0} → IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A →
      coneIntegral h J e g =
        ∫ y, sheetSum (J ⊔ Ideal.span {linForm ℓ - 1}) A
          (fun x s => g x * ((e.factorial : ℝ) / Real.pi ^ e *
            gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y / h.dualNorm x ^ (2 * (e + 1)))) y
def lastCoordsProj (e : ℕ) : Matrix (Fin e) (Fin (e + 1)) ℂ := fun i j => if j = i.succ then 1 else 0
def dehomFirstCoord (e : ℕ) : MvPolynomial (Fin (e + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin e) ℂ :=
  aeval (Fin.cons 1 X)
end
end GroundTheory.Heights₂.Heights


