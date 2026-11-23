-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarChart
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:45.549034+00:00
-- url     : https://prove2.me/theorems/5bfe2ba8-d933-4e5d-8ea7-715e7d8cbfd1
-- title:
--   Haar Chart
-- statement:
--   Definitions and structural lemmas for Haar Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarChart.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_UnitaryHaarVolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal
namespace GlobalTheory.FlagQuotHaar
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def HaarChart (X : Data E r) (c : ℝ≥0∞) : Prop :=
  ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
    ∫⁻ g, φ (frameOf X g) ∂haarR X = c * ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X)
def trF {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ)
    (y : Frame X.Ψ r) : Frame X'.Ψ r :=
  fun τ' => (mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ * mat y (e.symm τ') : Matrix (Fin r) (Fin r) ℂ)
example (X : Data E r) (y : Frame X.Ψ r) : trF X X (Equiv.refl _) y = y := by
  funext τ
  show mat (baseFr X) τ * (mat (baseFr X) τ)⁻¹ * mat y τ = mat y τ
  have h : (mat (baseFr X) τ).det ≠ 0 := (X.signature τ).choose_spec.1
  rw [Matrix.mul_nonsing_inv _ h.isUnit, Matrix.one_mul]
end
end GlobalTheory.FlagQuotHaar


