-- Prove2me | Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
-- name    : ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:28.554215+00:00
-- url     : https://prove2.me/theorems/89f551a8-83a2-456e-b295-c38b58a60035
-- title:
--   Matrix
-- statement:
--   Definitions and structural lemmas for Matrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/SkodaWeights/Matrix.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
namespace ReciprocityTheory.L2DbarEstimates
noncomputable def sqNorm {p : ℕ} (g : Fin p → ℂ) : ℝ := ∑ i, Complex.normSq (g i)
noncomputable def projPerp {p : ℕ} (g : Fin p → ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  1 - ((sqNorm g : ℝ) : ℂ)⁻¹ • vecMulVec g (star g)
def SkodaMatrixStatement : Prop :=
  ∀ (p n : ℕ) (g : Fin p → ℂ) (J V : Matrix (Fin p) (Fin n) ℂ), g ≠ 0 →
    Complex.normSq (trace (projPerp g * J * Vᵀ)) ≤
      ((p : ℝ) - 1) * ∑ i, sqNorm ((projPerp g * J) *ᵥ V i)
def SkodaPointwiseStatement : Prop :=
  ∀ (p n : ℕ) (g : Fin p → ℂ) (J V : Matrix (Fin p) (Fin n) ℂ), g ≠ 0 →
    sqNorm g * Complex.normSq (∑ i, ∑ k,
        (starRingEnd ℂ ((projPerp g * J) i k) / ((sqNorm g : ℝ) : ℂ)) * starRingEnd ℂ (V i k)) ≤
      ((p : ℝ) - 1) * ∑ i, sqNorm ((projPerp g * J) *ᵥ V i) / sqNorm g
def ProjPerpNormStatement : Prop :=
  ∀ (p : ℕ) (g w : Fin p → ℂ), g ≠ 0 →
    sqNorm (projPerp g *ᵥ w) = sqNorm w - Complex.normSq (star g ⬝ᵥ w) / sqNorm g
variable {p : ℕ}
end ReciprocityTheory.L2DbarEstimates


