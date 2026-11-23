-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_SumBoundStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:35:14.540504+00:00
-- url     : https://prove2.me/theorems/9c9f673f-046d-4576-8705-cff7eebce26e
-- title:
--   Sum Bound Statement
-- statement:
--   Definitions and structural lemmas for Sum Bound Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/SumBoundStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LiftFactorization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexOrder
noncomputable section
def Jf (p q : ℕ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.fromBlocks 1 0 0 (-1)
def IsUpq {p q : ℕ} (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) : Prop := gᴴ * Jf p q * g = Jf p q
def mob {p q : ℕ} (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Z : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin p) (Fin q) ℂ :=
  (g.toBlocks₁₁ * Z + g.toBlocks₁₂) * (g.toBlocks₂₁ * Z + g.toBlocks₂₂)⁻¹
def dpow {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) (s : ℝ) : ℝ := (1 - Z * Zᴴ).det.re ^ s
def DetIntStatement : Prop :=
  ∀ (f p q : ℕ) (s : ℝ), ((p + q : ℕ) : ℝ) - 1 < s →
    ∫⁻ v in Dset f p q, ENNReal.ofReal (∏ k, dpow (Zof v k) (s - (p + q : ℕ))) < ⊤
def SumBoundStatement : Prop :=
  ∀ (f p q : ℕ) (s : ℝ), 2 * (f : ℝ) * ((p + q : ℕ) : ℝ) ^ 2 < s →
    ∀ (Γ : Subgroup (Fin f → GL (Fin p ⊕ Fin q) ℂ)), DiscreteTopology Γ →
    (∀ γ ∈ Γ, ∀ k, IsUpq ((γ k : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)) →
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ v ∈ Dset f p q,
      ∑' γ : Γ, ENNReal.ofReal (∏ k, dpow (mob ((γ.1 k : GL (Fin p ⊕ Fin q) ℂ) :
        Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Zof v k)) s) ≤ C
end
end ReciprocityTheory.ChartRestriction.G.AR.Up


