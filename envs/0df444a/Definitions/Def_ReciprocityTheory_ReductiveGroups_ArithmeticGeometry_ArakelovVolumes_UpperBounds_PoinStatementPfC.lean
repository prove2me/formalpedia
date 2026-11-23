-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfC
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:40.564028+00:00
-- url     : https://prove2.me/theorems/66f3ce0a-cbe3-46ba-b869-b90d24a96c02
-- title:
--   Poin Statement Pf C
-- statement:
--   Definitions and structural lemmas for Poin Statement Pf C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfC.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def Bset (X : Data E r) (x : Frame X.Ψ r) (ρ : ℝ) : Set (V (nd X)) :=
  {w | ‖w‖ < ρ ∧ cpt X x w ∈ X.dom}
def SubMeanStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ C : ℝ≥0∞, C < ⊤ ∧
    ∀ P : Frame X.Ψ r → ℂ, DifferentiableOn ℂ P X.dom → ∀ x ∈ X.dom, IsOrth X x →
      ‖P x‖ₑ ^ 2 ≤ C * ∫⁻ w in Bset X x ρ,
        ‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))
def SubMeanLocStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ x ∈ X.dom, IsOrth X x →
    ∃ ε > 0, ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ P : Frame X.Ψ r → ℂ, IsBEq X la P → ∀ y ∈ Metric.ball x ε,
      ‖P y‖ₑ ^ 2 ≤ C * ∫⁻ w in Bset X x ρ,
        ‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))
def SumBallStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), Hyp X x0 la W bb F P →
    ∃ ρ0 : ℝ, 0 < ρ0 ∧ ρ0 ≤ 1 ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, IsOrth X x →
      ∑' γ : X.Γ, (∫⁻ w in Bset X x ρ0,
        ‖P (lact γ.1 (cpt X x w))‖ₑ ^ 2 * W (lact γ.1 (cpt X x w))) ^ (1 / 2 : ℝ) ≤ C
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf


