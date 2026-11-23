-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfB
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:35:19.545986+00:00
-- url     : https://prove2.me/theorems/805c3670-2ea2-468b-bc92-56e1ddca643b
-- title:
--   Poin Statement Pf B
-- statement:
--   Definitions and structural lemmas for Poin Statement Pf B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/PoinStatementPfB.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_PoinStatementPfA
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
def Hyp (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ) : Prop :=
  IsOrth X x0 ∧ PropDisc X ∧ IsMetricW X la W ∧ WLower X la W ∧
    4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧
    IsBEq X la P ∧ ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z
def supR (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (ρ : ℝ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  ⨆ (z : V (nd X)) (_ : ‖z‖ < ρ) (_ : cpt X x z ∈ X.dom),
    (ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) / W (cpt X x z)) ^ (1 / 2 : ℝ)
def LocStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), Hyp X x0 la W bb F P →
    ∀ x ∈ X.dom, ∃ ε > 0, ∃ u : X.Γ → ℝ, Summable u ∧
      ∀ γ : X.Γ, ∀ y ∈ Metric.ball x ε, ‖P (lact γ.1 y)‖ ≤ u γ
def BallStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), Hyp X x0 la W bb F P →
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, ∀ x ∈ X.dom, IsOrth X x →
      ∑' γ : X.Γ, ‖P (lact γ.1 x)‖ₑ ≤ ENNReal.ofReal C * supR X la W ρ x
def FFStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (bb : ℝ)
    (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ), Hyp X x0 la W bb F P →
    ∀ FF, IsFundSet X x0 FF → InFF X x0 W FF (poin X la P)
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf


