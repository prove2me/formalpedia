-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:21.888972+00:00
-- url     : https://prove2.me/theorems/e4eaae53-86c5-4be5-8bed-e6e979e140e6
-- title:
--   Ext FStatement Pf A
-- statement:
--   Definitions and structural lemmas for Ext FStatement Pf A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/ExtFStatementPfA.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetMeasStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowCoefficientBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
structure LUData (X : Data E r) (x0 : Frame X.Ψ r) where
  Δ : Frame X.Ψ r → ℂ
  zOf : Frame X.Ψ r → V (nd X)
  bOf : Frame X.Ψ r → Frame X.Ψ r
  hΔ : Differentiable ℂ Δ
  dense : ∀ x ∈ X.dom, ∀ ε > 0, ∃ y ∈ Metric.ball x ε, Δ y ≠ 0
  hz : DifferentiableOn ℂ zOf {x | x ∈ X.dom ∧ Δ x ≠ 0}
  hb : DifferentiableOn ℂ bOf {x | x ∈ X.dom ∧ Δ x ≠ 0}
  split : ∀ x ∈ X.dom, Δ x ≠ 0 → zOf x ∈ OmF X x0 ∧ bOf x ∈ Bor X.Ψ r ∧
    x = rmul (cpt X x0 (zOf x)) (bOf x)
  uniq : ∀ z ∈ OmF X x0, ∀ b ∈ Bor X.Ψ r, Δ (rmul (cpt X x0 z) b) ≠ 0 ∧
    zOf (rmul (cpt X x0 z) b) = z ∧ bOf (rmul (cpt X x0 z) b) = b
variable (X : Data E r)
def oneF : Frame X.Ψ r := fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)
def invF (b : Frame X.Ψ r) : Frame X.Ψ r := fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)
variable {X} {x0 : Frame X.Ψ r} (D : LUData X x0)
def cell : Set (Frame X.Ψ r) := {x | x ∈ X.dom ∧ D.Δ x ≠ 0}
open Classical in

def P0 (la : Wt X.Ψ r) (F : V (nd X) → ℂ) (x : Frame X.Ψ r) : ℂ :=
  if x ∈ X.dom ∧ D.Δ x ≠ 0 then bchar la (D.bOf x) * F (D.zOf x) else 0
end
end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf


