-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:28:57.805016+00:00
-- url     : https://prove2.me/theorems/58e6324e-7acf-4ccc-a50e-426d0fd951c0
-- title:
--   Pnorm Inv Statement
-- statement:
--   Definitions and structural lemmas for Pnorm Inv Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/ArakelovInstances/PnormInvStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_IsStrictDom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Inst
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def NfacRmulStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
    X.nfac la (rmul x b) = ‖bchar la b‖⁻¹ * X.nfac la x
def NfacLactStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r), ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, X.nfac la (lact γ x) = X.nfac la x
def PnormInvStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P →
    ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      X.pnorm la P (lact γ (rmul x b)) = X.pnorm la P x
def KapGGStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 x1 : Frame X.Ψ r) (γ : GL (Fin r) E) (U : Set (V (nd X)))
    (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Frame X.Ψ r), IsOpen U → DifferentiableOn ℂ Φ U →
    (∀ z ∈ U, cpt X x0 z ∈ X.dom ∧ bf z ∈ Bor X.Ψ r ∧
      cpt X x0 z = lact γ (rmul (cpt X x1 (Φ z)) (bf z))) →
    ∀ z ∈ U, (fderiv ℂ Φ z).det = bchar (kapW X) (bf z)
def CurvGGStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (x0 : Frame X.Ψ r) (z : V (nd X)), cpt X x0 z ∈ X.dom →
    (X.IsDominant la → ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ (leviV (nd X) (fun w => ((-2 * Real.log (X.nfac la (cpt X x0 w)) : ℝ) : ℂ)) z ξ).re) ∧
    (IsStrictDom X la → ∀ ξ : Fin (nd X) → ℂ, ξ ≠ 0 →
      0 < (leviV (nd X) (fun w => ((-2 * Real.log (X.nfac la (cpt X x0 w)) : ℝ) : ℂ)) z ξ).re)
def LineBundleFirstBoundGlobalGeneration : Prop :=
  ∀ (r : ℕ) (X : Data E r), 0 < r →
    (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, X.la1 (lact γ (rmul x b)) = X.la1 x) ∧
    ContinuousOn X.la1 X.dom ∧ ∀ x ∈ X.dom, 0 < X.la1 x
end
end ReciprocityTheory.ChartRestriction.G.AR.Inst


