-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_FdFjNearSupOf
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_FdFjNearSupOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:25.905288+00:00
-- url     : https://prove2.me/theorems/cbef3be3-98ee-4347-8b30-a9208c081295
-- title:
--   Fd Fj Near Sup Of
-- statement:
--   Definitions and structural lemmas for Fd Fj Near Sup Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FundamentalDomainExtension/NearSupremumBounds/FdFjNearSupOf.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.FdFjNearSup.W
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex MeasureTheory
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def FjHolo : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ),
    P ∈ X.SS la → X.IsIso ξ → DifferentiableOn ℂ (X.fj la ξ ν P) X.dom
def FjRealFlow : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (ν : X.Ψ → ℝ),
    P ∈ X.SS la → X.IsIso ξ → ∀ x ∈ X.dom, ∀ s : X.Ψ → ℝ,
      X.fj la ξ ν P (X.flowV (X.embV ξ) (fun τ => (s τ : ℂ)) x) =
        cexp (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * (s τ : ℂ)) * X.fj la ξ ν P x
end
end PI.FdFjNearSup.W


