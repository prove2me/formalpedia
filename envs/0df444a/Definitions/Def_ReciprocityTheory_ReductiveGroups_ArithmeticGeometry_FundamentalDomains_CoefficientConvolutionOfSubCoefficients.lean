-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientConvolutionOfSubCoefficients
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoefficientConvolutionOfSubCoefficients
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:01.799574+00:00
-- url     : https://prove2.me/theorems/46a2716d-ffe9-4303-a4e6-cf403966fa07
-- title:
--   Coefficient Convolution Of Sub Coefficients
-- statement:
--   Definitions and structural lemmas for Coefficient Convolution Of Sub Coefficients, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/CoefficientConvolutionOfSubCoefficients.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_RealEmbeddingCharacters_perL_rank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates.Y
  ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
def hline {r : ℕ} (X : Data E r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E) (x : Frame X.Ψ r)
    (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) : (Fin (Fintype.card X.Ψ) → ℂ) → ℂ :=
  fun t => P (X.flow ξ (fun τ => ∑ j, t j * (ω j τ : ℂ)) x)
def SubCoeffSt : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P →
    ∀ (ξ : Fin r → E), X.IsIso ξ → ∀ x ∈ X.dom, ∀ (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ),
      (∀ j, ω j ∈ X.periods la) → LinearIndependent ℝ ω →
      ∀ (k : Fin (Fintype.card X.Ψ) → ℤ) (ν : X.Ψ → ℝ), (∀ j, (k j : ℝ) = 2 * ∑ τ, ν τ * ω j τ) →
        fourCoeff (hline X P ξ x ω) 0 k = X.fj la ξ ν P x
variable {r : ℕ} (X : Data E r)
def bas1 (la : Wt X.Ψ r) : Module.Basis (Fin (Fintype.card X.Ψ)) ℤ (perL X la) :=
  Module.finBasisOfFinrankEq ℤ (perL X la) (perL_rank X la)
def om1 (la : Wt X.Ψ r) : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ := fun j => ((bas1 X la j : perL X la) : X.Ψ → ℝ)
def omc (la la' : Wt X.Ψ r) : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ :=
  fun j => ((X.chiOrd la' * X.chiOrd (la + la') : ℕ) : ℝ) • om1 X la j
section line
variable {X}
def Om (ξ : Fin r → E) (x : Frame X.Ψ r) (ω : Fin (Fintype.card X.Ψ) → X.Ψ → ℝ) :
    Set (Fin (Fintype.card X.Ψ) → ℝ) :=
  {b | (fun τ => ∑ j, b j * ω j τ) ∈ admissibleImaginary X ξ x}
end line
end
end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeMembership


