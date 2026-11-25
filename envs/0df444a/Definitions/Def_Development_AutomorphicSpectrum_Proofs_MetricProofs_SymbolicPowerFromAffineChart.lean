-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerFromAffineChart
-- name    : Development_AutomorphicSpectrum_Proofs_MetricProofs_SymbolicPowerFromAffineChart
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T14:31:14.246637+00:00
-- url     : https://prove2.me/theorems/0d5b649e-7d8c-46af-98fa-29fa4f3af1f7
-- title:
--   Symbolic Power From Affine Chart
-- statement:
--   Definitions and structural lemmas for Symbolic Power From Affine Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/SymbolicPowerFromAffineChart.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_AffineChartIdealPrimeAndSaturatedStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_exists_blockComponent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_isHomogeneous_of_isMultiHomogIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (cycBlockWt cyc_exists_blockComponent cyc_isHomogeneous_of_isMultiHomogIdeal)
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def mdeg (m : (Σ k, ι k) →₀ ℕ) : K → ℕ := fun k => ∑ i, m ⟨k, i⟩
open Classical in

def part (b : K → ℕ) (s : MvPolynomial (Σ k, ι k) ℂ) : MvPolynomial (Σ k, ι k) ℂ :=
  ∑ m ∈ s.support.filter (fun m => mdeg m = b), monomial m (coeff m s)
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom


