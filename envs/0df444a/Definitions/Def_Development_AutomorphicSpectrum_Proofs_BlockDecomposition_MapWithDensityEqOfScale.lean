-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MapWithDensityEqOfScale
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MapWithDensityEqOfScale
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:47.318168+00:00
-- url     : https://prove2.me/theorems/05c1aa8b-af40-4562-b8c5-0567c02a9403
-- title:
--   Map With Density Eq Of Scale
-- statement:
--   Definitions and structural lemmas for Map With Density Eq Of Scale, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TopoPolish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal
namespace GlobalTheory.CompanionTheory.QuotVan
def HaarNM : Prop := ∀ {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [LocallyCompactSpace Q] [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
  (νQ : Measure Q) [νQ.IsHaarMeasure] (N M : Subgroup Q) [N.Normal]
  (_ : IsClosed (N : Set Q)) (_ : IsClosed (M : Set Q))
  (_ : ∀ q : Q, ∃ u ∈ N, ∃ m ∈ M, q = u * m) (_ : N ⊓ M = ⊥)
  (νN : Measure N) [νN.IsHaarMeasure] (νM : Measure M) [νM.IsHaarMeasure],
  ∃ δ : M → ℝ≥0∞, Measurable δ ∧ (∀ m, δ m ≠ ∞) ∧
    νQ = ((νN.prod νM).withDensity fun p => δ p.2).map (fun p : N × M => (p.1 : Q) * (p.2 : Q))
section
variable {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
noncomputable def conjCE (N : Subgroup Q) [N.Normal] (g : Q) : N ≃ₜ* N where
  toMulEquiv := MulAut.conjNormal g
  continuous_toFun := by
    refine continuous_induced_rng.2 ?_
    have : Continuous fun u : N => g * (u : Q) * g⁻¹ := by fun_prop
    exact this
  continuous_invFun := by
    refine continuous_induced_rng.2 ?_
    have : Continuous fun u : N => g⁻¹ * (u : Q) * g⁻¹⁻¹ := by fun_prop
    exact this
variable [MeasurableSpace Q] [BorelSpace Q] [SecondCountableTopology Q] [T2Space Q]
variable (N M : Subgroup Q) [N.Normal] [LocallyCompactSpace N] [SecondCountableTopology N]
  [SecondCountableTopology M]
noncomputable def modInv (m : M) : ℝ≥0∞ :=
  ((mulEquivHaarChar (conjCE N (m : Q)) : ℝ≥0) : ℝ≥0∞)⁻¹
end
end GlobalTheory.CompanionTheory.QuotVan


