-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormula
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:00.862613+00:00
-- url     : https://prove2.me/theorems/f921a54c-ff17-401f-8ce9-4fbed9106ca0
-- title:
--   Disintegration Density Formula
-- statement:
--   Definitions and structural lemmas for Disintegration Density Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
namespace GlobalTheory.CompanionTheory.SW.Slice
section Theta
variable {V X Q : Type} [TopologicalSpace V] [TopologicalSpace X] [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X]
def theta (g : V → X) (b₀ : X) (p : Q × (g ⁻¹' {b₀})) : V := p.1 • (p.2 : V)
end Theta
section Core
variable {V X Q : Type} [TopologicalSpace V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
  [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
  [SecondCountableTopology Q] [T2Space Q] [MeasurableSpace Q] [BorelSpace Q]
  [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X]
noncomputable def fibFam (g : V → X) (b₀ : X) (w : Q → ℝ≥0) (m : Measure (g ⁻¹' {b₀})) (b : X) :
    Measure V :=
  open Classical in
  if b ∈ Set.range (fun q : Q => q • b₀) then
    (w (Function.invFun (fun q : Q => q • b₀) b) : ℝ≥0∞) •
      m.map (fun z : (g ⁻¹' {b₀}) => Function.invFun (fun q : Q => q • b₀) b • (z : V))
  else 0
end Core
end GlobalTheory.CompanionTheory.SW.Slice


