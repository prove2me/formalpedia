-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_IsFirstChernFamily
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_SiegelWeilActions_IsFirstChernFamily
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:16.126017+00:00
-- url     : https://prove2.me/theorems/4fe270b0-e18e-44db-b7fc-65bdefa4ad0f
-- title:
--   Is First Chern Family
-- statement:
--   Definitions and structural lemmas for Is First Chern Family, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/SiegelWeilActions/IsFirstChernFamily.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace PositivityTheory.SiegelWeilFormula.Act
def LatHaar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (Γ : AddSubgroup V) [Countable Γ] (φ : V ≃ₜ+ V), (∀ x, φ x ∈ Γ ↔ x ∈ Γ) →
    ∀ s : Set V, IsAddFundamentalDomain Γ s μ → μ s ≠ 0 → μ s ≠ ⊤ → μ.map φ = μ
end PositivityTheory.SiegelWeilFormula.Act
end


