-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeBallCountRatioBound
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeBallCountRatioBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:51.285136+00:00
-- url     : https://prove2.me/theorems/1e2c3b15-5117-4b84-bff8-514c854b6e69
-- title:
--   Lattice Ball Count Ratio Bound
-- statement:
--   Definitions and structural lemmas for Lattice Ball Count Ratio Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeBallCountRatioBound.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.Adelic.Packing
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Λ : Type} [AddCommGroup Λ]
def Sep (e : Λ →+ V) (r R : ℝ) (s : Finset Λ) : Prop :=
  (∀ l ∈ s, ‖e l‖ ≤ R) ∧ (s : Set Λ).Pairwise fun a b => r ≤ ‖e a - e b‖
end GlobalTheory.CompanionTheory.Adelic.Packing


