-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:42.093894+00:00
-- url     : https://prove2.me/theorems/c304d712-b0ee-4a98-aa0f-4c849f8ec85e
-- title:
--   Stokes D
-- statement:
--   Definitions and structural lemmas for Stokes D, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/StokesD.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
section Leibniz
variable {D : ℕ}
end Leibniz
variable {e : ℕ} {X : Type} [TopologicalSpace X]
section Piece
variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))
end Piece
end
end ReciprocityTheory.AnForm.M


