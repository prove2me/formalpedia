-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnimodIdx
-- name    : Formalism_PeriodIntegrals_UnimodIdx
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:38.571494+00:00
-- url     : https://prove2.me/theorems/220991cb-bf3b-488f-852c-de362eb9c571
-- title:
--   Unimod Idx
-- statement:
--   Definitions and structural lemmas for Unimod Idx, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnimodIdx.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
noncomputable section
namespace PI
def UnimodIdx : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [SigmaFinite μ], μ.IsHaarMeasure →
    ∀ (U : ℕ → Subgroup G), (∀ n, IsOpen (U n : Set G)) → (∀ V ∈ 𝓝 (1 : G), ∃ n, (U n : Set G) ⊆ V) →
    ∀ K : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
    (∀ x : G, (K.map (MulAut.conj x).toMonoidHom).relIndex K = (K.map (MulAut.conj x⁻¹).toMonoidHom).relIndex K) →
    μ.IsMulRightInvariant
end PI
end


