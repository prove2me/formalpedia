-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_AestronglyMeasurableCompRep
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_AestronglyMeasurableCompRep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:56:08.707683+00:00
-- url     : https://prove2.me/theorems/e2d0ec31-0307-40b8-8fa6-7d6104ffa347
-- title:
--   Aestrongly Measurable Comp Rep
-- statement:
--   Definitions and structural lemmas for Aestrongly Measurable Comp Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/AestronglyMeasurableCompRep.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped ENNReal symmDiff Topology Pointwise
namespace GlobalTheory.RightRegFund
variable {G : Type} [Group G]
def Good (Γ : Subgroup G) (D : Set G) (y : G) : Prop :=
  ∀ γ γ' : Γ, (γ : G) * y ∈ D → (γ' : G) * y ∈ D → γ = γ'
variable {Γ : Subgroup G} {D : Set G} {r : G → G}
variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant] [Countable Γ]
variable [μ.IsMulRightInvariant]
variable {R : G → (Lp ℂ 2 (μ.restrict D) →L[ℂ] Lp ℂ 2 (μ.restrict D))}
end GlobalTheory.RightRegFund


