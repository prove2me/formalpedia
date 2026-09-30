-- Prove2me | Definitions.Def_SP4PullbackCharts
-- name    : SP4PullbackCharts
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-05T19:23:40.574033+00:00
-- url     : https://prove2.me/theorems/1a7a63cf-b9ec-4495-9218-f2c0c1132917
-- title:
--   An atlas pulled back by a homeomorphism
-- statement:
--   For topological spaces M and N and a chart model H, a homeomorphism e : N ≃ₜ M transports the given H-charted-space structure on M to N by composition of its charts with e. The construction is universe-polymorphic.
-- source:
--   Unpublished local Lean source SPC4.lean, SHA-256 b17fdb932034e5211d0db8171c08e2b3a182016bceaecdd2deb49c39d6bfd5cc; supported copy and exact oracle provenance in the accompanying local package. Transported-chart construction and pullback compatibility also use the unpublished local PullbackGroupoid.lean source, SHA-256 f92aabb88c15cd62fd95afdeaa4c155b0daa62a8283b58a0848b576116fc8fa8.

-- Derived from frozen local sources; exact source/hash provenance in items.json.
import Mathlib

set_option autoImplicit false

namespace SP4Mission

open _root_.Homeomorph

open Set ChartedSpace

open scoped Manifold Topology

variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {N : Type*} [TopologicalSpace N]

namespace Homeomorph

@[instance_reducible]
def _root_.Homeomorph.sp4MissionPullbackChartedSpace (e : N ≃ₜ M) : ChartedSpace H N where
  atlas := (e.transOpenPartialHomeomorph ·) '' atlas H M
  chartAt x := e.transOpenPartialHomeomorph (chartAt H (e x))
  mem_chart_source x := mem_chart_source H (e x)
  chart_mem_atlas x := ⟨_, chart_mem_atlas _ (e x), rfl⟩

end Homeomorph

end SP4Mission


