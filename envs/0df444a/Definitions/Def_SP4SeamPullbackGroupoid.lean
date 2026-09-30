-- Prove2me | Definitions.Def_SP4SeamPullbackGroupoid
-- name    : SP4SeamPullbackGroupoid
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-07T06:54:50.802762+00:00
-- url     : https://prove2.me/theorems/60ca1913-5a37-449b-9bd2-37eec0e02dc7
-- title:
--   Pullback groupoid support for regional charts
-- statement:
--   Let $M$ be a charted space modeled on a topological space $H$, let $N$ be a topological space, and let $e:N\to M$ be a homeomorphism. Give $N$ the pulled-back charts $c\circ e$, where $c$ ranges over the atlas of $M$. For every structure groupoid $G$ on $H$ satisfied by the atlas of $M$, these charts on $N$ satisfy $G$. Their coordinate changes equal the original changes $c_2\circ c_1^{-1}$. This bundle supplies the proved groupoid support needed by the transported collar instances below; the charted-space construction itself is reused from the existing pullback definitions. It does not compare the pulled-back atlas with an independently prescribed atlas on $N$.
-- source:
--   Ryan Shin, PullbackGroupoid.lean, unpublished Lean source (2026), selected constructor/instance support in lines 84–114; supported-environment transcription SHA-256 f92aabb88c15cd62fd95afdeaa4c155b0daa62a8283b58a0848b576116fc8fa8. Extracted by Lean compiler declaration/reference oracles, with namespace-only adaptations; no tracked source commit is claimed.

import Mathlib
import Definitions.Def_SPC4DiskCharts
import Definitions.Def_SP4Gluing
import Definitions.Def_SP4PullbackCharts

set_option autoImplicit false
namespace SP4Seam
open SP4Gluing SPC4Disk
open _root_.Homeomorph

section

open Set ChartedSpace

open scoped Manifold Topology

variable {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] {N : Type*} [TopologicalSpace N]

namespace Homeomorph

omit [ChartedSpace H M] in

 theorem symm_trans_toOpenPartialHomeomorph (e : N ≃ₜ M) :
    e.toOpenPartialHomeomorph.symm ≫ₕ e.toOpenPartialHomeomorph =
      OpenPartialHomeomorph.refl M := by
  rw [← symm_toOpenPartialHomeomorph, ← trans_toOpenPartialHomeomorph,
    symm_trans_self, refl_toOpenPartialHomeomorph]

omit [ChartedSpace H M] in

theorem pullback_symm_trans (e : N ≃ₜ M) (c c' : OpenPartialHomeomorph M H) :
    (e.transOpenPartialHomeomorph c).symm ≫ₕ e.transOpenPartialHomeomorph c' =
      c.symm ≫ₕ c' := by
  simp only [transOpenPartialHomeomorph_eq_trans]
  rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc,
    ← OpenPartialHomeomorph.trans_assoc e.toOpenPartialHomeomorph.symm,
    symm_trans_toOpenPartialHomeomorph, OpenPartialHomeomorph.refl_trans]

theorem _root_.Homeomorph.sp4SeamPullbackHasGroupoid (e : N ≃ₜ M) (G : StructureGroupoid H)
    [HasGroupoid M G] :
    letI : ChartedSpace H N := e.sp4MissionPullbackChartedSpace
    HasGroupoid N G := by
  let _ : ChartedSpace H N := e.sp4MissionPullbackChartedSpace
  refine ⟨?_⟩
  rintro f g ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
  rw [pullback_symm_trans]
  exact StructureGroupoid.compatible _ hc hc'

end Homeomorph

end

end SP4Seam


