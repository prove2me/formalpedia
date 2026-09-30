-- Prove2me | Definitions.Def_SP4SeamHemispherePart3
-- name    : SP4SeamHemispherePart3
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-07T07:00:39.939213+00:00
-- url     : https://prove2.me/theorems/59f0d2bb-8bf5-4d5d-8081-2b18ac601329
-- title:
--   Chart selection on the glued quotient
-- statement:
--   For $m\geq0$ and $\varphi:S^m\to S^m$ a homeomorphism, select at each point of the two-disk quotient the seam regional chart when the point belongs to the open seam, otherwise the corresponding first- or second-interior regional chart. The cover established in the preceding part ensures that every point belongs to the source of its selected chart. The atlas is the range of this selection, giving a charted-space structure modeled on $\mathbb R^{m+1}$. The bundle also names the open punctured Euclidean space $\mathbb R^{m+1}\setminus\{0\}$ used in radial smoothness arguments. This is a charted-space instance only: no global smooth-manifold instance or all-atlas compatibility theorem is included.
-- source:
--   Ryan Shin, Hemisphere.lean, unpublished Lean source (2026), selected constructor/instance support in lines 1857–3185; supported-environment transcription SHA-256 6a3aff0ac5800716d2e07d947579fa7972003cef657f6c6d1d7846ce4bf29215. Extracted by Lean compiler declaration/reference oracles, with namespace-only adaptations; no tracked source commit is claimed.

import Mathlib
import Definitions.Def_SPC4DiskCharts
import Definitions.Def_SP4Gluing
import Definitions.Def_SP4PullbackCharts
import Definitions.Def_SP4SeamPullbackGroupoid
import Definitions.Def_SP4SeamDisk
import Definitions.Def_SP4SeamHemispherePart1
import Definitions.Def_SP4SeamHemispherePart2

set_option autoImplicit false
namespace SP4Seam
open SP4Gluing SPC4Disk
open _root_.Homeomorph
open SP4Seam.Homeomorph

open Set Metric

open scoped ContDiff Manifold

section Hemisphere

variable {m : ℕ}

lemma mem_twistedChartAt_source
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
    (x : TwistedSphere φ) : x ∈ (twistedChartAt φ x).source := by
  simp only [twistedChartAt]
  split_ifs with h h1 h2
  · exact mem_regionChart_source (isOpen_openSeam φ) ⟨x, h⟩
  · exact mem_regionChart_source (isOpen_interiorFst φ) ⟨x, h1⟩
  · exact mem_regionChart_source (isOpen_interiorSnd φ) ⟨x, h2⟩
  · exfalso
    have hcov := openSeam_union_interiors φ
    have hx : x ∈ (Set.univ : Set (TwistedSphere φ)) := Set.mem_univ x
    rw [← hcov] at hx
    rcases hx with (hs | hf) | hsn
    · exact h hs
    · exact h1 hf
    · exact h2 hsn

noncomputable instance twistedSphereChartedSpace
    (φ : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 ≃ₜ
      sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :
    ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) (TwistedSphere φ) where
  atlas := Set.range (twistedChartAt φ)
  chartAt := twistedChartAt φ
  mem_chart_source := mem_twistedChartAt_source φ
  chart_mem_atlas x := ⟨x, rfl⟩

def puncturedOpens (m : ℕ) :
    TopologicalSpace.Opens (EuclideanSpace ℝ (Fin (m + 1))) :=
  ⟨{w : EuclideanSpace ℝ (Fin (m + 1)) | w ≠ 0}, isOpen_ne⟩

end Hemisphere

end SP4Seam


