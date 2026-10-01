-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0019Root__19
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0019Root__19
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:49:51.712183+00:00
-- url     : https://prove2.me/theorems/91ff432b-ca01-4716-926c-6f4ad1795bde
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0019Root (+18 modules: GeneralCK.Certificates.E8TAxisZero0020Root, GeneralCK.Certificates.E8TAxisZero0021Root, GeneralCK.Cer…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0019Root (+18 modules: GeneralCK.Certificates.E8TAxisZero0020Root, GeneralCK.Certificates.E8TAxisZero0021Root, GeneralCK.Certificates.E8TAxisZero0022Root, GeneralCK.Certificates.E8TAxisZero0023Root, GeneralCK.Certificates.E8TAxisZero0024Root, GeneralCK.Certificates.E8TAxisZero0025Root, GeneralCK.Certificates.E8TAxisZero0026Root, GeneralCK.Certificates.E8TAxisZero0027Root, GeneralCK.Certificates.E8TAxisZero0028Root, GeneralCK.Certificates.E8TAxisZero0029Root, GeneralCK.Certificates.E8TAxisZero0030Root, GeneralCK.Certificates.E8TAxisZero0031Root, GeneralCK.Certificates.E8TAxisZero0032Root, GeneralCK.Certificates.E8TAxisZero0033Root, GeneralCK.Certificates.E8TAxisZero0034Root, GeneralCK.Certificates.E8TAxisZero0035Root, GeneralCK.Certificates.E8TAxisZero0036Root, GeneralCK.Certificates.E8TAxisZero0037Root)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0019Root (+18 modules: GeneralCK.Certificates.E8TAxisZero0020Root, GeneralCK.Certificates.E8TAxisZero0021Root, GeneralCK.Certificates.E8TAxisZero0022Root, GeneralCK.Certificates.E8TAxisZero0023Root, GeneralCK.Certificates.E8TAxisZero0024Root, GeneralCK.Certificates.E8TAxisZero0025Root, GeneralCK.Certificates.E8TAxisZero0026Root, GeneralCK.Certificates.E8TAxisZero0027Root, GeneralCK.Certificates.E8TAxisZero0028Root, GeneralCK.Certificates.E8TAxisZero0029Root, GeneralCK.Certificates.E8TAxisZero0030Root, GeneralCK.Certificates.E8TAxisZero0031Root, GeneralCK.Certificates.E8TAxisZero0032Root, GeneralCK.Certificates.E8TAxisZero0033Root, GeneralCK.Certificates.E8TAxisZero0034Root, GeneralCK.Certificates.E8TAxisZero0035Root, GeneralCK.Certificates.E8TAxisZero0036Root, GeneralCK.Certificates.E8TAxisZero0037Root)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0019Root (+18 modules: GeneralCK.Certificates.E8TAxisZero0020Root, GeneralCK.Certificates.E8TAxisZero0021Root, GeneralCK.Certificates.E8TAxisZero0022Root, GeneralCK.Certificates.E8TAxisZero0023Root, GeneralCK.Certificates.E8TAxisZero0024Root, GeneralCK.Certificates.E8TAxisZero0025Root, GeneralCK.Certificates.E8TAxisZero0026Root, GeneralCK.Certificates.E8TAxisZero0027Root, GeneralCK.Certificates.E8TAxisZero0028Root, GeneralCK.Certificates.E8TAxisZero0029Root, GeneralCK.Certificates.E8TAxisZero0030Root, GeneralCK.Certificates.E8TAxisZero0031Root, GeneralCK.Certificates.E8TAxisZero0032Root, GeneralCK.Certificates.E8TAxisZero0033Root, GeneralCK.Certificates.E8TAxisZero0034Root, GeneralCK.Certificates.E8TAxisZero0035Root, GeneralCK.Certificates.E8TAxisZero0036Root, GeneralCK.Certificates.E8TAxisZero0037Root) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0019Root (+18 modules: GeneralCK/Certificates/E8TAxisZero0020Root, GeneralCK/Certificates/E8TAxisZero0021Root, GeneralCK/Certificates/E8TAxisZero0022Root, GeneralCK/Certificates/E8TAxisZero0023Root, GeneralCK/Certificates/E8TAxisZero0024Root, GeneralCK/Certificates/E8TAxisZero0025Root, GeneralCK/Certificates/E8TAxisZero0026Root, GeneralCK/Certificates/E8TAxisZero0027Root, GeneralCK/Certificates/E8TAxisZero0028Root, GeneralCK/Certificates/E8TAxisZero0029Root, GeneralCK/Certificates/E8TAxisZero0030Root, GeneralCK/Certificates/E8TAxisZero0031Root, GeneralCK/Certificates/E8TAxisZero0032Root, GeneralCK/Certificates/E8TAxisZero0033Root, GeneralCK/Certificates/E8TAxisZero0034Root, GeneralCK/Certificates/E8TAxisZero0035Root, GeneralCK/Certificates/E8TAxisZero0036Root, GeneralCK/Certificates/E8TAxisZero0037Root).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0019Certified__19
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneratedGeometry

-- ===== source module GeneralCK.Certificates.E8TAxisZero0019Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0019Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(13 / 32 : ℚ), (7 / 16 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[72]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0019Certified.positiveAt
  norm_num [E8TAxisZero0019Geometry.rectangle, Rect.Covers, E8TAxisZero0019Geometry.sLower,
    E8TAxisZero0019Geometry.sUpper, E8TAxisZero0019Geometry.tLower, E8TAxisZero0019Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0019Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0020Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0020Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(3 / 8 : ℚ), (13 / 32 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[68]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0020Certified.positiveAt
  norm_num [E8TAxisZero0020Geometry.rectangle, Rect.Covers, E8TAxisZero0020Geometry.sLower,
    E8TAxisZero0020Geometry.sUpper, E8TAxisZero0020Geometry.tLower, E8TAxisZero0020Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0020Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0021Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0021Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(11 / 32 : ℚ), (3 / 8 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[64]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0021Certified.positiveAt
  norm_num [E8TAxisZero0021Geometry.rectangle, Rect.Covers, E8TAxisZero0021Geometry.sLower,
    E8TAxisZero0021Geometry.sUpper, E8TAxisZero0021Geometry.tLower, E8TAxisZero0021Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0021Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0022Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0022Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(5 / 16 : ℚ), (11 / 32 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[60]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0022Certified.positiveAt
  norm_num [E8TAxisZero0022Geometry.rectangle, Rect.Covers, E8TAxisZero0022Geometry.sLower,
    E8TAxisZero0022Geometry.sUpper, E8TAxisZero0022Geometry.tLower, E8TAxisZero0022Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0022Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0023Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0023Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(9 / 32 : ℚ), (5 / 16 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[56]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0023Certified.positiveAt
  norm_num [E8TAxisZero0023Geometry.rectangle, Rect.Covers, E8TAxisZero0023Geometry.sLower,
    E8TAxisZero0023Geometry.sUpper, E8TAxisZero0023Geometry.tLower, E8TAxisZero0023Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0023Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0024Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0024Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(1 / 4 : ℚ), (9 / 32 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[52]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0024Certified.positiveAt
  norm_num [E8TAxisZero0024Geometry.rectangle, Rect.Covers, E8TAxisZero0024Geometry.sLower,
    E8TAxisZero0024Geometry.sUpper, E8TAxisZero0024Geometry.tLower, E8TAxisZero0024Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0024Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0025Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0025Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(15 / 16 : ℚ), (1 / 1 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[129]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0025Certified.positiveAt
  norm_num [E8TAxisZero0025Geometry.rectangle, Rect.Covers, E8TAxisZero0025Geometry.sLower,
    E8TAxisZero0025Geometry.sUpper, E8TAxisZero0025Geometry.tLower, E8TAxisZero0025Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0025Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0026Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0026Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(7 / 8 : ℚ), (15 / 16 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[125]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0026Certified.positiveAt
  norm_num [E8TAxisZero0026Geometry.rectangle, Rect.Covers, E8TAxisZero0026Geometry.sLower,
    E8TAxisZero0026Geometry.sUpper, E8TAxisZero0026Geometry.tLower, E8TAxisZero0026Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0026Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0027Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0027Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(13 / 16 : ℚ), (7 / 8 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[121]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0027Certified.positiveAt
  norm_num [E8TAxisZero0027Geometry.rectangle, Rect.Covers, E8TAxisZero0027Geometry.sLower,
    E8TAxisZero0027Geometry.sUpper, E8TAxisZero0027Geometry.tLower, E8TAxisZero0027Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0027Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0028Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0028Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(3 / 4 : ℚ), (13 / 16 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[117]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0028Certified.positiveAt
  norm_num [E8TAxisZero0028Geometry.rectangle, Rect.Covers, E8TAxisZero0028Geometry.sLower,
    E8TAxisZero0028Geometry.sUpper, E8TAxisZero0028Geometry.tLower, E8TAxisZero0028Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0028Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0029Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0029Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(11 / 16 : ℚ), (3 / 4 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[113]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0029Certified.positiveAt
  norm_num [E8TAxisZero0029Geometry.rectangle, Rect.Covers, E8TAxisZero0029Geometry.sLower,
    E8TAxisZero0029Geometry.sUpper, E8TAxisZero0029Geometry.tLower, E8TAxisZero0029Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0029Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0030Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0030Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(5 / 8 : ℚ), (11 / 16 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[109]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0030Certified.positiveAt
  norm_num [E8TAxisZero0030Geometry.rectangle, Rect.Covers, E8TAxisZero0030Geometry.sLower,
    E8TAxisZero0030Geometry.sUpper, E8TAxisZero0030Geometry.tLower, E8TAxisZero0030Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0030Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0031Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0031Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(19 / 32 : ℚ), (5 / 8 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[108]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0031Certified.positiveAt
  norm_num [E8TAxisZero0031Geometry.rectangle, Rect.Covers, E8TAxisZero0031Geometry.sLower,
    E8TAxisZero0031Geometry.sUpper, E8TAxisZero0031Geometry.tLower, E8TAxisZero0031Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0031Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0032Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0032Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(9 / 16 : ℚ), (19 / 32 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[100]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0032Certified.positiveAt
  norm_num [E8TAxisZero0032Geometry.rectangle, Rect.Covers, E8TAxisZero0032Geometry.sLower,
    E8TAxisZero0032Geometry.sUpper, E8TAxisZero0032Geometry.tLower, E8TAxisZero0032Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0032Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0033Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0033Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(17 / 32 : ℚ), (9 / 16 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[92]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0033Certified.positiveAt
  norm_num [E8TAxisZero0033Geometry.rectangle, Rect.Covers, E8TAxisZero0033Geometry.sLower,
    E8TAxisZero0033Geometry.sUpper, E8TAxisZero0033Geometry.tLower, E8TAxisZero0033Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0033Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0034Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0034Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(1 / 2 : ℚ), (17 / 32 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[84]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0034Certified.positiveAt
  norm_num [E8TAxisZero0034Geometry.rectangle, Rect.Covers, E8TAxisZero0034Geometry.sLower,
    E8TAxisZero0034Geometry.sUpper, E8TAxisZero0034Geometry.tLower, E8TAxisZero0034Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0034Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0035Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0035Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(31 / 16 : ℚ), (2 / 1 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[253]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0035Certified.positiveAt
  norm_num [E8TAxisZero0035Geometry.rectangle, Rect.Covers, E8TAxisZero0035Geometry.sLower,
    E8TAxisZero0035Geometry.sUpper, E8TAxisZero0035Geometry.tLower, E8TAxisZero0035Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0035Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0036Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0036Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(15 / 8 : ℚ), (31 / 16 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[245]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0036Certified.positiveAt
  norm_num [E8TAxisZero0036Geometry.rectangle, Rect.Covers, E8TAxisZero0036Geometry.sLower,
    E8TAxisZero0036Geometry.sUpper, E8TAxisZero0036Geometry.tLower, E8TAxisZero0036Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0036Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0037Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0037Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(29 / 16 : ℚ), (15 / 8 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[237]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0037Certified.positiveAt
  norm_num [E8TAxisZero0037Geometry.rectangle, Rect.Covers, E8TAxisZero0037Geometry.sLower,
    E8TAxisZero0037Geometry.sUpper, E8TAxisZero0037Geometry.tLower, E8TAxisZero0037Geometry.tUpper] at *
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem cellPositive : CellPositive rectangle := by
  intro s t _ h
  exact positiveAt h

theorem zeroEdge_positive {s : ℝ}
    (hs : s ∈ Icc rectangle.s0 rectangle.s1) : 0 < e8RegularDeltaT s 0 := by
  apply positiveAt
  refine ⟨hs.1, hs.2, ?_, ?_⟩ <;> norm_num [rectangle, rationalRectangle]

#print axioms historical_index_checked
#print axioms positiveAt
#print axioms cellPositive
#print axioms zeroEdge_positive
end GeneralCK.Certificates.E8TAxisZero0037Root

end


