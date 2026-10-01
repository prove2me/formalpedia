-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0075Root__8
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0075Root__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T02:18:33.740565+00:00
-- url     : https://prove2.me/theorems/cc3f630c-b18a-4f90-933a-74282634f082
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0075Root (+7 modules: GeneralCK.Certificates.E8TAxisZero0076Root, GeneralCK.Certificates.E8TAxisZero0077Root, GeneralCK.Cert…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0075Root (+7 modules: GeneralCK.Certificates.E8TAxisZero0076Root, GeneralCK.Certificates.E8TAxisZero0077Root, GeneralCK.Certificates.E8TAxisZero0078Root, GeneralCK.Certificates.E8TAxisZero0079Root, GeneralCK.Certificates.E8TAxisZero0080Root, GeneralCK.Certificates.E8TAxisZero0081Root, GeneralCK.Certificates.E8TAxisZero0082Root)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0075Root (+7 modules: GeneralCK.Certificates.E8TAxisZero0076Root, GeneralCK.Certificates.E8TAxisZero0077Root, GeneralCK.Certificates.E8TAxisZero0078Root, GeneralCK.Certificates.E8TAxisZero0079Root, GeneralCK.Certificates.E8TAxisZero0080Root, GeneralCK.Certificates.E8TAxisZero0081Root, GeneralCK.Certificates.E8TAxisZero0082Root)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0075Root (+7 modules: GeneralCK.Certificates.E8TAxisZero0076Root, GeneralCK.Certificates.E8TAxisZero0077Root, GeneralCK.Certificates.E8TAxisZero0078Root, GeneralCK.Certificates.E8TAxisZero0079Root, GeneralCK.Certificates.E8TAxisZero0080Root, GeneralCK.Certificates.E8TAxisZero0081Root, GeneralCK.Certificates.E8TAxisZero0082Root) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0075Root (+7 modules: GeneralCK/Certificates/E8TAxisZero0076Root, GeneralCK/Certificates/E8TAxisZero0077Root, GeneralCK/Certificates/E8TAxisZero0078Root, GeneralCK/Certificates/E8TAxisZero0079Root, GeneralCK/Certificates/E8TAxisZero0080Root, GeneralCK/Certificates/E8TAxisZero0081Root, GeneralCK/Certificates/E8TAxisZero0082Root).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0074Certified__9
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneratedGeometry

-- ===== source module GeneralCK.Certificates.E8TAxisZero0075Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0075Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (5718749999999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[373]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0075Certified.positiveAt
  norm_num [E8TAxisZero0075Geometry.rectangle, Rect.Covers, E8TAxisZero0075Geometry.sLower,
    E8TAxisZero0075Geometry.sUpper, E8TAxisZero0075Geometry.tLower, E8TAxisZero0075Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0075Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0076Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0076Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (11257812499999999999999999999999999999999999999999999999998088289706641 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[357]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0076Certified.positiveAt
  norm_num [E8TAxisZero0076Geometry.rectangle, Rect.Covers, E8TAxisZero0076Geometry.sLower,
    E8TAxisZero0076Geometry.sUpper, E8TAxisZero0076Geometry.tLower, E8TAxisZero0076Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0076Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0077Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0077Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(279 / 128 : ℚ), (2769531249999999999999999999999999999999999999999999999999362763235547 / 1250000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[341]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0077Certified.positiveAt
  norm_num [E8TAxisZero0077Geometry.rectangle, Rect.Covers, E8TAxisZero0077Geometry.sLower,
    E8TAxisZero0077Geometry.sUpper, E8TAxisZero0077Geometry.tLower, E8TAxisZero0077Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0077Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0078Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0078Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (279 / 128 : ℚ), (0 / 1 : ℚ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[325]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0078Certified.positiveAt
  norm_num [E8TAxisZero0078Geometry.rectangle, Rect.Covers, E8TAxisZero0078Geometry.sLower,
    E8TAxisZero0078Geometry.sUpper, E8TAxisZero0078Geometry.tLower, E8TAxisZero0078Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0078Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0079Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0079Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (10718749999999999999999999999999999999999999999999999999999362763235547 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[309]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0079Certified.positiveAt
  norm_num [E8TAxisZero0079Geometry.rectangle, Rect.Covers, E8TAxisZero0079Geometry.sLower,
    E8TAxisZero0079Geometry.sUpper, E8TAxisZero0079Geometry.tLower, E8TAxisZero0079Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0079Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0080Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0080Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (5269531249999999999999999999999999999999999999999999999999362763235547 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[293]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0080Certified.positiveAt
  norm_num [E8TAxisZero0080Geometry.rectangle, Rect.Covers, E8TAxisZero0080Geometry.sLower,
    E8TAxisZero0080Geometry.sUpper, E8TAxisZero0080Geometry.tLower, E8TAxisZero0080Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0080Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0081Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0081Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (5179687500000000000000000000000000000000000000000000000000637236764453 / 2500000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[277]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0081Certified.positiveAt
  norm_num [E8TAxisZero0081Geometry.rectangle, Rect.Covers, E8TAxisZero0081Geometry.sLower,
    E8TAxisZero0081Geometry.sUpper, E8TAxisZero0081Geometry.tLower, E8TAxisZero0081Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0081Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0082Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0082Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(2 / 1 : ℚ), (10179687500000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[261]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0082Certified.positiveAt
  norm_num [E8TAxisZero0082Geometry.rectangle, Rect.Covers, E8TAxisZero0082Geometry.sLower,
    E8TAxisZero0082Geometry.sUpper, E8TAxisZero0082Geometry.tLower, E8TAxisZero0082Geometry.tUpper]
  exact ⟨hs0, hs1, ht0, ht1⟩

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
end GeneralCK.Certificates.E8TAxisZero0082Root

end


