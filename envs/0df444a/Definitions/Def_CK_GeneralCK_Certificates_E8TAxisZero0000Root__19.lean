-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000Root__19
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0000Root__19
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:52:09.019151+00:00
-- url     : https://prove2.me/theorems/2703bd0f-6bf2-430c-adca-6a5db0769d80
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0000Root (+18 modules: GeneralCK.Certificates.E8TAxisZero0001Root, GeneralCK.Certificates.E8TAxisZero0002Root, GeneralCK.Cer…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0000Root (+18 modules: GeneralCK.Certificates.E8TAxisZero0001Root, GeneralCK.Certificates.E8TAxisZero0002Root, GeneralCK.Certificates.E8TAxisZero0003Root, GeneralCK.Certificates.E8TAxisZero0004Root, GeneralCK.Certificates.E8TAxisZero0005Root, GeneralCK.Certificates.E8TAxisZero0006Root, GeneralCK.Certificates.E8TAxisZero0007Root, GeneralCK.Certificates.E8TAxisZero0008Root, GeneralCK.Certificates.E8TAxisZero0009Root, GeneralCK.Certificates.E8TAxisZero0010Root, GeneralCK.Certificates.E8TAxisZero0011Root, GeneralCK.Certificates.E8TAxisZero0012Root, GeneralCK.Certificates.E8TAxisZero0013Root, GeneralCK.Certificates.E8TAxisZero0014Root, GeneralCK.Certificates.E8TAxisZero0015Root, GeneralCK.Certificates.E8TAxisZero0016Root, GeneralCK.Certificates.E8TAxisZero0017Root, GeneralCK.Certificates.E8TAxisZero0018Root)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0000Root (+18 modules: GeneralCK.Certificates.E8TAxisZero0001Root, GeneralCK.Certificates.E8TAxisZero0002Root, GeneralCK.Certificates.E8TAxisZero0003Root, GeneralCK.Certificates.E8TAxisZero0004Root, GeneralCK.Certificates.E8TAxisZero0005Root, GeneralCK.Certificates.E8TAxisZero0006Root, GeneralCK.Certificates.E8TAxisZero0007Root, GeneralCK.Certificates.E8TAxisZero0008Root, GeneralCK.Certificates.E8TAxisZero0009Root, GeneralCK.Certificates.E8TAxisZero0010Root, GeneralCK.Certificates.E8TAxisZero0011Root, GeneralCK.Certificates.E8TAxisZero0012Root, GeneralCK.Certificates.E8TAxisZero0013Root, GeneralCK.Certificates.E8TAxisZero0014Root, GeneralCK.Certificates.E8TAxisZero0015Root, GeneralCK.Certificates.E8TAxisZero0016Root, GeneralCK.Certificates.E8TAxisZero0017Root, GeneralCK.Certificates.E8TAxisZero0018Root)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0000Root (+18 modules: GeneralCK.Certificates.E8TAxisZero0001Root, GeneralCK.Certificates.E8TAxisZero0002Root, GeneralCK.Certificates.E8TAxisZero0003Root, GeneralCK.Certificates.E8TAxisZero0004Root, GeneralCK.Certificates.E8TAxisZero0005Root, GeneralCK.Certificates.E8TAxisZero0006Root, GeneralCK.Certificates.E8TAxisZero0007Root, GeneralCK.Certificates.E8TAxisZero0008Root, GeneralCK.Certificates.E8TAxisZero0009Root, GeneralCK.Certificates.E8TAxisZero0010Root, GeneralCK.Certificates.E8TAxisZero0011Root, GeneralCK.Certificates.E8TAxisZero0012Root, GeneralCK.Certificates.E8TAxisZero0013Root, GeneralCK.Certificates.E8TAxisZero0014Root, GeneralCK.Certificates.E8TAxisZero0015Root, GeneralCK.Certificates.E8TAxisZero0016Root, GeneralCK.Certificates.E8TAxisZero0017Root, GeneralCK.Certificates.E8TAxisZero0018Root) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0000Root (+18 modules: GeneralCK/Certificates/E8TAxisZero0001Root, GeneralCK/Certificates/E8TAxisZero0002Root, GeneralCK/Certificates/E8TAxisZero0003Root, GeneralCK/Certificates/E8TAxisZero0004Root, GeneralCK/Certificates/E8TAxisZero0005Root, GeneralCK/Certificates/E8TAxisZero0006Root, GeneralCK/Certificates/E8TAxisZero0007Root, GeneralCK/Certificates/E8TAxisZero0008Root, GeneralCK/Certificates/E8TAxisZero0009Root, GeneralCK/Certificates/E8TAxisZero0010Root, GeneralCK/Certificates/E8TAxisZero0011Root, GeneralCK/Certificates/E8TAxisZero0012Root, GeneralCK/Certificates/E8TAxisZero0013Root, GeneralCK/Certificates/E8TAxisZero0014Root, GeneralCK/Certificates/E8TAxisZero0015Root, GeneralCK/Certificates/E8TAxisZero0016Root, GeneralCK/Certificates/E8TAxisZero0017Root, GeneralCK/Certificates/E8TAxisZero0018Root).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0000Certified__18
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisGeneratedGeometry
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0014LCertified
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0014RCertified

-- ===== source module GeneralCK.Certificates.E8TAxisZero0000Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0000Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(17812500000000000000000000000000000000000000000000000000001393955422241 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (3 / 40 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[5]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0000Certified.positiveAt
  norm_num [E8TAxisZero0000Geometry.rectangle, Rect.Covers, E8TAxisZero0000Geometry.sLower,
    E8TAxisZero0000Geometry.sUpper, E8TAxisZero0000Geometry.tLower, E8TAxisZero0000Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0000Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0001Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0001Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(13500000000000000000000000000000000000000000000000000000000637236764453 / 200000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (17812500000000000000000000000000000000000000000000000000001393955422241 / 250000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[3]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0001Certified.positiveAt
  norm_num [E8TAxisZero0001Geometry.rectangle, Rect.Covers, E8TAxisZero0001Geometry.sLower,
    E8TAxisZero0001Geometry.sUpper, E8TAxisZero0001Geometry.tLower, E8TAxisZero0001Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0001Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0002Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0002Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(31875000000000000000000000000000000000000000000000000000000398272977783 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (13500000000000000000000000000000000000000000000000000000000637236764453 / 200000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[2]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0002Certified.positiveAt
  norm_num [E8TAxisZero0002Geometry.rectangle, Rect.Covers, E8TAxisZero0002Geometry.sLower,
    E8TAxisZero0002Geometry.sUpper, E8TAxisZero0002Geometry.tLower, E8TAxisZero0002Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0002Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0003Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0003Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(3 / 50 : ℚ), (31875000000000000000000000000000000000000000000000000000000398272977783 / 500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[0]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0003Certified.positiveAt
  norm_num [E8TAxisZero0003Geometry.rectangle, Rect.Covers, E8TAxisZero0003Geometry.sLower,
    E8TAxisZero0003Geometry.sUpper, E8TAxisZero0003Geometry.tLower, E8TAxisZero0003Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0003Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0004Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0004Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(3 / 32 : ℚ), (1 / 10 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[12]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0004Certified.positiveAt
  norm_num [E8TAxisZero0004Geometry.rectangle, Rect.Covers, E8TAxisZero0004Geometry.sLower,
    E8TAxisZero0004Geometry.sUpper, E8TAxisZero0004Geometry.tLower, E8TAxisZero0004Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0004Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0005Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0005Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(3500000000000000000000000000000000000000000000000000000000637236764453 / 40000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (3 / 32 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[10]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0005Certified.positiveAt
  norm_num [E8TAxisZero0005Geometry.rectangle, Rect.Covers, E8TAxisZero0005Geometry.sLower,
    E8TAxisZero0005Geometry.sUpper, E8TAxisZero0005Geometry.tLower, E8TAxisZero0005Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0005Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0006Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0006Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(81250000000000000000000000000000000000000000000000000000011948189333493 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (3500000000000000000000000000000000000000000000000000000000637236764453 / 40000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[8]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0006Certified.positiveAt
  norm_num [E8TAxisZero0006Geometry.rectangle, Rect.Covers, E8TAxisZero0006Geometry.sLower,
    E8TAxisZero0006Geometry.sUpper, E8TAxisZero0006Geometry.tLower, E8TAxisZero0006Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0006Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0007Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0007Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(3 / 40 : ℚ), (81250000000000000000000000000000000000000000000000000000011948189333493 / 1000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[6]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0007Certified.positiveAt
  norm_num [E8TAxisZero0007Geometry.rectangle, Rect.Covers, E8TAxisZero0007Geometry.sLower,
    E8TAxisZero0007Geometry.sUpper, E8TAxisZero0007Geometry.tLower, E8TAxisZero0007Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0007Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0008Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0008Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(11562500000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (1 / 4 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[48]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0008Certified.positiveAt
  norm_num [E8TAxisZero0008Geometry.rectangle, Rect.Covers, E8TAxisZero0008Geometry.sLower,
    E8TAxisZero0008Geometry.sUpper, E8TAxisZero0008Geometry.tLower, E8TAxisZero0008Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0008Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0009Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0009Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (11562500000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[44]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0009Certified.positiveAt
  norm_num [E8TAxisZero0009Geometry.rectangle, Rect.Covers, E8TAxisZero0009Geometry.sLower,
    E8TAxisZero0009Geometry.sUpper, E8TAxisZero0009Geometry.tLower, E8TAxisZero0009Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0009Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0010Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0010Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (5312500000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[40]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0010Certified.positiveAt
  norm_num [E8TAxisZero0010Geometry.rectangle, Rect.Covers, E8TAxisZero0010Geometry.sLower,
    E8TAxisZero0010Geometry.sUpper, E8TAxisZero0010Geometry.tLower, E8TAxisZero0010Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0010Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0011Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0011Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(8749999999999999999999999999999999999999999999999999999999601727022217 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (4843749999999999999999999999999999999999999999999999999999601727022217 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[36]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0011Certified.positiveAt
  norm_num [E8TAxisZero0011Geometry.rectangle, Rect.Covers, E8TAxisZero0011Geometry.sLower,
    E8TAxisZero0011Geometry.sUpper, E8TAxisZero0011Geometry.tLower, E8TAxisZero0011Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0011Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0012Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0012Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(5 / 32 : ℚ), (8749999999999999999999999999999999999999999999999999999999601727022217 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[32]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0012Certified.positiveAt
  norm_num [E8TAxisZero0012Geometry.rectangle, Rect.Covers, E8TAxisZero0012Geometry.sLower,
    E8TAxisZero0012Geometry.sUpper, E8TAxisZero0012Geometry.tLower, E8TAxisZero0012Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0012Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0013Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0013Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(6875000000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (5 / 32 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[28]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0013Certified.positiveAt
  norm_num [E8TAxisZero0013Geometry.rectangle, Rect.Covers, E8TAxisZero0013Geometry.sLower,
    E8TAxisZero0013Geometry.sUpper, E8TAxisZero0013Geometry.tLower, E8TAxisZero0013Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0013Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0014Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0014Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(2968750000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (6875000000000000000000000000000000000000000000000000000000398272977783 / 50000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[24]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  by_cases hcut2 : s ≤ ((12812500000000000000000000000000000000000000000000000000001194818933349 / 100000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ)
  ·
    apply E8TAxisZero0014LCertified.positiveAt
    norm_num [E8TAxisZero0014LGeometry.rectangle, Rect.Covers, E8TAxisZero0014LGeometry.sLower,
      E8TAxisZero0014LGeometry.sUpper, E8TAxisZero0014LGeometry.tLower, E8TAxisZero0014LGeometry.tUpper] at *
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  ·
    apply E8TAxisZero0014RCertified.positiveAt
    norm_num [E8TAxisZero0014RGeometry.rectangle, Rect.Covers, E8TAxisZero0014RGeometry.sLower,
      E8TAxisZero0014RGeometry.sUpper, E8TAxisZero0014RGeometry.tLower, E8TAxisZero0014RGeometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0014Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0015Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0015Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(7 / 64 : ℚ), (2968750000000000000000000000000000000000000000000000000000398272977783 / 25000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[21]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0015Certified.positiveAt
  norm_num [E8TAxisZero0015Geometry.rectangle, Rect.Covers, E8TAxisZero0015Geometry.sLower,
    E8TAxisZero0015Geometry.sUpper, E8TAxisZero0015Geometry.tLower, E8TAxisZero0015Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0015Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0016Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0016Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(1 / 10 : ℚ), (7 / 64 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[13]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0016Certified.positiveAt
  norm_num [E8TAxisZero0016Geometry.rectangle, Rect.Covers, E8TAxisZero0016Geometry.sLower,
    E8TAxisZero0016Geometry.sUpper, E8TAxisZero0016Geometry.tLower, E8TAxisZero0016Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0016Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0017Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0017Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(15 / 32 : ℚ), (1 / 2 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[80]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0017Certified.positiveAt
  norm_num [E8TAxisZero0017Geometry.rectangle, Rect.Covers, E8TAxisZero0017Geometry.sLower,
    E8TAxisZero0017Geometry.sUpper, E8TAxisZero0017Geometry.tLower, E8TAxisZero0017Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0017Root

end

-- ===== source module GeneralCK.Certificates.E8TAxisZero0018Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0018Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(7 / 16 : ℚ), (15 / 32 : ℚ), (0 / 1 : ℚ), (24999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[76]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0018Certified.positiveAt
  norm_num [E8TAxisZero0018Geometry.rectangle, Rect.Covers, E8TAxisZero0018Geometry.sLower,
    E8TAxisZero0018Geometry.sUpper, E8TAxisZero0018Geometry.tLower, E8TAxisZero0018Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0018Root

end


