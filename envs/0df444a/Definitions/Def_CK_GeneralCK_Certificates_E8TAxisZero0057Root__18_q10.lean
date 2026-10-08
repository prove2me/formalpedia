-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057Root__18_q10
-- name    : CK_GeneralCK_Certificates_E8TAxisZero0057Root__18_q10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-05T07:55:18.482913+00:00
-- url     : https://prove2.me/theorems/c95561ca-4160-49a9-bd66-59c474ff5454
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisZero0057Root (+17 modules: GeneralCK.Certificates.E8TAxisZero0058Root, GeneralCK.Certificates.E8TAxisZero0059Root, GeneralCK.Cer…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisZero0057Root (+17 modules: GeneralCK.Certificates.E8TAxisZero0058Root, GeneralCK.Certificates.E8TAxisZero0059Root, GeneralCK.Certificates.E8TAxisZero0060Root, GeneralCK.Certificates.E8TAxisZero0061Root, GeneralCK.Certificates.E8TAxisZero0062Root, GeneralCK.Certificates.E8TAxisZero0063Root, GeneralCK.Certificates.E8TAxisZero0064Root, GeneralCK.Certificates.E8TAxisZero0065Root, GeneralCK.Certificates.E8TAxisZero0066Root, GeneralCK.Certificates.E8TAxisZero0067Root, GeneralCK.Certificates.E8TAxisZero0068Root, GeneralCK.Certificates.E8TAxisZero0069Root, GeneralCK.Certificates.E8TAxisZero0070Root, GeneralCK.Certificates.E8TAxisZero0071Root, GeneralCK.Certificates.E8TAxisZero0072Root, GeneralCK.Certificates.E8TAxisZero0073Root, GeneralCK.Certificates.E8TAxisZero0074Root) (piece 11 of 18)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisZero0057Root (+17 modules: GeneralCK.Certificates.E8TAxisZero0058Root, GeneralCK.Certificates.E8TAxisZero0059Root, GeneralCK.Certificates.E8TAxisZero0060Root, GeneralCK.Certificates.E8TAxisZero0061Root, GeneralCK.Certificates.E8TAxisZero0062Root, GeneralCK.Certificates.E8TAxisZero0063Root, GeneralCK.Certificates.E8TAxisZero0064Root, GeneralCK.Certificates.E8TAxisZero0065Root, GeneralCK.Certificates.E8TAxisZero0066Root, GeneralCK.Certificates.E8TAxisZero0067Root, GeneralCK.Certificates.E8TAxisZero0068Root, GeneralCK.Certificates.E8TAxisZero0069Root, GeneralCK.Certificates.E8TAxisZero0070Root, GeneralCK.Certificates.E8TAxisZero0071Root, GeneralCK.Certificates.E8TAxisZero0072Root, GeneralCK.Certificates.E8TAxisZero0073Root, GeneralCK.Certificates.E8TAxisZero0074Root) (piece 11 of 18)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisZero0057Root (+17 modules: GeneralCK.Certificates.E8TAxisZero0058Root, GeneralCK.Certificates.E8TAxisZero0059Root, GeneralCK.Certificates.E8TAxisZero0060Root, GeneralCK.Certificates.E8TAxisZero0061Root, GeneralCK.Certificates.E8TAxisZero0062Root, GeneralCK.Certificates.E8TAxisZero0063Root, GeneralCK.Certificates.E8TAxisZero0064Root, GeneralCK.Certificates.E8TAxisZero0065Root, GeneralCK.Certificates.E8TAxisZero0066Root, GeneralCK.Certificates.E8TAxisZero0067Root, GeneralCK.Certificates.E8TAxisZero0068Root, GeneralCK.Certificates.E8TAxisZero0069Root, GeneralCK.Certificates.E8TAxisZero0070Root, GeneralCK.Certificates.E8TAxisZero0071Root, GeneralCK.Certificates.E8TAxisZero0072Root, GeneralCK.Certificates.E8TAxisZero0073Root, GeneralCK.Certificates.E8TAxisZero0074Root) (piece 11 of 18) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisZero0057Root (+17 modules: GeneralCK/Certificates/E8TAxisZero0058Root, GeneralCK/Certificates/E8TAxisZero0059Root, GeneralCK/Certificates/E8TAxisZero0060Root, GeneralCK/Certificates/E8TAxisZero0061Root, GeneralCK/Certificates/E8TAxisZero0062Root, GeneralCK/Certificates/E8TAxisZero0063Root, GeneralCK/Certificates/E8TAxisZero0064Root, GeneralCK/Certificates/E8TAxisZero0065Root, GeneralCK/Certificates/E8TAxisZero0066Root, GeneralCK/Certificates/E8TAxisZero0067Root, GeneralCK/Certificates/E8TAxisZero0068Root, GeneralCK/Certificates/E8TAxisZero0069Root, GeneralCK/Certificates/E8TAxisZero0070Root, GeneralCK/Certificates/E8TAxisZero0071Root, GeneralCK/Certificates/E8TAxisZero0072Root, GeneralCK/Certificates/E8TAxisZero0073Root, GeneralCK/Certificates/E8TAxisZero0074Root) (piece 11 of 18).lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisZero0057Root__18_q09

-- ===== source module GeneralCK.Certificates.E8TAxisZero0067Root =====
section
namespace GeneralCK.Certificates.E8TAxisZero0067Root
open GeneralCK Set E8TAxisPartitionKernel E8TAxisGeneratedGeometry
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
def rationalRectangle : RatRect := ⟨(325 / 128 : ℚ), (12875000000000000000000000000000000000000000000000000000000637236764453 / 5000000000000000000000000000000000000000000000000000000000000000000000 : ℚ), (0 / 1 : ℚ), (12499999999999999999999999999999999999999999999999999999998630936638871 / 10000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)⟩
theorem historical_index_checked : cells[501]? =
    some rationalRectangle := by decide +kernel
noncomputable def rectangle : Rect :=
  ⟨rationalRectangle.s0, rationalRectangle.s1, rationalRectangle.t0, rationalRectangle.t1⟩

theorem positiveAt {s t : ℝ} (h : rectangle.Covers s t) : 0 < e8RegularDeltaT s t := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [rectangle, rationalRectangle] at hs0 hs1 ht0 ht1
  apply E8TAxisZero0067Certified.positiveAt
  norm_num [E8TAxisZero0067Geometry.rectangle, Rect.Covers, E8TAxisZero0067Geometry.sLower,
    E8TAxisZero0067Geometry.sUpper, E8TAxisZero0067Geometry.tLower, E8TAxisZero0067Geometry.tUpper] at *
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
end GeneralCK.Certificates.E8TAxisZero0067Root

end


