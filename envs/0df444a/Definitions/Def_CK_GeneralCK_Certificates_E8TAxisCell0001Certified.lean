-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCell0001Certified
-- name    : CK_GeneralCK_Certificates_E8TAxisCell0001Certified
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T01:59:41.663703+00:00
-- url     : https://prove2.me/theorems/2b3eaa38-acd8-4f67-8b19-9207c0dbb84c
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisCell0001Certified` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisCell0001Certified` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisCell0001Certified` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisCell0001Certified (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisCell0001Certified.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCell0001Sub0Certified
import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCell0001Sub1Certified

-- ===== source module GeneralCK.Certificates.E8TAxisCell0001Certified =====
section

/-! The weak second positive historical t-axis rectangle, certified after one
exact midpoint refinement in the s direction. -/

namespace GeneralCK.Certificates.E8TAxisCell0001Certified

open E8TAxisPartitionKernel

noncomputable def rectangle : Rect :=
  { s0 := 3 / 50
    s1 := E8TAxisOneCellGeometry.sLower
    t0 := E8TAxisOneCellGeometry.tLower
    t1 := 1 / 50 }

def split : ℚ :=
  25500000000000000000000000000000000000000000000000000000000637236764453 /
    400000000000000000000000000000000000000000000000000000000000000000000000

def tree : Tree := .splitS split .leaf .leaf

theorem allLeaves : AllLeaves CellPositive tree rectangle := by
  refine ⟨by norm_num [rectangle, split, E8TAxisOneCellGeometry.sLower],
    by norm_num [rectangle, split, E8TAxisOneCellGeometry.sLower], ?_, ?_⟩
  · change CellPositive (rectangle.leftS split)
    simpa [rectangle, split, Rect.leftS,
      E8TAxisCell0001Sub0Geometry.rectangle,
      E8TAxisCell0001Sub0Geometry.sLower, E8TAxisCell0001Sub0Geometry.sUpper,
      E8TAxisCell0001Sub0Geometry.tLower, E8TAxisCell0001Sub0Geometry.tUpper,
      E8TAxisOneCellGeometry.sLower, E8TAxisOneCellGeometry.tLower] using
      E8TAxisCell0001Sub0Certified.cellPositive
  · change CellPositive (rectangle.rightS split)
    simpa [rectangle, split, Rect.rightS,
      E8TAxisCell0001Sub1Geometry.rectangle,
      E8TAxisCell0001Sub1Geometry.sLower, E8TAxisCell0001Sub1Geometry.sUpper,
      E8TAxisCell0001Sub1Geometry.tLower, E8TAxisCell0001Sub1Geometry.tUpper,
      E8TAxisOneCellGeometry.sLower, E8TAxisOneCellGeometry.tLower] using
      E8TAxisCell0001Sub1Certified.cellPositive

theorem cellPositive : CellPositive rectangle := by
  intro s t hadm h
  obtain ⟨leaf, hp, hc⟩ := locate_leaf allLeaves h
  exact hp s t hadm hc

#print axioms allLeaves
#print axioms cellPositive

end GeneralCK.Certificates.E8TAxisCell0001Certified

end


