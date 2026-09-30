-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCell0001Sub1Geometry
-- name    : CK_GeneralCK_Certificates_E8TAxisCell0001Sub1Geometry
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T10:08:09.948792+00:00
-- url     : https://prove2.me/theorems/88983b18-216d-4c43-bd3c-0494dfdc3411
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisCell0001Sub1Geometry` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisCell0001Sub1Geometry` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisCell0001Sub1Geometry` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisCell0001Sub1Geometry (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisCell0001Sub1Geometry.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisCellCertificateSchema

-- ===== source module GeneralCK.Certificates.E8TAxisCell0001Sub1Geometry =====
section

namespace GeneralCK.Certificates.E8TAxisCell0001Sub1Geometry
open GeneralCK Set DyadicInterval E8TAxisPartitionKernel

noncomputable def sLower : ℝ := (25500000000000000000000000000000000000000000000000000000000637236764453 / 400000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def sUpper : ℝ := (13500000000000000000000000000000000000000000000000000000000637236764453 / 200000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tLower : ℝ := (24999999999999999999999999999999999999999999999999999999997261873277741 / 2500000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def tUpper : ℝ := (1 / 50 : ℝ)
noncomputable def centerS : ℝ := (52500000000000000000000000000000000000000000000000000000001911710293359 / 800000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
noncomputable def centerT : ℝ := (74999999999999999999999999999999999999999999999999999999997261873277741 / 5000000000000000000000000000000000000000000000000000000000000000000000000 : ℝ)
def ds : DyadicInterval 160 := ⟨-2740315569995442971631909061343030661854873519, 2740315569995442971631909061343030661854873519⟩
def dt : DyadicInterval 160 := ⟨-7307508186654514591018424163581415098279662715, 7307508186654514591018424163581415098279662715⟩
def InCell (s t : ℝ) : Prop :=
  sLower ≤ s ∧ s ≤ sUpper ∧ tLower ≤ t ∧ t ≤ tUpper
noncomputable def rectangle : Rect := ⟨sLower, sUpper, tLower, tUpper⟩

theorem center_mem : InCell centerS centerT := by
  norm_num [InCell, sLower, sUpper, tLower, tUpper, centerS, centerT]

theorem displacement_mem {s t : ℝ} (h : InCell s t) :
    ds.Contains (s - centerS) ∧ dt.Contains (t - centerT) := by
  rcases h with ⟨hs0, hs1, ht0, ht1⟩
  norm_num [sLower, sUpper, tLower, tUpper] at hs0 hs1 ht0 ht1
  norm_num [Contains, ds, dt, centerS, centerT, scale]
  constructor <;> constructor <;> linarith

theorem inputsInRange_of_cell {s t : ℝ} (h : InCell s t) :
    E8TAxisDeltaDirectionalJet.InputsInRange s t := by
  have hs : 0 < s := lt_of_lt_of_le (by norm_num [sLower]) h.1
  have ht : 0 < t := lt_of_lt_of_le (by norm_num [tLower]) h.2.2.1
  have hB : 2 * s + t ≤ 17 / 100 := by
    rcases h with ⟨_, hs1, _, ht1⟩
    norm_num [sUpper, tUpper] at hs1 ht1 ⊢
    linarith
  exact ⟨e8SlopeRange_downward E8TAxisOneCellGeometry.upperSlope_mem ht (by linarith),
    e8SlopeRange_downward E8TAxisOneCellGeometry.upperSlope_mem (by positivity) hB,
    e8SlopeRange_downward E8TAxisOneCellGeometry.upperSlope_mem (by positivity) (by linarith),
    e8SlopeRange_downward E8TAxisOneCellGeometry.upperSlope_mem hs (by linarith)⟩

end GeneralCK.Certificates.E8TAxisCell0001Sub1Geometry

end


