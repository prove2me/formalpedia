-- Prove2me | Definitions.Def_CK_CKLaneA3V_Chain07_q01
-- name    : CK_CKLaneA3V_Chain07_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T10:30:54.985244+00:00
-- url     : https://prove2.me/theorems/20c44b08-6c33-45ab-ad1f-728eb3b7c976
-- title:
--   Courtade–Kumar proof module `CKLaneA3V.Chain07 (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3V.Chain07 (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3V.Chain07 (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3V.Chain07 (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3V/Chain07 (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneA3V_Chain07_q01_q02

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace CKLaneA3V
theorem G_qonep : Good F_qonep D_qonep :=
  (TMd.mul_good G_q G_onep 0 0 14 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).of_eq (by decide +kernel) rfl (by decide +kernel)

noncomputable def F_z : ℝ → ℝ → ℝ := fun t ρ => (((-1 : ℚ) : ℚ) : ℝ) * F_qonep t ρ
noncomputable def D_z : TMd := ⟨[[(0, [(0, ((-1 : ℚ) / 4))])],
  [],
  [(0, [(-1, ((-1 : ℚ) / 4)), (0, (1 : ℚ))]), (1, [(-1, ((-1 : ℚ) / 2))])],
  [],
  [(0, [(-2, ((-5 : ℚ) / 16)), (-1, ((2 : ℚ) / 3))]), (1, [(-2, ((-3 : ℚ) / 8)), (-1, ((4 : ℚ) / 3))]), (2, [(-2, ((1 : ℚ) / 4))]), (3, [(-2, ((-1 : ℚ) / 2))])],
  [],
  [(0, [(-3, ((-25 : ℚ) / 64)), (-2, ((21 : ℚ) / 32)), (-1, ((8 : ℚ) / 15))]), (1, [(-3, ((-5 : ℚ) / 32)), (-2, ((35 : ℚ) / 48)), (-1, ((16 : ℚ) / 15))]), (2, [(-3, ((3 : ℚ) / 8)), (-2, ((-3 : ℚ) / 4))]), (3, [(-3, ((-5 : ℚ) / 4)), (-2, ((7 : ℚ) / 6))]), (4, [(-3, ((3 : ℚ) / 4)), (-2, ((1 : ℚ) / 2))]), (5, [(-3, ((-1 : ℚ) / 2)), (-2, ((-1 : ℚ) / 3))])],
  [],
  [(0, [(-4, ((-125 : ℚ) / 256)), (-3, ((115 : ℚ) / 192)), (-2, ((125 : ℚ) / 144)), (-1, ((32 : ℚ) / 35))]), (1, [(-4, ((25 : ℚ) / 128)), (-3, ((3 : ℚ) / 32)), (-2, ((371 : ℚ) / 360)), (-1, ((64 : ℚ) / 35))]), (2, [(-4, ((15 : ℚ) / 64)), (-3, ((-49 : ℚ) / 48)), (-2, ((-83 : ℚ) / 180))]), (3, [(-4, ((-67 : ℚ) / 32)), (-3, ((61 : ℚ) / 24)), (-2, ((151 : ℚ) / 90))]), (4, [(-4, ((41 : ℚ) / 16)), (-3, ((-7 : ℚ) / 12)), (-2, (-1 : ℚ))]), (5, [(-4, ((-21 : ℚ) / 8)), (-3, ((-5 : ℚ) / 6)), (-2, ((-14 : ℚ) / 45))]), (6, [(-4, ((5 : ℚ) / 4)), (-3, ((5 : ℚ) / 3)), (-2, ((4 : ℚ) / 3))]), (7, [(-4, ((-1 : ℚ) / 2)), (-3, ((-2 : ℚ) / 3)), (-2, ((-8 : ℚ) / 15))])],
  [],
  [(0, [(-5, ((-625 : ℚ) / 1024)), (-4, ((725 : ℚ) / 1536)), (-3, ((2791 : ℚ) / 2304)), (-2, ((3739 : ℚ) / 2240)), (-1, ((128 : ℚ) / 63))]), (1, [(-5, ((375 : ℚ) / 512)), (-4, ((-355 : ℚ) / 768)), (-3, ((431 : ℚ) / 1152)), (-2, ((21659 : ℚ) / 10080)), (-1, ((256 : ℚ) / 63))]), (2, [(-5, ((-25 : ℚ) / 64)), (-4, ((-27 : ℚ) / 32)), (-3, ((-593 : ℚ) / 720)), (-2, ((-649 : ℚ) / 1260))]), (3, [(-5, ((-85 : ℚ) / 32)), (-4, ((175 : ℚ) / 48)), (-3, ((1579 : ℚ) / 360)), (-2, ((1411 : ℚ) / 630))]), (4, [(-5, ((177 : ℚ) / 32)), (-4, ((-145 : ℚ) / 48)), (-3, ((-553 : ℚ) / 120)), (-2, ((-221 : ℚ) / 90))]), (5, [(-5, ((-127 : ℚ) / 16)), (-4, ((-3 : ℚ) / 8)), (-3, ((517 : ℚ) / 180)), (-2, ((131 : ℚ) / 45))]), (6, [(-5, ((27 : ℚ) / 4)), (-4, ((31 : ℚ) / 6)), (-3, ((41 : ℚ) / 15)), (-2, ((4 : ℚ) / 9))]), (7, [(-5, ((-9 : ℚ) / 2)), (-4, ((-17 : ℚ) / 3)), (-3, ((-86 : ℚ) / 15)), (-2, ((-1352 : ℚ) / 315))]), (8, [(-5, ((7 : ℚ) / 4)), (-4, ((7 : ℚ) / 2)), (-3, ((203 : ℚ) / 45)), (-2, (4 : ℚ))]), (9, [(-5, ((-1 : ℚ) / 2)), (-4, (-1 : ℚ)), (-3, ((-58 : ℚ) / 45)), (-2, ((-8 : ℚ) / 7))])],
  [],
  [(0, [(-6, ((-3125 : ℚ) / 4096)), (-5, ((125 : ℚ) / 512)), (-4, ((4655 : ℚ) / 3072)), (-3, ((65203 : ℚ) / 24192)), (-2, ((19511 : ℚ) / 5040)), (-1, ((512 : ℚ) / 99))]), (1, [(-6, ((3125 : ℚ) / 2048)), (-5, ((-575 : ℚ) / 768)), (-4, ((-1487 : ℚ) / 1536)), (-3, ((8737 : ℚ) / 6720)), (-2, ((65921 : ℚ) / 12600)), (-1, ((1024 : ℚ) / 99))]), (2, [(-6, ((-1875 : ℚ) / 1024)), (-5, ((-65 : ℚ) / 128)), (-4, ((-77 : ℚ) / 256)), (-3, ((-3067 : ℚ) / 3360)), (-2, ((-2363 : ℚ) / 2100))]), (3, [(-6, ((-1125 : ℚ) / 512)), (-5, ((811 : ℚ) / 192)), (-4, ((14539 : ℚ) / 1920)), (-3, ((11363 : ℚ) / 1680)), (-2, ((481 : ℚ) / 126))]), (4, [(-6, ((1175 : ℚ) / 128)), (-5, ((-293 : ℚ) / 48)), (-4, ((-6089 : ℚ) / 480)), (-3, ((-5083 : ℚ) / 540)), (-2, ((-202 : ℚ) / 63))]), (5, [(-6, ((-1159 : ℚ) / 64)), (-5, ((29 : ℚ) / 24)), (-4, ((1107 : ℚ) / 80)), (-3, ((27781 : ℚ) / 1890)), (-2, ((4364 : ℚ) / 525))]), (6, [(-6, ((701 : ℚ) / 32)), (-5, ((133 : ℚ) / 12)), (-4, ((-179 : ℚ) / 120)), (-3, ((-1213 : ℚ) / 135)), (-2, ((-88 : ℚ) / 9))]), (7, [(-6, ((-325 : ℚ) / 16)), (-5, ((-125 : ℚ) / 6)), (-4, ((-917 : ℚ) / 60)), (-3, ((-1426 : ℚ) / 189)), (-2, ((592 : ℚ) / 1575))]), (8, [(-6, ((215 : ℚ) / 16)), (-5, ((131 : ℚ) / 6)), (-4, ((509 : ℚ) / 20)), (-3, ((22742 : ℚ) / 945)), (-2, (16 : ℚ))]), (9, [(-6, ((-55 : ℚ) / 8)), (-5, ((-43 : ℚ) / 3)), (-4, ((-631 : ℚ) / 30)), (-3, ((-23692 : ℚ) / 945)), (-2, ((-1376 : ℚ) / 63))]), (10, [(-6, ((9 : ℚ) / 4)), (-5, (6 : ℚ)), (-4, ((51 : ℚ) / 5)), (-3, ((472 : ℚ) / 35)), (-2, ((64 : ℚ) / 5))]), (11, [(-6, ((-1 : ℚ) / 2)), (-5, ((-4 : ℚ) / 3)), (-4, ((-34 : ℚ) / 15)), (-3, ((-944 : ℚ) / 315)), (-2, ((-128 : ℚ) / 45))])],
  []],
  ((6368189100391253 : ℚ) / 1099511627776), 14⟩
end CKLaneA3V


