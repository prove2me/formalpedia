-- Prove2me | Definitions.Def_CK_CKLaneA3V_Chain07_q01_q01
-- name    : CK_CKLaneA3V_Chain07_q01_q01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T10:13:04.419729+00:00
-- url     : https://prove2.me/theorems/3aecdf95-95f5-4527-a081-0670199e77e5
-- title:
--   Courtade–Kumar proof module `CKLaneA3V.Chain07 (piece 2 of 4) (piece 2 of 4)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneA3V.Chain07 (piece 2 of 4) (piece 2 of 4)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneA3V.Chain07 (piece 2 of 4) (piece 2 of 4)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneA3V.Chain07 (piece 2 of 4) (piece 2 of 4) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3V/Chain07 (piece 2 of 4) (piece 2 of 4).lean)

import Definitions.Def_CK_CKLaneA3V_Chain07_q01_q00

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
namespace CKLaneA3V
theorem G_dJ : Good F_dJ D_dJ :=
  (TMd.mul_good G_d G_J 1 1 14 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).of_eq (by decide +kernel) rfl (by decide +kernel)

noncomputable def F_dJSi : ℝ → ℝ → ℝ := fun t ρ => F_dJ t ρ * F_Si t ρ
noncomputable def D_dJSi : TMd := ⟨[[],
  [],
  [(0, [(-1, (1 : ℚ))]), (1, [(-1, (2 : ℚ))])],
  [],
  [(0, [(-2, ((5 : ℚ) / 4)), (-1, ((4 : ℚ) / 3))]), (1, [(-2, ((3 : ℚ) / 2)), (-1, ((8 : ℚ) / 3))]), (2, [(-2, (-1 : ℚ))]), (3, [(-2, (2 : ℚ))])],
  [],
  [(0, [(-3, ((25 : ℚ) / 16)), (-2, ((19 : ℚ) / 8)), (-1, ((16 : ℚ) / 5))]), (1, [(-3, ((5 : ℚ) / 8)), (-2, ((37 : ℚ) / 12)), (-1, ((32 : ℚ) / 5))]), (2, [(-3, ((-3 : ℚ) / 2)), (-2, (-1 : ℚ))]), (3, [(-3, (5 : ℚ)), (-2, ((10 : ℚ) / 3))]), (4, [(-3, (-3 : ℚ)), (-2, (-2 : ℚ))]), (5, [(-3, (2 : ℚ)), (-2, ((4 : ℚ) / 3))])],
  [],
  [(0, [(-4, ((125 : ℚ) / 64)), (-3, ((185 : ℚ) / 48)), (-2, ((217 : ℚ) / 36)), (-1, ((64 : ℚ) / 7))]), (1, [(-4, ((-25 : ℚ) / 32)), (-3, ((17 : ℚ) / 8)), (-2, ((739 : ℚ) / 90)), (-1, ((128 : ℚ) / 7))]), (2, [(-4, ((-15 : ℚ) / 16)), (-3, ((-23 : ℚ) / 12)), (-2, ((-97 : ℚ) / 45))]), (3, [(-4, ((67 : ℚ) / 8)), (-3, ((59 : ℚ) / 6)), (-2, ((298 : ℚ) / 45))]), (4, [(-4, ((-41 : ℚ) / 4)), (-3, ((-29 : ℚ) / 3)), (-2, (-4 : ℚ))]), (5, [(-4, ((21 : ℚ) / 2)), (-3, ((34 : ℚ) / 3)), (-2, ((296 : ℚ) / 45))]), (6, [(-4, (-5 : ℚ)), (-3, ((-20 : ℚ) / 3)), (-2, ((-16 : ℚ) / 3))]), (7, [(-4, (2 : ℚ)), (-3, ((8 : ℚ) / 3)), (-2, ((32 : ℚ) / 15))])],
  [],
  [(0, [(-5, ((625 : ℚ) / 256)), (-4, ((2275 : ℚ) / 384)), (-3, ((6089 : ℚ) / 576)), (-2, ((87869 : ℚ) / 5040)), (-1, ((256 : ℚ) / 9))]), (1, [(-5, ((-375 : ℚ) / 128)), (-4, ((-245 : ℚ) / 192)), (-3, ((2017 : ℚ) / 288)), (-2, ((61109 : ℚ) / 2520)), (-1, ((512 : ℚ) / 9))]), (2, [(-5, ((25 : ℚ) / 16)), (-4, ((-3 : ℚ) / 8)), (-3, ((-787 : ℚ) / 180)), (-2, ((-689 : ℚ) / 105))]), (3, [(-5, ((85 : ℚ) / 8)), (-4, ((227 : ℚ) / 12)), (-3, ((1961 : ℚ) / 90)), (-2, ((5522 : ℚ) / 315))]), (4, [(-5, ((-177 : ℚ) / 8)), (-4, ((-347 : ℚ) / 12)), (-3, ((-607 : ℚ) / 30)), (-2, ((-278 : ℚ) / 45))]), (5, [(-5, ((127 : ℚ) / 4)), (-4, ((87 : ℚ) / 2)), (-3, ((1523 : ℚ) / 45)), (-2, ((44 : ℚ) / 3))]), (6, [(-5, (-27 : ℚ)), (-4, ((-122 : ℚ) / 3)), (-3, ((-188 : ℚ) / 5)), (-2, ((-208 : ℚ) / 9))]), (7, [(-5, (18 : ℚ)), (-4, ((92 : ℚ) / 3)), (-3, ((168 : ℚ) / 5)), (-2, ((8096 : ℚ) / 315))]), (8, [(-5, (-7 : ℚ)), (-4, (-14 : ℚ)), (-3, ((-812 : ℚ) / 45)), (-2, (-16 : ℚ))]), (9, [(-5, (2 : ℚ)), (-4, (4 : ℚ)), (-3, ((232 : ℚ) / 45)), (-2, ((32 : ℚ) / 7))])],
  [],
  [(0, [(-6, ((3125 : ℚ) / 1024)), (-5, ((1125 : ℚ) / 128)), (-4, ((4515 : ℚ) / 256)), (-3, ((190535 : ℚ) / 6048)), (-2, ((11393 : ℚ) / 210)), (-1, ((1024 : ℚ) / 11))]), (1, [(-6, ((-3125 : ℚ) / 512)), (-5, ((-1675 : ℚ) / 192)), (-4, ((-473 : ℚ) / 384)), (-3, ((114979 : ℚ) / 5040)), (-2, ((17116 : ℚ) / 225)), (-1, ((2048 : ℚ) / 11))]), (2, [(-6, ((1875 : ℚ) / 256)), (-5, ((265 : ℚ) / 32)), (-4, ((-19 : ℚ) / 64)), (-3, ((-34871 : ℚ) / 2520)), (-2, ((-1631 : ℚ) / 75))]), (3, [(-6, ((1125 : ℚ) / 128)), (-5, ((1229 : ℚ) / 48)), (-4, ((21781 : ℚ) / 480)), (-3, ((75727 : ℚ) / 1260)), (-2, ((17278 : ℚ) / 315))]), (4, [(-6, ((-1175 : ℚ) / 32)), (-5, ((-769 : ℚ) / 12)), (-4, ((-2597 : ℚ) / 40)), (-3, ((-5843 : ℚ) / 135)), (-2, ((-416 : ℚ) / 35))]), (5, [(-6, ((1159 : ℚ) / 16)), (-5, ((733 : ℚ) / 6)), (-4, ((2373 : ℚ) / 20)), (-3, ((14474 : ℚ) / 189)), (-2, ((4448 : ℚ) / 175))]), (6, [(-6, ((-701 : ℚ) / 8)), (-5, ((-457 : ℚ) / 3)), (-4, ((-1567 : ℚ) / 10)), (-3, ((-15452 : ℚ) / 135)), (-2, ((-160 : ℚ) / 3))]), (7, [(-6, ((325 : ℚ) / 4)), (-5, ((466 : ℚ) / 3)), (-4, ((919 : ℚ) / 5)), (-3, ((155528 : ℚ) / 945)), (-2, ((17728 : ℚ) / 175))]), (8, [(-6, ((-215 : ℚ) / 4)), (-5, ((-346 : ℚ) / 3)), (-4, ((-789 : ℚ) / 5)), (-3, ((-159176 : ℚ) / 945)), (-2, (-128 : ℚ))]), (9, [(-6, ((55 : ℚ) / 2)), (-5, ((196 : ℚ) / 3)), (-4, ((1502 : ℚ) / 15)), (-3, ((114256 : ℚ) / 945)), (-2, ((6656 : ℚ) / 63))]), (10, [(-6, (-9 : ℚ)), (-5, (-24 : ℚ)), (-4, ((-204 : ℚ) / 5)), (-3, ((-1888 : ℚ) / 35)), (-2, ((-256 : ℚ) / 5))]), (11, [(-6, (2 : ℚ)), (-5, ((16 : ℚ) / 3)), (-4, ((136 : ℚ) / 15)), (-3, ((3776 : ℚ) / 315)), (-2, ((512 : ℚ) / 45))])],
  []],
  ((18106465351023807 : ℚ) / 1099511627776), 14⟩
end CKLaneA3V


