-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_E8TAxisOneCellArithmetic
-- name    : CK_GeneralCK_Certificates_E8TAxisOneCellArithmetic
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T09:59:36.984729+00:00
-- url     : https://prove2.me/theorems/d5245272-b74a-41d4-8261-48ca6517f94d
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.E8TAxisOneCellArithmetic` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.E8TAxisOneCellArithmetic` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.E8TAxisOneCellArithmetic` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.E8TAxisOneCellArithmetic (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisOneCellArithmetic.lean)

import Definitions.Def_CK_GeneralCK_Certificates_E8TAxisDyadicJetKernel
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface

-- ===== source module GeneralCK.Certificates.E8TAxisOneCellArithmetic =====
section

/-! Exact dyadic replay of the centered arithmetic for the first bridge leaf.

The derivative intervals in this file are the outputs of the traced BJ5
evaluation.  This module checks every subsequent multiplication, division,
addition, and the final strict positivity.  A separate semantic theorem must
still prove that those derivative boxes contain the concrete E8 derivatives.
-/

namespace GeneralCK.Certificates.E8TAxisOneCellArithmetic

open DyadicInterval



def powI (a : DyadicInterval precision) : ℕ → DyadicInterval precision
  | 0 => ofInt precision 1
  | n + 1 => (powI a n).mul a

def divNat (a : DyadicInterval precision) (n : ℕ) : DyadicInterval precision :=
  a.mul (ofInt precision n).recip



def initial : DyadicInterval precision := ⟨96479987514856367516858255125746966456, 96479987514856367516858255125746966457⟩
def der_0_2 : DyadicInterval precision := ⟨4519210457057521137229765141354245421005, 4519210457057521137229765141354245421006⟩
def term_00 : DyadicInterval precision :=
  divNat ((der_0_2.mul (powI ds 0)).mul (powI dt 1)) 1
def der_1_1 : DyadicInterval precision := ⟨5825744588294595774549217804696951856591, 5825744588294595774549217804696951856592⟩
def term_01 : DyadicInterval precision :=
  divNat ((der_1_1.mul (powI ds 1)).mul (powI dt 0)) 1
def der_0_3 : DyadicInterval precision := ⟨118582717436939698908153654196102423982377, 118582717436939698908153654196102423982378⟩
def term_02 : DyadicInterval precision :=
  divNat ((der_0_3.mul (powI ds 0)).mul (powI dt 2)) 2
def der_1_2 : DyadicInterval precision := ⟨229186523496188191082139692016834927154521, 229186523496188191082139692016834927154522⟩
def term_03 : DyadicInterval precision :=
  divNat ((der_1_2.mul (powI ds 1)).mul (powI dt 1)) 1
def der_2_1 : DyadicInterval precision := ⟨279368631586065225204327724264734615978079, 279368631586065225204327724264734615978080⟩
def term_04 : DyadicInterval precision :=
  divNat ((der_2_1.mul (powI ds 2)).mul (powI dt 0)) 2
def der_0_4 : DyadicInterval precision := ⟨1392332258135485598173151523474367399572789, 1392332258135485598173151523474367399572790⟩
def term_05 : DyadicInterval precision :=
  divNat ((der_0_4.mul (powI ds 0)).mul (powI dt 3)) 6
def der_1_3 : DyadicInterval precision := ⟨4720977068780883704213191717654544051284798, 4720977068780883704213191717654544051284799⟩
def term_06 : DyadicInterval precision :=
  divNat ((der_1_3.mul (powI ds 1)).mul (powI dt 2)) 2
def der_2_2 : DyadicInterval precision := ⟨8688810967106778156071161810398760156686530, 8688810967106778156071161810398760156686531⟩
def term_07 : DyadicInterval precision :=
  divNat ((der_2_2.mul (powI ds 2)).mul (powI dt 1)) 2
def der_3_1 : DyadicInterval precision := ⟨9973899596571059047491509856339808284992519, 9973899596571059047491509856339808284992520⟩
def term_08 : DyadicInterval precision :=
  divNat ((der_3_1.mul (powI ds 3)).mul (powI dt 0)) 6
def der_0_5 : DyadicInterval precision := ⟨-39650124131037391327253355385768318930600639515, 39504181119357617933921129666349342106993765452⟩
def term_09 : DyadicInterval precision :=
  divNat ((der_0_5.mul (powI ds 0)).mul (powI dt 4)) 24
def der_1_4 : DyadicInterval precision := ⟨-51711515788143094325076437455461675942582110669, 51346357371845229472204442517632425325292215690⟩
def term_10 : DyadicInterval precision :=
  divNat ((der_1_4.mul (powI ds 1)).mul (powI dt 3)) 6
def der_2_3 : DyadicInterval precision := ⟨-79573223867531099897250579537987000980859222779, 79083629626869876958952174899665922714119802515⟩
def term_11 : DyadicInterval precision :=
  divNat ((der_2_3.mul (powI ds 2)).mul (powI dt 2)) 4
def der_3_2 : DyadicInterval precision := ⟨-137802679877904028449942018430273307142661469485, 137245720291106155681741642122116246242621641305⟩
def term_12 : DyadicInterval precision :=
  divNat ((der_3_2.mul (powI ds 3)).mul (powI dt 1)) 6
def der_4_1 : DyadicInterval precision := ⟨-253355451538131606042877647628360560486872739056, 253203448681657190933886061677592959756989445893⟩
def term_13 : DyadicInterval precision :=
  divNat ((der_4_1.mul (powI ds 4)).mul (powI dt 0)) 24

def centeredReplay : DyadicInterval precision :=
  ((((((((((((((initial.add term_00).add term_01).add term_02).add term_03).add term_04).add term_05).add term_06).add term_07).add term_08).add term_09).add term_10).add term_11).add term_12).add term_13)

theorem centeredReplay_positive : centeredReplay.positiveCheck = true := by decide

#print axioms centeredReplay_positive

end GeneralCK.Certificates.E8TAxisOneCellArithmetic

end


