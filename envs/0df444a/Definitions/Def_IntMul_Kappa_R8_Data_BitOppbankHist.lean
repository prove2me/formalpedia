-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankHist
-- name    : IntMul_Kappa_R8_Data_BitOppbankHist
-- status  : Definition
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:32:07.692083+00:00
-- url     : https://prove2.me/theorems/cb4b257b-f0c6-4043-8e59-32b251fdad4d
-- title:
--   R8 opp-bank one-run child-width histogram
-- statement:
--   # Opp-bank bit histogram
--
--   The round-eight opposite-bank one-run compile of Jain's round-seven witness 2 produces a child-width histogram with $46$ bins, multiplicity sum $749446467$, and rank sum $s=55395128481$. This matches the platform constant `Jain.bitR8` and is rebuilt by `independent/round8-oppbank/bit_hist.py` from the frozen schedule.
--
--   Emitted here as an independent schedule-check artifact for the BitNB transplant (not a QHNet pack).
-- source:
--   Jain integer-mult-kappa independent/round8-oppbank/bit_hist.py + certificates/round7 witness 2; matches Prove2me IntMul_KappaJainData.bitR8.

import Mathlib.Data.Nat.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Opp-bank one-run child-width histogram (Jain R8 bit side)

Rebuilt by `independent/round8-oppbank/bit_hist.onerun_hist` from frozen round-seven
witness 2. Multiplicity sum and rank sum are the child counts / rank sum of the
histogram (not the QHNet role count `W`). Target match: platform `Jain.bitR8`.
-/

namespace IntMul.Kappa.R8.Bit.Oppbank

def oppbankHist : List (ℕ × ℕ) :=
  [(1, 221936407), (2, 259926128), (3, 38728228), (4, 49343602), (5, 24609816), (6, 8068676), (7, 3818276), (8, 4785242), (9, 2992990), (10, 1211364), (11, 1445136), (12, 1331792), (13, 1080310), (14, 669438), (15, 2755676), (16, 3860780), (17, 1933932), (18, 364826), (19, 13388760), (20, 587972), (21, 1771000), (22, 116886), (484, 6272882), (506, 59760624), (507, 453376), (508, 173558), (509, 421498), (510, 233772), (511, 205436), (512, 226688), (513, 340032), (514, 602140), (515, 173558), (516, 357742), (517, 283360), (518, 690690), (519, 389620), (520, 102718), (521, 184184), (522, 584430), (523, 350658), (524, 3021326), (525, 13448974), (526, 4558554), (527, 5649490), (528, 6233920)]

def oppbankHist_childCount : ℕ := (oppbankHist.map (·.2)).sum
def oppbankHist_rankSum : ℕ := (oppbankHist.map (fun p => p.1 * p.2)).sum

theorem oppbankHist_childCount_eq : oppbankHist_childCount = 749446467 := by decide
theorem oppbankHist_rankSum_eq : oppbankHist_rankSum = 55395128481 := by decide

end IntMul.Kappa.R8.Bit.Oppbank


