-- Prove2me | Definitions.Def_StableVotingDistortion_Lemma9IntervalArithmetic
-- name    : StableVotingDistortion_Lemma9IntervalArithmetic
-- status  : Definition
-- author  : @a142857a
-- created : 2026-11-14T18:07:47.934673+00:00
-- url     : https://prove2.me/theorems/4d3fb655-ceb6-4f43-981e-95c6b6adbd2b
-- title:
--   Rational interval checker for the published voting residuals
-- statement:
--   Rational interval checker for the published voting residuals.
-- source:
--   STOC submission, Section 6, Lemma 9, original released certificate, SHA-256 6a04e0dafad717b2cb646d23a8faca4a7ba7930aba032af6dc6724427b9006e7.

import Definitions.Def_StableVotingDistortion_Lemma9ReleasedData

namespace StableVotingDistortion.PaperBox
open Set MeasureTheory
noncomputable section
set_option maxRecDepth 100000
structure Bounds where
  lo : ℚ
  hi : ℚ
deriving DecidableEq, Repr
namespace Bounds
def point (q : ℚ) : Bounds := ⟨q,q⟩
def plus (i j : Bounds) : Bounds := ⟨i.lo+j.lo,i.hi+j.hi⟩
def neg (i : Bounds) : Bounds := ⟨-i.hi,-i.lo⟩
def minus (i j : Bounds) : Bounds := i.plus j.neg
def times (i j : Bounds) : Bounds :=
  ⟨min (min (i.lo*j.lo) (i.hi*j.lo)) (min (i.lo*j.hi) (i.hi*j.hi)),
   max (max (i.lo*j.lo) (i.hi*j.lo)) (max (i.lo*j.hi) (i.hi*j.hi))⟩
def posPart (i : Bounds) : Bounds := ⟨max i.lo 0,max i.hi 0⟩
end Bounds
end
end StableVotingDistortion.PaperBox

namespace StableVotingDistortion.PaperBox
open Set MeasureTheory
open StableVotingDistortion.PaperBox
open StableVotingDistortion.PaperBox.Bounds
noncomputable section
set_option maxRecDepth 100000
def decreasingRange (atPoint : ℚ → Bounds) (i : Bounds) : Bounds :=
  ⟨(atPoint i.hi).lo,(atPoint i.lo).hi⟩
def unimodalRange (atPoint : ℚ → Bounds) (t : ℚ) (i : Bounds) : Bounds :=
  if i.hi ≤ t then ⟨(atPoint i.lo).lo,(atPoint i.hi).hi⟩
  else if t ≤ i.lo then decreasingRange atPoint i
  else ⟨min (atPoint i.lo).lo (atPoint i.hi).lo,(atPoint t).hi⟩
end
end StableVotingDistortion.PaperBox

namespace StableVotingDistortion.PaperBox
open Set MeasureTheory
open StableVotingDistortion.PaperBox
open StableVotingDistortion.PaperBox.Bounds
noncomputable section
set_option maxRecDepth 100000
abbrev Box (d : ℕ) := Fin d → Bounds
inductive Cover (d : ℕ) where
  | leaf
  | split (axis : Fin d) (cut : ℚ) (left right : Cover d)
def lowerBox {d : ℕ} (b : Box d) (j : Fin d) (c : ℚ) : Box d :=
  Function.update b j ⟨(b j).lo,c⟩
def upperBox {d : ℕ} (b : Box d) (j : Fin d) (c : ℚ) : Box d :=
  Function.update b j ⟨c,(b j).hi⟩
def Cover.verify {d : ℕ} (ok : Box d → Bool) (b : Box d) : Cover d → Bool
  | .leaf => ok b
  | .split j c l r => l.verify ok (lowerBox b j c) && r.verify ok (upperBox b j c)
end
end StableVotingDistortion.PaperBox

namespace StableVotingDistortion.PaperCurve
open Set MeasureTheory
open StableVotingDistortion.PaperBox
open StableVotingDistortion.PaperBox.Bounds
noncomputable section
set_option maxRecDepth 100000
def qclamp (x : ℚ) : ℚ := max 0 (min 1 x)
def clampBox (i : Bounds) : Bounds := ⟨qclamp i.lo,qclamp i.hi⟩
def clampSlopeBox (i : Bounds) : Bounds :=
  if 0 ≤ i.lo ∧ i.hi ≤ 1 then point 1 else if i.hi ≤ 0 ∨ 1 ≤ i.lo then point 0 else ⟨0,1⟩
end
end StableVotingDistortion.PaperCurve

namespace StableVotingDistortion.PaperBox
open Set MeasureTheory
open StableVotingDistortion.PaperBox
open StableVotingDistortion.PaperBox.Bounds
noncomputable section
set_option maxRecDepth 100000
def clipSlope (i : Bounds) : Bounds :=
  if i.hi≤0 then point 0 else if 0 ≤ i.lo then point 1 else ⟨0,1⟩
end
end StableVotingDistortion.PaperBox

namespace StableVotingDistortion.PaperBox
open Set MeasureTheory
open StableVotingDistortion.PaperBox
open StableVotingDistortion.PaperBox.Bounds
noncomputable section
set_option maxRecDepth 100000
def midpoint (b : Bounds) : ℚ := (b.lo+b.hi)/2
def radius (b : Bounds) : ℚ := (b.hi-b.lo)/2
end
end StableVotingDistortion.PaperBox

namespace StableVotingDistortion.PaperCurve
open Set MeasureTheory
open StableVotingDistortion.PaperBox
open StableVotingDistortion.PaperBox.Bounds
open StableVotingDistortion.PaperCurve
noncomputable section
set_option maxRecDepth 100000
def anchor (b s : Bounds) : ℚ :=
  if 0 ≤ s.lo then b.hi else if s.hi ≤ 0 then b.lo else midpoint b
def deviation (b s : Bounds) : ℚ :=
  if 0 ≤ s.lo ∨ s.hi ≤ 0 then 0 else radius b * max (-s.lo) s.hi
end
end StableVotingDistortion.PaperCurve

namespace StableVotingDistortion.PaperCurve
open Set MeasureTheory
open StableVotingDistortion.PaperBox
open StableVotingDistortion.PaperBox.Bounds
noncomputable section
set_option maxRecDepth 100000
inductive RowTree
  | leaf (p : Piece)
  | branch (pivot : ℚ) (left right : RowTree)
def RowTree.lookup (x : ℚ) : RowTree → Piece
  | .leaf p => p
  | .branch t l r => if x≤t then l.lookup x else r.lookup x
end
end StableVotingDistortion.PaperCurve

namespace StableVotingDistortion.PaperCurve
open Set MeasureTheory
open StableVotingDistortion.PaperBox
open StableVotingDistortion.PaperBox.Bounds
noncomputable section
set_option maxRecDepth 100000
def node_0_1 : RowTree := .leaf (rows00[0]!)
def node_1_2 : RowTree := .leaf (rows00[1]!)
def node_2_3 : RowTree := .leaf (rows00[2]!)
def node_1_3 : RowTree := .branch (590187/2000000) node_1_2 node_2_3
def node_0_3 : RowTree := .branch (527/2000) node_0_1 node_1_3
def node_3_4 : RowTree := .leaf (rows00[3]!)
def node_4_5 : RowTree := .leaf (rows00[4]!)
def node_5_6 : RowTree := .leaf (rows00[5]!)
def node_4_6 : RowTree := .branch (325331667/1100000000) node_4_5 node_5_6
def node_3_6 : RowTree := .branch (40636091/137500000) node_3_4 node_4_6
def node_0_6 : RowTree := .branch (324845789/1100000000) node_0_3 node_3_6
def node_6_7 : RowTree := .leaf (rows00[6]!)
def node_7_8 : RowTree := .leaf (rows00[7]!)
def node_8_9 : RowTree := .leaf (rows01[0]!)
def node_7_9 : RowTree := .branch (81515121/275000000) node_7_8 node_8_9
def node_6_9 : RowTree := .branch (65163509/220000000) node_6_7 node_7_9
def node_9_10 : RowTree := .leaf (rows01[1]!)
def node_10_11 : RowTree := .leaf (rows01[2]!)
def node_11_12 : RowTree := .leaf (rows01[3]!)
def node_10_12 : RowTree := .branch (326789301/1100000000) node_10_11 node_11_12
def node_9_12 : RowTree := .branch (163273181/550000000) node_9_10 node_10_12
def node_6_12 : RowTree := .branch (326303423/1100000000) node_6_9 node_9_12
def node_0_12 : RowTree := .branch (162787303/550000000) node_0_6 node_6_12
def node_12_13 : RowTree := .leaf (rows01[4]!)
def node_13_14 : RowTree := .leaf (rows01[5]!)
def node_14_15 : RowTree := .leaf (rows01[6]!)
def node_13_15 : RowTree := .branch (163759059/550000000) node_13_14 node_14_15
def node_12_15 : RowTree := .branch (29752289/100000000) node_12_13 node_13_15
def node_15_16 : RowTree := .leaf (rows01[7]!)
def node_16_17 : RowTree := .leaf (rows02[0]!)
def node_17_18 : RowTree := .leaf (rows02[1]!)
def node_16_18 : RowTree := .branch (65649387/220000000) node_16_17 node_17_18
def node_15_18 : RowTree := .branch (82000999/275000000) node_15_16 node_16_18
def node_12_18 : RowTree := .branch (327761057/1100000000) node_12_15 node_15_18
def node_18_19 : RowTree := .leaf (rows02[2]!)
def node_19_20 : RowTree := .leaf (rows02[3]!)
def node_20_21 : RowTree := .leaf (rows02[4]!)
def node_19_21 : RowTree := .branch (41121969/137500000) node_19_20 node_20_21
def node_18_21 : RowTree := .branch (328732813/1100000000) node_18_19 node_19_21
def node_21_22 : RowTree := .leaf (rows02[5]!)
def node_22_23 : RowTree := .leaf (rows02[6]!)
def node_21_23 : RowTree := .branch (32946163/110000000) node_21_22 node_22_23
def node_23_24 : RowTree := .leaf (rows02[7]!)
def node_24_25 : RowTree := .leaf (rows03[0]!)
def node_23_25 : RowTree := .branch (7498807/25000000) node_23_24 node_24_25
def node_21_25 : RowTree := .branch (329704569/1100000000) node_21_23 node_23_25
def node_18_25 : RowTree := .branch (329218691/1100000000) node_18_21 node_21_25
def node_12_25 : RowTree := .branch (164244937/550000000) node_12_18 node_18_25
def node_0_25 : RowTree := .branch (4087903/13750000) node_0_12 node_12_25
def node_25_26 : RowTree := .leaf (rows03[1]!)
def node_26_27 : RowTree := .leaf (rows03[2]!)
def node_27_28 : RowTree := .leaf (rows03[3]!)
def node_26_28 : RowTree := .branch (13227053/44000000) node_26_27 node_27_28
def node_25_28 : RowTree := .branch (165216693/550000000) node_25_26 node_26_28
def node_28_29 : RowTree := .leaf (rows03[4]!)
def node_29_30 : RowTree := .leaf (rows03[5]!)
def node_30_31 : RowTree := .leaf (rows03[6]!)
def node_29_31 : RowTree := .branch (165702571/550000000) node_29_30 node_30_31
def node_28_31 : RowTree := .branch (331162203/1100000000) node_28_29 node_29_31
def node_25_31 : RowTree := .branch (10341227/34375000) node_25_28 node_28_31
def node_31_32 : RowTree := .leaf (rows03[7]!)
def node_32_33 : RowTree := .leaf (rows04[0]!)
def node_33_34 : RowTree := .leaf (rows04[1]!)
def node_32_34 : RowTree := .branch (332133959/1100000000) node_32_33 node_33_34
def node_31_34 : RowTree := .branch (16594551/55000000) node_31_32 node_32_34
def node_34_35 : RowTree := .leaf (rows04[2]!)
def node_35_36 : RowTree := .leaf (rows04[3]!)
def node_36_37 : RowTree := .leaf (rows04[4]!)
def node_35_37 : RowTree := .branch (41607847/137500000) node_35_36 node_36_37
def node_34_37 : RowTree := .branch (30238167/100000000) node_34_35 node_35_37
def node_31_37 : RowTree := .branch (166188449/550000000) node_31_34 node_34_37
def node_25_37 : RowTree := .branch (331648081/1100000000) node_25_31 node_31_37
def node_37_38 : RowTree := .leaf (rows04[5]!)
def node_38_39 : RowTree := .leaf (rows04[6]!)
def node_39_40 : RowTree := .leaf (rows04[7]!)
def node_38_40 : RowTree := .branch (333591593/1100000000) node_38_39 node_39_40
def node_37_40 : RowTree := .branch (166674327/550000000) node_37_38 node_38_40
def node_40_41 : RowTree := .leaf (rows05[0]!)
def node_41_42 : RowTree := .leaf (rows05[1]!)
def node_42_43 : RowTree := .leaf (rows05[2]!)
def node_41_43 : RowTree := .branch (33432041/110000000) node_41_42 node_42_43
def node_40_43 : RowTree := .branch (334077471/1100000000) node_40_41 node_41_43
def node_37_43 : RowTree := .branch (83458633/275000000) node_37_40 node_40_43
def node_43_44 : RowTree := .leaf (rows05[3]!)
def node_44_45 : RowTree := .leaf (rows05[4]!)
def node_45_46 : RowTree := .leaf (rows05[5]!)
def node_44_46 : RowTree := .branch (335049227/1100000000) node_44_45 node_45_46
def node_43_46 : RowTree := .branch (20925393/68750000) node_43_44 node_44_46
def node_46_47 : RowTree := .leaf (rows05[6]!)
def node_47_48 : RowTree := .leaf (rows05[7]!)
def node_46_48 : RowTree := .branch (67107021/220000000) node_46_47 node_47_48
def node_48_49 : RowTree := .leaf (rows06[0]!)
def node_49_50 : RowTree := .leaf (rows06[1]!)
def node_48_50 : RowTree := .branch (336020983/1100000000) node_48_49 node_49_50
def node_46_50 : RowTree := .branch (83944511/275000000) node_46_48 node_48_50
def node_43_50 : RowTree := .branch (15240553/50000000) node_43_46 node_46_50
def node_37_50 : RowTree := .branch (334563349/1100000000) node_37_43 node_43_50
def node_25_50 : RowTree := .branch (66621143/220000000) node_25_37 node_37_50
def node_0_50 : RowTree := .branch (330190447/1100000000) node_0_25 node_25_50
def node_50_51 : RowTree := .leaf (rows06[2]!)
def node_51_52 : RowTree := .leaf (rows06[3]!)
def node_52_53 : RowTree := .leaf (rows06[4]!)
def node_51_53 : RowTree := .branch (1683749/5500000) node_51_52 node_52_53
def node_50_53 : RowTree := .branch (336506861/1100000000) node_50_51 node_51_53
def node_53_54 : RowTree := .leaf (rows06[5]!)
def node_54_55 : RowTree := .leaf (rows06[6]!)
def node_55_56 : RowTree := .leaf (rows06[7]!)
def node_54_56 : RowTree := .branch (337478617/1100000000) node_54_55 node_55_56
def node_53_56 : RowTree := .branch (168617839/550000000) node_53_54 node_54_56
def node_50_56 : RowTree := .branch (336992739/1100000000) node_50_53 node_53_56
def node_56_57 : RowTree := .leaf (rows07[0]!)
def node_57_58 : RowTree := .leaf (rows07[1]!)
def node_58_59 : RowTree := .leaf (rows07[2]!)
def node_57_59 : RowTree := .branch (169103717/550000000) node_57_58 node_58_59
def node_56_59 : RowTree := .branch (6144809/20000000) node_56_57 node_57_59
def node_59_60 : RowTree := .leaf (rows07[3]!)
def node_60_61 : RowTree := .leaf (rows07[4]!)
def node_61_62 : RowTree := .leaf (rows07[5]!)
def node_60_62 : RowTree := .branch (338936251/1100000000) node_60_61 node_61_62
def node_59_62 : RowTree := .branch (5292083/17187500) node_59_60 node_60_62
def node_56_62 : RowTree := .branch (338450373/1100000000) node_56_59 node_59_62
def node_50_62 : RowTree := .branch (84430389/275000000) node_50_56 node_56_62
def node_62_63 : RowTree := .leaf (rows07[6]!)
def node_63_64 : RowTree := .leaf (rows07[7]!)
def node_64_65 : RowTree := .leaf (rows08[0]!)
def node_63_65 : RowTree := .branch (84916267/275000000) node_63_64 node_64_65
def node_62_65 : RowTree := .branch (339422129/1100000000) node_62_63 node_63_65
def node_65_66 : RowTree := .leaf (rows08[1]!)
def node_66_67 : RowTree := .leaf (rows08[2]!)
def node_67_68 : RowTree := .leaf (rows08[3]!)
def node_66_68 : RowTree := .branch (68078777/220000000) node_66_67 node_67_68
def node_65_68 : RowTree := .branch (170075473/550000000) node_65_66 node_66_68
def node_62_68 : RowTree := .branch (339908007/1100000000) node_62_65 node_65_68
def node_68_69 : RowTree := .leaf (rows08[4]!)
def node_69_70 : RowTree := .leaf (rows08[5]!)
def node_70_71 : RowTree := .leaf (rows08[6]!)
def node_69_71 : RowTree := .branch (170561351/550000000) node_69_70 node_70_71
def node_68_71 : RowTree := .branch (340879763/1100000000) node_68_69 node_69_71
def node_71_72 : RowTree := .leaf (rows08[7]!)
def node_72_73 : RowTree := .leaf (rows09[0]!)
def node_71_73 : RowTree := .branch (17080429/55000000) node_71_72 node_72_73
def node_73_74 : RowTree := .leaf (rows09[1]!)
def node_74_75 : RowTree := .leaf (rows09[2]!)
def node_73_75 : RowTree := .branch (171047229/550000000) node_73_74 node_74_75
def node_71_75 : RowTree := .branch (341851519/1100000000) node_71_73 node_73_75
def node_68_75 : RowTree := .branch (341365641/1100000000) node_68_71 node_71_75
def node_62_75 : RowTree := .branch (3870873/12500000) node_62_68 node_68_75
def node_50_75 : RowTree := .branch (33917919/110000000) node_50_62 node_62_75
def node_75_76 : RowTree := .leaf (rows09[3]!)
def node_76_77 : RowTree := .leaf (rows09[4]!)
def node_77_78 : RowTree := .leaf (rows09[5]!)
def node_76_78 : RowTree := .branch (13712931/44000000) node_76_77 node_77_78
def node_75_78 : RowTree := .branch (21411271/68750000) node_75_76 node_76_78
def node_78_79 : RowTree := .leaf (rows09[6]!)
def node_79_80 : RowTree := .leaf (rows09[7]!)
def node_80_81 : RowTree := .leaf (rows10[0]!)
def node_79_81 : RowTree := .branch (85888023/275000000) node_79_80 node_80_81
def node_78_81 : RowTree := .branch (31209923/100000000) node_78_79 node_79_81
def node_75_81 : RowTree := .branch (171533107/550000000) node_75_78 node_78_81
def node_81_82 : RowTree := .leaf (rows10[1]!)
def node_82_83 : RowTree := .leaf (rows10[2]!)
def node_83_84 : RowTree := .leaf (rows10[3]!)
def node_82_84 : RowTree := .branch (344280909/1100000000) node_82_83 node_83_84
def node_81_84 : RowTree := .branch (34403797/110000000) node_81_82 node_82_84
def node_84_85 : RowTree := .leaf (rows10[4]!)
def node_85_86 : RowTree := .leaf (rows10[5]!)
def node_84_86 : RowTree := .branch (344766787/1100000000) node_84_85 node_85_86
def node_86_87 : RowTree := .leaf (rows10[6]!)
def node_87_88 : RowTree := .leaf (rows10[7]!)
def node_86_88 : RowTree := .branch (69050533/220000000) node_86_87 node_87_88
def node_84_88 : RowTree := .branch (172504863/550000000) node_84_86 node_86_88
def node_81_88 : RowTree := .branch (43065481/137500000) node_81_84 node_84_88
def node_75_88 : RowTree := .branch (343795031/1100000000) node_75_81 node_81_88
def node_88_89 : RowTree := .leaf (rows11[0]!)
def node_89_90 : RowTree := .leaf (rows11[1]!)
def node_90_91 : RowTree := .leaf (rows11[2]!)
def node_89_91 : RowTree := .branch (15726431/50000000) node_89_90 node_90_91
def node_88_91 : RowTree := .branch (345738543/1100000000) node_88_89 node_89_91
def node_91_92 : RowTree := .leaf (rows11[3]!)
def node_92_93 : RowTree := .leaf (rows11[4]!)
def node_93_94 : RowTree := .leaf (rows11[5]!)
def node_92_94 : RowTree := .branch (346710299/1100000000) node_92_93 node_93_94
def node_91_94 : RowTree := .branch (2165421/6875000) node_91_92 node_92_94
def node_88_94 : RowTree := .branch (346224421/1100000000) node_88_91 node_91_94
def node_94_95 : RowTree := .leaf (rows11[6]!)
def node_95_96 : RowTree := .leaf (rows11[7]!)
def node_96_97 : RowTree := .leaf (rows12[0]!)
def node_95_97 : RowTree := .branch (86859779/275000000) node_95_96 node_96_97
def node_94_97 : RowTree := .branch (347196177/1100000000) node_94_95 node_95_97
def node_97_98 : RowTree := .leaf (rows12[1]!)
def node_98_99 : RowTree := .leaf (rows12[2]!)
def node_97_99 : RowTree := .branch (173962497/550000000) node_97_98 node_98_99
def node_99_100 : RowTree := .leaf (rows12[3]!)
def node_100_101 : RowTree := .leaf (rows12[4]!)
def node_99_101 : RowTree := .branch (43551359/137500000) node_99_100 node_100_101
def node_97_101 : RowTree := .branch (348167933/1100000000) node_97_99 node_99_101
def node_94_101 : RowTree := .branch (69536411/220000000) node_94_97 node_97_101
def node_88_101 : RowTree := .branch (173476619/550000000) node_88_94 node_94_101
def node_75_101 : RowTree := .branch (86373901/275000000) node_75_88 node_88_101
def node_50_101 : RowTree := .branch (342337397/1100000000) node_50_75 node_75_101
def node_0_101 : RowTree := .branch (168131961/550000000) node_0_50 node_50_101
def node_101_102 : RowTree := .leaf (rows12[5]!)
def node_102_103 : RowTree := .leaf (rows12[6]!)
def node_103_104 : RowTree := .leaf (rows12[7]!)
def node_102_104 : RowTree := .branch (349139689/1100000000) node_102_103 node_103_104
def node_101_104 : RowTree := .branch (1395587/4400000) node_101_102 node_102_104
def node_104_105 : RowTree := .leaf (rows13[0]!)
def node_105_106 : RowTree := .leaf (rows13[1]!)
def node_106_107 : RowTree := .leaf (rows13[2]!)
def node_105_107 : RowTree := .branch (174934253/550000000) node_105_106 node_106_107
def node_104_107 : RowTree := .branch (349625567/1100000000) node_104_105 node_105_107
def node_101_107 : RowTree := .branch (87345657/275000000) node_101_104 node_104_107
def node_107_108 : RowTree := .leaf (rows13[3]!)
def node_108_109 : RowTree := .leaf (rows13[4]!)
def node_109_110 : RowTree := .leaf (rows13[5]!)
def node_108_110 : RowTree := .branch (350597323/1100000000) node_108_109 node_109_110
def node_107_110 : RowTree := .branch (21897149/68750000) node_107_108 node_108_110
def node_110_111 : RowTree := .leaf (rows13[6]!)
def node_111_112 : RowTree := .leaf (rows13[7]!)
def node_112_113 : RowTree := .leaf (rows14[0]!)
def node_111_113 : RowTree := .branch (1596937/5000000) node_111_112 node_112_113
def node_110_113 : RowTree := .branch (351083201/1100000000) node_110_111 node_111_113
def node_107_113 : RowTree := .branch (175420131/550000000) node_107_110 node_110_113
def node_101_113 : RowTree := .branch (70022289/220000000) node_101_107 node_107_113
def node_113_114 : RowTree := .leaf (rows14[1]!)
def node_114_115 : RowTree := .leaf (rows14[2]!)
def node_115_116 : RowTree := .leaf (rows14[3]!)
def node_114_116 : RowTree := .branch (352054957/1100000000) node_114_115 node_115_116
def node_113_116 : RowTree := .branch (175906009/550000000) node_113_114 node_114_116
def node_116_117 : RowTree := .leaf (rows14[4]!)
def node_117_118 : RowTree := .leaf (rows14[5]!)
def node_118_119 : RowTree := .leaf (rows14[6]!)
def node_117_119 : RowTree := .branch (176391887/550000000) node_117_118 node_118_119
def node_116_119 : RowTree := .branch (70508167/220000000) node_116_117 node_117_119
def node_113_119 : RowTree := .branch (44037237/137500000) node_113_116 node_116_119
def node_119_120 : RowTree := .leaf (rows14[7]!)
def node_120_121 : RowTree := .leaf (rows15[0]!)
def node_121_122 : RowTree := .leaf (rows15[1]!)
def node_120_122 : RowTree := .branch (353512591/1100000000) node_120_121 node_121_122
def node_119_122 : RowTree := .branch (88317413/275000000) node_119_120 node_120_122
def node_122_123 : RowTree := .leaf (rows15[2]!)
def node_123_124 : RowTree := .leaf (rows15[3]!)
def node_122_124 : RowTree := .branch (32181679/100000000) node_122_123 node_123_124
def node_124_125 : RowTree := .leaf (rows15[4]!)
def node_125_126 : RowTree := .leaf (rows15[5]!)
def node_124_126 : RowTree := .branch (354484347/1100000000) node_124_125 node_125_126
def node_122_126 : RowTree := .branch (2767511/8593750) node_122_124 node_124_126
def node_119_126 : RowTree := .branch (35375553/110000000) node_119_122 node_122_126
def node_113_126 : RowTree := .branch (353026713/1100000000) node_113_119 node_119_126
def node_101_126 : RowTree := .branch (351569079/1100000000) node_101_113 node_113_126
def node_126_127 : RowTree := .leaf (rows15[6]!)
def node_127_128 : RowTree := .leaf (rows15[7]!)
def node_128_129 : RowTree := .leaf (rows16[0]!)
def node_127_129 : RowTree := .branch (88803291/275000000) node_127_128 node_128_129
def node_126_129 : RowTree := .branch (14198809/44000000) node_126_127 node_127_129
def node_129_130 : RowTree := .leaf (rows16[1]!)
def node_130_131 : RowTree := .leaf (rows16[2]!)
def node_131_132 : RowTree := .leaf (rows16[3]!)
def node_130_132 : RowTree := .branch (355941981/1100000000) node_130_131 node_131_132
def node_129_132 : RowTree := .branch (177849521/550000000) node_129_130 node_130_132
def node_126_132 : RowTree := .branch (355456103/1100000000) node_126_129 node_129_132
def node_132_133 : RowTree := .leaf (rows16[4]!)
def node_133_134 : RowTree := .leaf (rows16[5]!)
def node_134_135 : RowTree := .leaf (rows16[6]!)
def node_133_135 : RowTree := .branch (16212309/50000000) node_133_134 node_134_135
def node_132_135 : RowTree := .branch (356427859/1100000000) node_132_133 node_133_135
def node_135_136 : RowTree := .leaf (rows16[7]!)
def node_136_137 : RowTree := .leaf (rows17[0]!)
def node_137_138 : RowTree := .leaf (rows17[1]!)
def node_136_138 : RowTree := .branch (71479923/220000000) node_136_137 node_137_138
def node_135_138 : RowTree := .branch (89289169/275000000) node_135_136 node_136_138
def node_132_138 : RowTree := .branch (356913737/1100000000) node_132_135 node_135_138
def node_126_138 : RowTree := .branch (8904623/27500000) node_126_132 node_132_138
def node_138_139 : RowTree := .leaf (rows17[2]!)
def node_139_140 : RowTree := .leaf (rows17[3]!)
def node_140_141 : RowTree := .leaf (rows17[4]!)
def node_139_141 : RowTree := .branch (22383027/68750000) node_139_140 node_140_141
def node_138_141 : RowTree := .branch (357885493/1100000000) node_138_139 node_139_141
def node_141_142 : RowTree := .leaf (rows17[5]!)
def node_142_143 : RowTree := .leaf (rows17[6]!)
def node_143_144 : RowTree := .leaf (rows17[7]!)
def node_142_144 : RowTree := .branch (358857249/1100000000) node_142_143 node_143_144
def node_141_144 : RowTree := .branch (35861431/110000000) node_141_142 node_142_144
def node_138_144 : RowTree := .branch (358371371/1100000000) node_138_141 node_141_144
def node_144_145 : RowTree := .leaf (rows18[0]!)
def node_145_146 : RowTree := .leaf (rows18[1]!)
def node_146_147 : RowTree := .leaf (rows18[2]!)
def node_145_147 : RowTree := .branch (179793033/550000000) node_145_146 node_146_147
def node_144_147 : RowTree := .branch (32667557/100000000) node_144_145 node_145_147
def node_147_148 : RowTree := .leaf (rows18[3]!)
def node_148_149 : RowTree := .leaf (rows18[4]!)
def node_147_149 : RowTree := .branch (45008993/137500000) node_147_148 node_148_149
def node_149_150 : RowTree := .leaf (rows18[5]!)
def node_150_151 : RowTree := .leaf (rows18[6]!)
def node_149_151 : RowTree := .branch (180278911/550000000) node_149_150 node_150_151
def node_147_151 : RowTree := .branch (360314883/1100000000) node_147_149 node_149_151
def node_144_151 : RowTree := .branch (71965801/220000000) node_144_147 node_147_151
def node_138_151 : RowTree := .branch (89775047/275000000) node_138_144 node_144_151
def node_126_151 : RowTree := .branch (178821277/550000000) node_126_138 node_138_151
def node_101_151 : RowTree := .branch (177363643/550000000) node_101_126 node_126_151
def node_151_152 : RowTree := .leaf (rows18[7]!)
def node_152_153 : RowTree := .leaf (rows19[0]!)
def node_153_154 : RowTree := .leaf (rows19[1]!)
def node_152_154 : RowTree := .branch (361286639/1100000000) node_152_153 node_153_154
def node_151_154 : RowTree := .branch (3610437/11000000) node_151_152 node_152_154
def node_154_155 : RowTree := .leaf (rows19[2]!)
def node_155_156 : RowTree := .leaf (rows19[3]!)
def node_156_157 : RowTree := .leaf (rows19[4]!)
def node_155_157 : RowTree := .branch (1028453/3125000) node_155_156 node_156_157
def node_154_157 : RowTree := .branch (361772517/1100000000) node_154_155 node_155_157
def node_151_157 : RowTree := .branch (180764789/550000000) node_151_154 node_154_157
def node_157_158 : RowTree := .leaf (rows19[5]!)
def node_158_159 : RowTree := .leaf (rows19[6]!)
def node_159_160 : RowTree := .leaf (rows19[7]!)
def node_158_160 : RowTree := .branch (362744273/1100000000) node_158_159 node_159_160
def node_157_160 : RowTree := .branch (181250667/550000000) node_157_158 node_158_160
def node_160_161 : RowTree := .leaf (rows20[0]!)
def node_161_162 : RowTree := .leaf (rows20[1]!)
def node_162_163 : RowTree := .leaf (rows20[2]!)
def node_161_163 : RowTree := .branch (36347309/110000000) node_161_162 node_162_163
def node_160_163 : RowTree := .branch (363230151/1100000000) node_160_161 node_161_163
def node_157_163 : RowTree := .branch (90746803/275000000) node_157_160 node_160_163
def node_151_163 : RowTree := .branch (72451679/220000000) node_151_157 node_157_163
def node_163_164 : RowTree := .leaf (rows20[3]!)
def node_164_165 : RowTree := .leaf (rows20[4]!)
def node_165_166 : RowTree := .leaf (rows20[5]!)
def node_164_166 : RowTree := .branch (364201907/1100000000) node_164_165 node_165_166
def node_163_166 : RowTree := .branch (45494871/137500000) node_163_164 node_164_166
def node_166_167 : RowTree := .leaf (rows20[6]!)
def node_167_168 : RowTree := .leaf (rows20[7]!)
def node_168_169 : RowTree := .leaf (rows21[0]!)
def node_167_169 : RowTree := .branch (91232681/275000000) node_167_168 node_168_169
def node_166_169 : RowTree := .branch (6630687/20000000) node_166_167 node_167_169
def node_163_169 : RowTree := .branch (182222423/550000000) node_163_166 node_166_169
def node_169_170 : RowTree := .leaf (rows21[1]!)
def node_170_171 : RowTree := .leaf (rows21[2]!)
def node_171_172 : RowTree := .leaf (rows21[3]!)
def node_170_172 : RowTree := .branch (365659541/1100000000) node_170_171 node_171_172
def node_169_172 : RowTree := .branch (182708301/550000000) node_169_170 node_170_172
def node_172_173 : RowTree := .leaf (rows21[4]!)
def node_173_174 : RowTree := .leaf (rows21[5]!)
def node_172_174 : RowTree := .branch (366145419/1100000000) node_172_173 node_173_174
def node_174_175 : RowTree := .leaf (rows21[6]!)
def node_175_176 : RowTree := .leaf (rows21[7]!)
def node_174_176 : RowTree := .branch (366631297/1100000000) node_174_175 node_175_176
def node_172_176 : RowTree := .branch (183194179/550000000) node_172_174 node_174_176
def node_169_176 : RowTree := .branch (4573781/13750000) node_169_172 node_172_176
def node_163_176 : RowTree := .branch (365173663/1100000000) node_163_169 node_169_176
def node_151_176 : RowTree := .branch (363716029/1100000000) node_151_163 node_163_176
def node_176_177 : RowTree := .leaf (rows22[0]!)
def node_177_178 : RowTree := .leaf (rows22[1]!)
def node_178_179 : RowTree := .leaf (rows22[2]!)
def node_177_179 : RowTree := .branch (16698187/50000000) node_177_178 node_178_179
def node_176_179 : RowTree := .branch (14684687/44000000) node_176_177 node_177_179
def node_179_180 : RowTree := .leaf (rows22[3]!)
def node_180_181 : RowTree := .leaf (rows22[4]!)
def node_181_182 : RowTree := .leaf (rows22[5]!)
def node_180_182 : RowTree := .branch (368088931/1100000000) node_180_181 node_181_182
def node_179_182 : RowTree := .branch (45980749/137500000) node_179_180 node_180_182
def node_176_182 : RowTree := .branch (367603053/1100000000) node_176_179 node_179_182
def node_182_183 : RowTree := .leaf (rows22[6]!)
def node_183_184 : RowTree := .leaf (rows22[7]!)
def node_184_185 : RowTree := .leaf (rows23[0]!)
def node_183_185 : RowTree := .branch (92204437/275000000) node_183_184 node_184_185
def node_182_185 : RowTree := .branch (368574809/1100000000) node_182_183 node_183_185
def node_185_186 : RowTree := .leaf (rows23[1]!)
def node_186_187 : RowTree := .leaf (rows23[2]!)
def node_185_187 : RowTree := .branch (184651813/550000000) node_185_186 node_186_187
def node_187_188 : RowTree := .leaf (rows23[3]!)
def node_188_189 : RowTree := .leaf (rows23[4]!)
def node_187_189 : RowTree := .branch (5777961/17187500) node_187_188 node_188_189
def node_185_189 : RowTree := .branch (73909313/220000000) node_185_187 node_187_189
def node_182_189 : RowTree := .branch (369060687/1100000000) node_182_185 node_185_189
def node_176_189 : RowTree := .branch (36833187/110000000) node_176_182 node_182_189
def node_189_190 : RowTree := .leaf (rows23[5]!)
def node_190_191 : RowTree := .leaf (rows23[6]!)
def node_191_192 : RowTree := .leaf (rows23[7]!)
def node_190_192 : RowTree := .branch (370518321/1100000000) node_190_191 node_191_192
def node_189_192 : RowTree := .branch (185137691/550000000) node_189_190 node_190_192
def node_192_193 : RowTree := .leaf (rows24[0]!)
def node_193_194 : RowTree := .leaf (rows24[1]!)
def node_194_195 : RowTree := .leaf (rows24[2]!)
def node_193_195 : RowTree := .branch (185623569/550000000) node_193_194 node_194_195
def node_192_195 : RowTree := .branch (371004199/1100000000) node_192_193 node_193_195
def node_189_195 : RowTree := .branch (18538063/55000000) node_189_192 node_192_195
def node_195_196 : RowTree := .leaf (rows24[3]!)
def node_196_197 : RowTree := .leaf (rows24[4]!)
def node_197_198 : RowTree := .leaf (rows24[5]!)
def node_196_198 : RowTree := .branch (74395191/220000000) node_196_197 node_197_198
def node_195_198 : RowTree := .branch (46466627/137500000) node_195_196 node_196_198
def node_198_199 : RowTree := .leaf (rows24[6]!)
def node_199_200 : RowTree := .leaf (rows24[7]!)
def node_198_200 : RowTree := .branch (372461833/1100000000) node_198_199 node_199_200
def node_200_201 : RowTree := .leaf (rows25[0]!)
def node_201_202 : RowTree := .leaf (rows25[1]!)
def node_200_202 : RowTree := .branch (372947711/1100000000) node_200_201 node_201_202
def node_198_202 : RowTree := .branch (8470563/25000000) node_198_200 node_200_202
def node_195_202 : RowTree := .branch (186109447/550000000) node_195_198 node_198_202
def node_189_202 : RowTree := .branch (371490077/1100000000) node_189_195 node_195_202
def node_176_202 : RowTree := .branch (33639313/100000000) node_176_189 node_189_202
def node_151_202 : RowTree := .branch (91718559/275000000) node_151_176 node_176_202
def node_101_202 : RowTree := .branch (360800761/1100000000) node_101_151 node_151_202
def node_0_202 : RowTree := .branch (31695801/100000000) node_0_101 node_101_202
def node_202_203 : RowTree := .leaf (rows25[2]!)
def node_203_204 : RowTree := .leaf (rows25[3]!)
def node_204_205 : RowTree := .leaf (rows25[4]!)
def node_203_205 : RowTree := .branch (23354783/68750000) node_203_204 node_204_205
def node_202_205 : RowTree := .branch (373433589/1100000000) node_202_203 node_203_205
def node_205_206 : RowTree := .leaf (rows25[5]!)
def node_206_207 : RowTree := .leaf (rows25[6]!)
def node_207_208 : RowTree := .leaf (rows25[7]!)
def node_206_208 : RowTree := .branch (74881069/220000000) node_206_207 node_207_208
def node_205_208 : RowTree := .branch (187081203/550000000) node_205_206 node_206_208
def node_202_208 : RowTree := .branch (373919467/1100000000) node_202_205 node_205_208
def node_208_209 : RowTree := .leaf (rows26[0]!)
def node_209_210 : RowTree := .leaf (rows26[1]!)
def node_210_211 : RowTree := .leaf (rows26[2]!)
def node_209_211 : RowTree := .branch (187567081/550000000) node_209_210 node_210_211
def node_208_211 : RowTree := .branch (374891223/1100000000) node_208_209 node_209_211
def node_211_212 : RowTree := .leaf (rows26[3]!)
def node_212_213 : RowTree := .leaf (rows26[4]!)
def node_213_214 : RowTree := .leaf (rows26[5]!)
def node_212_214 : RowTree := .branch (375862979/1100000000) node_212_213 node_213_214
def node_211_214 : RowTree := .branch (9390501/27500000) node_211_212 node_212_214
def node_208_214 : RowTree := .branch (34125191/100000000) node_208_211 node_211_214
def node_202_214 : RowTree := .branch (93662071/275000000) node_202_208 node_208_214
def node_214_215 : RowTree := .leaf (rows26[6]!)
def node_215_216 : RowTree := .leaf (rows26[7]!)
def node_216_217 : RowTree := .leaf (rows27[0]!)
def node_215_217 : RowTree := .branch (94147949/275000000) node_215_216 node_216_217
def node_214_217 : RowTree := .branch (376348857/1100000000) node_214_215 node_215_217
def node_217_218 : RowTree := .leaf (rows27[1]!)
def node_218_219 : RowTree := .leaf (rows27[2]!)
def node_219_220 : RowTree := .leaf (rows27[3]!)
def node_218_220 : RowTree := .branch (377320613/1100000000) node_218_219 node_219_220
def node_217_220 : RowTree := .branch (188538837/550000000) node_217_218 node_218_220
def node_214_220 : RowTree := .branch (75366947/220000000) node_214_217 node_217_220
def node_220_221 : RowTree := .leaf (rows27[4]!)
def node_221_222 : RowTree := .leaf (rows27[5]!)
def node_222_223 : RowTree := .leaf (rows27[6]!)
def node_221_223 : RowTree := .branch (3436813/10000000) node_221_222 node_222_223
def node_220_223 : RowTree := .branch (377806491/1100000000) node_220_221 node_221_223
def node_223_224 : RowTree := .leaf (rows27[7]!)
def node_224_225 : RowTree := .leaf (rows28[0]!)
def node_223_225 : RowTree := .branch (94633827/275000000) node_223_224 node_224_225
def node_225_226 : RowTree := .leaf (rows28[1]!)
def node_226_227 : RowTree := .leaf (rows28[2]!)
def node_225_227 : RowTree := .branch (189510593/550000000) node_225_226 node_226_227
def node_223_227 : RowTree := .branch (378778247/1100000000) node_223_225 node_225_227
def node_220_227 : RowTree := .branch (378292369/1100000000) node_220_223 node_223_227
def node_214_227 : RowTree := .branch (11798861/34375000) node_214_220 node_220_227
def node_202_227 : RowTree := .branch (188052959/550000000) node_202_214 node_214_227
def node_227_228 : RowTree := .leaf (rows28[3]!)
def node_228_229 : RowTree := .leaf (rows28[4]!)
def node_229_230 : RowTree := .leaf (rows28[5]!)
def node_228_230 : RowTree := .branch (379750003/1100000000) node_228_229 node_229_230
def node_227_230 : RowTree := .branch (47438383/137500000) node_227_228 node_228_230
def node_230_231 : RowTree := .leaf (rows28[6]!)
def node_231_232 : RowTree := .leaf (rows28[7]!)
def node_232_233 : RowTree := .leaf (rows29[0]!)
def node_231_233 : RowTree := .branch (19023941/55000000) node_231_232 node_232_233
def node_230_233 : RowTree := .branch (380235881/1100000000) node_230_231 node_231_233
def node_227_233 : RowTree := .branch (189996471/550000000) node_227_230 node_230_233
def node_233_234 : RowTree := .leaf (rows29[1]!)
def node_234_235 : RowTree := .leaf (rows29[2]!)
def node_235_236 : RowTree := .leaf (rows29[3]!)
def node_234_236 : RowTree := .branch (381207637/1100000000) node_234_235 node_235_236
def node_233_236 : RowTree := .branch (190482349/550000000) node_233_234 node_234_236
def node_236_237 : RowTree := .leaf (rows29[4]!)
def node_237_238 : RowTree := .leaf (rows29[5]!)
def node_238_239 : RowTree := .leaf (rows29[6]!)
def node_237_239 : RowTree := .branch (190968227/550000000) node_237_238 node_238_239
def node_236_239 : RowTree := .branch (76338703/220000000) node_236_237 node_237_239
def node_233_239 : RowTree := .branch (23840661/68750000) node_233_236 node_236_239
def node_227_239 : RowTree := .branch (34611069/100000000) node_227_233 node_233_239
def node_239_240 : RowTree := .leaf (rows29[7]!)
def node_240_241 : RowTree := .leaf (rows30[0]!)
def node_241_242 : RowTree := .leaf (rows30[1]!)
def node_240_242 : RowTree := .branch (382665271/1100000000) node_240_241 node_241_242
def node_239_242 : RowTree := .branch (95605583/275000000) node_239_240 node_240_242
def node_242_243 : RowTree := .leaf (rows30[2]!)
def node_243_244 : RowTree := .leaf (rows30[3]!)
def node_244_245 : RowTree := .leaf (rows30[4]!)
def node_243_245 : RowTree := .branch (4356751/12500000) node_243_244 node_244_245
def node_242_245 : RowTree := .branch (383151149/1100000000) node_242_243 node_243_245
def node_239_245 : RowTree := .branch (38290821/110000000) node_239_242 node_242_245
def node_245_246 : RowTree := .leaf (rows30[5]!)
def node_246_247 : RowTree := .leaf (rows30[6]!)
def node_247_248 : RowTree := .leaf (rows30[7]!)
def node_246_248 : RowTree := .branch (98/125) node_246_247 node_247_248
def node_245_248 : RowTree := .branch (1567/2000) node_245_246 node_246_248
def node_248_249 : RowTree := .leaf (rows31[0]!)
def node_249_250 : RowTree := .leaf (rows31[1]!)
def node_248_250 : RowTree := .branch (157/200) node_248_249 node_249_250
def node_250_251 : RowTree := .leaf (rows31[2]!)
def node_251_252 : RowTree := .leaf (rows31[3]!)
def node_250_252 : RowTree := .branch (393/500) node_250_251 node_251_252
def node_248_252 : RowTree := .branch (1571/2000) node_248_250 node_250_252
def node_245_252 : RowTree := .branch (1569/2000) node_245_248 node_248_252
def node_239_252 : RowTree := .branch (783/1000) node_239_245 node_245_252
def node_227_252 : RowTree := .branch (382179393/1100000000) node_227_239 node_239_252
def node_202_252 : RowTree := .branch (3034113/8800000) node_202_227 node_227_252
def node_252_253 : RowTree := .leaf (rows31[4]!)
def node_253_254 : RowTree := .leaf (rows31[5]!)
def node_254_255 : RowTree := .leaf (rows31[6]!)
def node_253_255 : RowTree := .branch (63/80) node_253_254 node_254_255
def node_252_255 : RowTree := .branch (787/1000) node_252_253 node_253_255
def node_255_256 : RowTree := .leaf (rows31[7]!)
def node_256_257 : RowTree := .leaf (rows32[0]!)
def node_257_258 : RowTree := .leaf (rows32[1]!)
def node_256_258 : RowTree := .branch (789/1000) node_256_257 node_257_258
def node_255_258 : RowTree := .branch (1577/2000) node_255_256 node_256_258
def node_252_258 : RowTree := .branch (197/250) node_252_255 node_255_258
def node_258_259 : RowTree := .leaf (rows32[2]!)
def node_259_260 : RowTree := .leaf (rows32[3]!)
def node_260_261 : RowTree := .leaf (rows32[4]!)
def node_259_261 : RowTree := .branch (1581/2000) node_259_260 node_260_261
def node_258_261 : RowTree := .branch (79/100) node_258_259 node_259_261
def node_261_262 : RowTree := .leaf (rows32[5]!)
def node_262_263 : RowTree := .leaf (rows32[6]!)
def node_263_264 : RowTree := .leaf (rows32[7]!)
def node_262_264 : RowTree := .branch (99/125) node_262_263 node_263_264
def node_261_264 : RowTree := .branch (1583/2000) node_261_262 node_262_264
def node_258_264 : RowTree := .branch (791/1000) node_258_261 node_261_264
def node_252_264 : RowTree := .branch (1579/2000) node_252_258 node_258_264
def node_264_265 : RowTree := .leaf (rows33[0]!)
def node_265_266 : RowTree := .leaf (rows33[1]!)
def node_266_267 : RowTree := .leaf (rows33[2]!)
def node_265_267 : RowTree := .branch (1587/2000) node_265_266 node_266_267
def node_264_267 : RowTree := .branch (793/1000) node_264_265 node_265_267
def node_267_268 : RowTree := .leaf (rows33[3]!)
def node_268_269 : RowTree := .leaf (rows33[4]!)
def node_269_270 : RowTree := .leaf (rows33[5]!)
def node_268_270 : RowTree := .branch (159/200) node_268_269 node_269_270
def node_267_270 : RowTree := .branch (1589/2000) node_267_268 node_268_270
def node_264_270 : RowTree := .branch (397/500) node_264_267 node_267_270
def node_270_271 : RowTree := .leaf (rows33[6]!)
def node_271_272 : RowTree := .leaf (rows33[7]!)
def node_272_273 : RowTree := .leaf (rows34[0]!)
def node_271_273 : RowTree := .branch (1593/2000) node_271_272 node_272_273
def node_270_273 : RowTree := .branch (199/250) node_270_271 node_271_273
def node_273_274 : RowTree := .leaf (rows34[1]!)
def node_274_275 : RowTree := .leaf (rows34[2]!)
def node_273_275 : RowTree := .branch (319/400) node_273_274 node_274_275
def node_275_276 : RowTree := .leaf (rows34[3]!)
def node_276_277 : RowTree := .leaf (rows34[4]!)
def node_275_277 : RowTree := .branch (1597/2000) node_275_276 node_276_277
def node_273_277 : RowTree := .branch (399/500) node_273_275 node_275_277
def node_270_277 : RowTree := .branch (797/1000) node_270_273 node_273_277
def node_264_277 : RowTree := .branch (1591/2000) node_264_270 node_270_277
def node_252_277 : RowTree := .branch (317/400) node_252_264 node_264_277
def node_277_278 : RowTree := .leaf (rows34[5]!)
def node_278_279 : RowTree := .leaf (rows34[6]!)
def node_279_280 : RowTree := .leaf (rows34[7]!)
def node_278_280 : RowTree := .branch (4/5) node_278_279 node_279_280
def node_277_280 : RowTree := .branch (1599/2000) node_277_278 node_278_280
def node_280_281 : RowTree := .leaf (rows35[0]!)
def node_281_282 : RowTree := .leaf (rows35[1]!)
def node_282_283 : RowTree := .leaf (rows35[2]!)
def node_281_283 : RowTree := .branch (1603/2000) node_281_282 node_282_283
def node_280_283 : RowTree := .branch (801/1000) node_280_281 node_281_283
def node_277_283 : RowTree := .branch (1601/2000) node_277_280 node_280_283
def node_283_284 : RowTree := .leaf (rows35[3]!)
def node_284_285 : RowTree := .leaf (rows35[4]!)
def node_285_286 : RowTree := .leaf (rows35[5]!)
def node_284_286 : RowTree := .branch (803/1000) node_284_285 node_285_286
def node_283_286 : RowTree := .branch (321/400) node_283_284 node_284_286
def node_286_287 : RowTree := .leaf (rows35[6]!)
def node_287_288 : RowTree := .leaf (rows35[7]!)
def node_286_288 : RowTree := .branch (201/250) node_286_287 node_287_288
def node_288_289 : RowTree := .leaf (rows36[0]!)
def node_289_290 : RowTree := .leaf (rows36[1]!)
def node_288_290 : RowTree := .branch (161/200) node_288_289 node_289_290
def node_286_290 : RowTree := .branch (1609/2000) node_286_288 node_288_290
def node_283_290 : RowTree := .branch (1607/2000) node_283_286 node_286_290
def node_277_290 : RowTree := .branch (401/500) node_277_283 node_283_290
def node_290_291 : RowTree := .leaf (rows36[2]!)
def node_291_292 : RowTree := .leaf (rows36[3]!)
def node_292_293 : RowTree := .leaf (rows36[4]!)
def node_291_293 : RowTree := .branch (1613/2000) node_291_292 node_292_293
def node_290_293 : RowTree := .branch (403/500) node_290_291 node_291_293
def node_293_294 : RowTree := .leaf (rows36[5]!)
def node_294_295 : RowTree := .leaf (rows36[6]!)
def node_295_296 : RowTree := .leaf (rows36[7]!)
def node_294_296 : RowTree := .branch (101/125) node_294_295 node_295_296
def node_293_296 : RowTree := .branch (323/400) node_293_294 node_294_296
def node_290_296 : RowTree := .branch (807/1000) node_290_293 node_293_296
def node_296_297 : RowTree := .leaf (rows37[0]!)
def node_297_298 : RowTree := .leaf (rows37[1]!)
def node_298_299 : RowTree := .leaf (rows37[2]!)
def node_297_299 : RowTree := .branch (1619/2000) node_297_298 node_298_299
def node_296_299 : RowTree := .branch (809/1000) node_296_297 node_297_299
def node_299_300 : RowTree := .leaf (rows37[3]!)
def node_300_301 : RowTree := .leaf (rows37[4]!)
def node_299_301 : RowTree := .branch (1621/2000) node_299_300 node_300_301
def node_301_302 : RowTree := .leaf (rows37[5]!)
def node_302_303 : RowTree := .leaf (rows37[6]!)
def node_301_303 : RowTree := .branch (1623/2000) node_301_302 node_302_303
def node_299_303 : RowTree := .branch (811/1000) node_299_301 node_301_303
def node_296_303 : RowTree := .branch (81/100) node_296_299 node_299_303
def node_290_303 : RowTree := .branch (1617/2000) node_290_296 node_296_303
def node_277_303 : RowTree := .branch (1611/2000) node_277_290 node_290_303
def node_252_303 : RowTree := .branch (799/1000) node_252_277 node_277_303
def node_202_303 : RowTree := .branch (1573/2000) node_202_252 node_252_303
def node_303_304 : RowTree := .leaf (rows37[7]!)
def node_304_305 : RowTree := .leaf (rows38[0]!)
def node_305_306 : RowTree := .leaf (rows38[1]!)
def node_304_306 : RowTree := .branch (813/1000) node_304_305 node_305_306
def node_303_306 : RowTree := .branch (13/16) node_303_304 node_304_306
def node_306_307 : RowTree := .leaf (rows38[2]!)
def node_307_308 : RowTree := .leaf (rows38[3]!)
def node_308_309 : RowTree := .leaf (rows38[4]!)
def node_307_309 : RowTree := .branch (1629/2000) node_307_308 node_308_309
def node_306_309 : RowTree := .branch (407/500) node_306_307 node_307_309
def node_303_309 : RowTree := .branch (1627/2000) node_303_306 node_306_309
def node_309_310 : RowTree := .leaf (rows38[5]!)
def node_310_311 : RowTree := .leaf (rows38[6]!)
def node_311_312 : RowTree := .leaf (rows38[7]!)
def node_310_312 : RowTree := .branch (102/125) node_310_311 node_311_312
def node_309_312 : RowTree := .branch (1631/2000) node_309_310 node_310_312
def node_312_313 : RowTree := .leaf (rows39[0]!)
def node_313_314 : RowTree := .leaf (rows39[1]!)
def node_314_315 : RowTree := .leaf (rows39[2]!)
def node_313_315 : RowTree := .branch (327/400) node_313_314 node_314_315
def node_312_315 : RowTree := .branch (817/1000) node_312_313 node_313_315
def node_309_315 : RowTree := .branch (1633/2000) node_309_312 node_312_315
def node_303_315 : RowTree := .branch (163/200) node_303_309 node_309_315
def node_315_316 : RowTree := .leaf (rows39[3]!)
def node_316_317 : RowTree := .leaf (rows39[4]!)
def node_317_318 : RowTree := .leaf (rows39[5]!)
def node_316_318 : RowTree := .branch (819/1000) node_316_317 node_317_318
def node_315_318 : RowTree := .branch (1637/2000) node_315_316 node_316_318
def node_318_319 : RowTree := .leaf (rows39[6]!)
def node_319_320 : RowTree := .leaf (rows39[7]!)
def node_320_321 : RowTree := .leaf (rows40[0]!)
def node_319_321 : RowTree := .branch (1641/2000) node_319_320 node_320_321
def node_318_321 : RowTree := .branch (41/50) node_318_319 node_319_321
def node_315_321 : RowTree := .branch (1639/2000) node_315_318 node_318_321
def node_321_322 : RowTree := .leaf (rows40[1]!)
def node_322_323 : RowTree := .leaf (rows40[2]!)
def node_323_324 : RowTree := .leaf (rows40[3]!)
def node_322_324 : RowTree := .branch (411/500) node_322_323 node_323_324
def node_321_324 : RowTree := .branch (1643/2000) node_321_322 node_322_324
def node_324_325 : RowTree := .leaf (rows40[4]!)
def node_325_326 : RowTree := .leaf (rows40[5]!)
def node_324_326 : RowTree := .branch (823/1000) node_324_325 node_325_326
def node_326_327 : RowTree := .leaf (rows40[6]!)
def node_327_328 : RowTree := .leaf (rows40[7]!)
def node_326_328 : RowTree := .branch (103/125) node_326_327 node_327_328
def node_324_328 : RowTree := .branch (1647/2000) node_324_326 node_326_328
def node_321_328 : RowTree := .branch (329/400) node_321_324 node_324_328
def node_315_328 : RowTree := .branch (821/1000) node_315_321 node_321_328
def node_303_328 : RowTree := .branch (409/500) node_303_315 node_315_328
def node_328_329 : RowTree := .leaf (rows41[0]!)
def node_329_330 : RowTree := .leaf (rows41[1]!)
def node_330_331 : RowTree := .leaf (rows41[2]!)
def node_329_331 : RowTree := .branch (1651/2000) node_329_330 node_330_331
def node_328_331 : RowTree := .branch (33/40) node_328_329 node_329_331
def node_331_332 : RowTree := .leaf (rows41[3]!)
def node_332_333 : RowTree := .leaf (rows41[4]!)
def node_333_334 : RowTree := .leaf (rows41[5]!)
def node_332_334 : RowTree := .branch (827/1000) node_332_333 node_333_334
def node_331_334 : RowTree := .branch (1653/2000) node_331_332 node_332_334
def node_328_334 : RowTree := .branch (413/500) node_328_331 node_331_334
def node_334_335 : RowTree := .leaf (rows41[6]!)
def node_335_336 : RowTree := .leaf (rows41[7]!)
def node_336_337 : RowTree := .leaf (rows42[0]!)
def node_335_337 : RowTree := .branch (1657/2000) node_335_336 node_336_337
def node_334_337 : RowTree := .branch (207/250) node_334_335 node_335_337
def node_337_338 : RowTree := .leaf (rows42[1]!)
def node_338_339 : RowTree := .leaf (rows42[2]!)
def node_337_339 : RowTree := .branch (1659/2000) node_337_338 node_338_339
def node_339_340 : RowTree := .leaf (rows42[3]!)
def node_340_341 : RowTree := .leaf (rows42[4]!)
def node_339_341 : RowTree := .branch (1661/2000) node_339_340 node_340_341
def node_337_341 : RowTree := .branch (83/100) node_337_339 node_339_341
def node_334_341 : RowTree := .branch (829/1000) node_334_337 node_337_341
def node_328_341 : RowTree := .branch (331/400) node_328_334 node_334_341
def node_341_342 : RowTree := .leaf (rows42[5]!)
def node_342_343 : RowTree := .leaf (rows42[6]!)
def node_343_344 : RowTree := .leaf (rows42[7]!)
def node_342_344 : RowTree := .branch (104/125) node_342_343 node_343_344
def node_341_344 : RowTree := .branch (1663/2000) node_341_342 node_342_344
def node_344_345 : RowTree := .leaf (rows43[0]!)
def node_345_346 : RowTree := .leaf (rows43[1]!)
def node_346_347 : RowTree := .leaf (rows43[2]!)
def node_345_347 : RowTree := .branch (1667/2000) node_345_346 node_346_347
def node_344_347 : RowTree := .branch (833/1000) node_344_345 node_345_347
def node_341_347 : RowTree := .branch (333/400) node_341_344 node_344_347
def node_347_348 : RowTree := .leaf (rows43[3]!)
def node_348_349 : RowTree := .leaf (rows43[4]!)
def node_349_350 : RowTree := .leaf (rows43[5]!)
def node_348_350 : RowTree := .branch (167/200) node_348_349 node_349_350
def node_347_350 : RowTree := .branch (1669/2000) node_347_348 node_348_350
def node_350_351 : RowTree := .leaf (rows43[6]!)
def node_351_352 : RowTree := .leaf (rows43[7]!)
def node_350_352 : RowTree := .branch (209/250) node_350_351 node_351_352
def node_352_353 : RowTree := .leaf (rows44[0]!)
def node_353_354 : RowTree := .leaf (rows44[1]!)
def node_352_354 : RowTree := .branch (837/1000) node_352_353 node_353_354
def node_350_354 : RowTree := .branch (1673/2000) node_350_352 node_352_354
def node_347_354 : RowTree := .branch (1671/2000) node_347_350 node_350_354
def node_341_354 : RowTree := .branch (417/500) node_341_347 node_347_354
def node_328_354 : RowTree := .branch (831/1000) node_328_341 node_341_354
def node_303_354 : RowTree := .branch (1649/2000) node_303_328 node_328_354
def node_354_355 : RowTree := .leaf (rows44[2]!)
def node_355_356 : RowTree := .leaf (rows44[3]!)
def node_356_357 : RowTree := .leaf (rows44[4]!)
def node_355_357 : RowTree := .branch (1677/2000) node_355_356 node_356_357
def node_354_357 : RowTree := .branch (419/500) node_354_355 node_355_357
def node_357_358 : RowTree := .leaf (rows44[5]!)
def node_358_359 : RowTree := .leaf (rows44[6]!)
def node_359_360 : RowTree := .leaf (rows44[7]!)
def node_358_360 : RowTree := .branch (21/25) node_358_359 node_359_360
def node_357_360 : RowTree := .branch (1679/2000) node_357_358 node_358_360
def node_354_360 : RowTree := .branch (839/1000) node_354_357 node_357_360
def node_360_361 : RowTree := .leaf (rows45[0]!)
def node_361_362 : RowTree := .leaf (rows45[1]!)
def node_362_363 : RowTree := .leaf (rows45[2]!)
def node_361_363 : RowTree := .branch (1683/2000) node_361_362 node_362_363
def node_360_363 : RowTree := .branch (841/1000) node_360_361 node_361_363
def node_363_364 : RowTree := .leaf (rows45[3]!)
def node_364_365 : RowTree := .leaf (rows45[4]!)
def node_365_366 : RowTree := .leaf (rows45[5]!)
def node_364_366 : RowTree := .branch (843/1000) node_364_365 node_365_366
def node_363_366 : RowTree := .branch (337/400) node_363_364 node_364_366
def node_360_366 : RowTree := .branch (421/500) node_360_363 node_363_366
def node_354_366 : RowTree := .branch (1681/2000) node_354_360 node_360_366
def node_366_367 : RowTree := .leaf (rows45[6]!)
def node_367_368 : RowTree := .leaf (rows45[7]!)
def node_368_369 : RowTree := .leaf (rows46[0]!)
def node_367_369 : RowTree := .branch (1689/2000) node_367_368 node_368_369
def node_366_369 : RowTree := .branch (211/250) node_366_367 node_367_369
def node_369_370 : RowTree := .leaf (rows46[1]!)
def node_370_371 : RowTree := .leaf (rows46[2]!)
def node_371_372 : RowTree := .leaf (rows46[3]!)
def node_370_372 : RowTree := .branch (423/500) node_370_371 node_371_372
def node_369_372 : RowTree := .branch (1691/2000) node_369_370 node_370_372
def node_366_372 : RowTree := .branch (169/200) node_366_369 node_369_372
def node_372_373 : RowTree := .leaf (rows46[4]!)
def node_373_374 : RowTree := .leaf (rows46[5]!)
def node_374_375 : RowTree := .leaf (rows46[6]!)
def node_373_375 : RowTree := .branch (339/400) node_373_374 node_374_375
def node_372_375 : RowTree := .branch (847/1000) node_372_373 node_373_375
def node_375_376 : RowTree := .leaf (rows46[7]!)
def node_376_377 : RowTree := .leaf (rows47[0]!)
def node_375_377 : RowTree := .branch (1697/2000) node_375_376 node_376_377
def node_377_378 : RowTree := .leaf (rows47[1]!)
def node_378_379 : RowTree := .leaf (rows47[2]!)
def node_377_379 : RowTree := .branch (1699/2000) node_377_378 node_378_379
def node_375_379 : RowTree := .branch (849/1000) node_375_377 node_377_379
def node_372_379 : RowTree := .branch (106/125) node_372_375 node_375_379
def node_366_379 : RowTree := .branch (1693/2000) node_366_372 node_372_379
def node_354_379 : RowTree := .branch (1687/2000) node_354_366 node_366_379
def node_379_380 : RowTree := .leaf (rows47[3]!)
def node_380_381 : RowTree := .leaf (rows47[4]!)
def node_381_382 : RowTree := .leaf (rows47[5]!)
def node_380_382 : RowTree := .branch (851/1000) node_380_381 node_381_382
def node_379_382 : RowTree := .branch (1701/2000) node_379_380 node_380_382
def node_382_383 : RowTree := .leaf (rows47[6]!)
def node_383_384 : RowTree := .leaf (rows47[7]!)
def node_384_385 : RowTree := .leaf (rows48[0]!)
def node_383_385 : RowTree := .branch (341/400) node_383_384 node_384_385
def node_382_385 : RowTree := .branch (213/250) node_382_383 node_383_385
def node_379_385 : RowTree := .branch (1703/2000) node_379_382 node_382_385
def node_385_386 : RowTree := .leaf (rows48[1]!)
def node_386_387 : RowTree := .leaf (rows48[2]!)
def node_387_388 : RowTree := .leaf (rows48[3]!)
def node_386_388 : RowTree := .branch (427/500) node_386_387 node_387_388
def node_385_388 : RowTree := .branch (1707/2000) node_385_386 node_386_388
def node_388_389 : RowTree := .leaf (rows48[4]!)
def node_389_390 : RowTree := .leaf (rows48[5]!)
def node_388_390 : RowTree := .branch (171/200) node_388_389 node_389_390
def node_390_391 : RowTree := .leaf (rows48[6]!)
def node_391_392 : RowTree := .leaf (rows48[7]!)
def node_390_392 : RowTree := .branch (107/125) node_390_391 node_391_392
def node_388_392 : RowTree := .branch (1711/2000) node_388_390 node_390_392
def node_385_392 : RowTree := .branch (1709/2000) node_385_388 node_388_392
def node_379_392 : RowTree := .branch (853/1000) node_379_385 node_385_392
def node_392_393 : RowTree := .leaf (rows49[0]!)
def node_393_394 : RowTree := .leaf (rows49[1]!)
def node_394_395 : RowTree := .leaf (rows49[2]!)
def node_393_395 : RowTree := .branch (343/400) node_393_394 node_394_395
def node_392_395 : RowTree := .branch (857/1000) node_392_393 node_393_395
def node_395_396 : RowTree := .leaf (rows49[3]!)
def node_396_397 : RowTree := .leaf (rows49[4]!)
def node_397_398 : RowTree := .leaf (rows49[5]!)
def node_396_398 : RowTree := .branch (859/1000) node_396_397 node_397_398
def node_395_398 : RowTree := .branch (1717/2000) node_395_396 node_396_398
def node_392_398 : RowTree := .branch (429/500) node_392_395 node_395_398
def node_398_399 : RowTree := .leaf (rows49[6]!)
def node_399_400 : RowTree := .leaf (rows49[7]!)
def node_400_401 : RowTree := .leaf (rows50[0]!)
def node_399_401 : RowTree := .branch (1721/2000) node_399_400 node_400_401
def node_398_401 : RowTree := .branch (43/50) node_398_399 node_399_401
def node_401_402 : RowTree := .leaf (rows50[1]!)
def node_402_403 : RowTree := .leaf (rows50[2]!)
def node_401_403 : RowTree := .branch (1723/2000) node_401_402 node_402_403
def node_403_404 : RowTree := .leaf (rows50[3]!)
def node_404_405 : RowTree := .leaf (rows50[4]!)
def node_403_405 : RowTree := .branch (539/625) node_403_404 node_404_405
def node_401_405 : RowTree := .branch (431/500) node_401_403 node_403_405
def node_398_405 : RowTree := .branch (861/1000) node_398_401 node_401_405
def node_392_405 : RowTree := .branch (1719/2000) node_392_398 node_398_405
def node_379_405 : RowTree := .branch (1713/2000) node_379_392 node_392_405
def node_354_405 : RowTree := .branch (17/20) node_354_379 node_379_405
def node_303_405 : RowTree := .branch (67/80) node_303_354 node_354_405
def node_202_405 : RowTree := .branch (203/250) node_202_303 node_303_405
def node_0_405 : RowTree := .branch (7463813/22000000) node_0_202 node_202_405
def quickRow (x : ℚ) : Piece := node_0_405.lookup x
def quickScore (x : ℚ) := (node_0_405.lookup x).qvalue x
def quickJ (x : ℚ) := (node_0_405.lookup x).qprimitive x
end
end StableVotingDistortion.PaperCurve

namespace StableVotingDistortion.PaperCurve
open Set MeasureTheory
open StableVotingDistortion.PaperBox
open StableVotingDistortion.PaperBox.Bounds
noncomputable section
set_option maxRecDepth 100000
def quickTotalScore (q : ℚ) : ℚ := quickScore (qclamp q)
def quickTotalJ (q : ℚ) : ℚ := quickJ (qclamp q)
def quickTotalScoreBox (i : Bounds) : Bounds :=
  ⟨quickTotalScore i.hi,quickTotalScore i.lo⟩
def quickTotalPrimitiveBox (i : Bounds) : Bounds :=
  unimodalRange (fun q => point (quickJ q)) lamQ (clampBox i)
def quickTotalPrimitiveSlope (i : Bounds) : Bounds :=
  (quickTotalScoreBox i).times (clampSlopeBox i)
end
end StableVotingDistortion.PaperCurve

namespace StableVotingDistortion.PaperMiddle
open Set MeasureTheory
open StableVotingDistortion.PaperBox
open StableVotingDistortion.PaperBox.Bounds
noncomputable section
set_option maxRecDepth 100000
def qRank (k : Knot) : ℚ := (k.position:ℚ)/1000
def qValue (col : Knot → ℕ) (k : Knot) : ℚ := (col k:ℚ)/1000000
def qSlope (col : Knot → ℕ) (k l : Knot) : ℚ :=
  (qValue col l-qValue col k)/(qRank l-qRank k)
def lineRange (col : Knot → ℕ) (k l : Knot) (i : Bounds) : Bounds :=
  (point (qValue col k)).plus ((point (qSlope col k l)).times (i.minus (point (qRank k))))
end
end StableVotingDistortion.PaperMiddle

namespace StableVotingDistortion.PaperMiddle
open Set MeasureTheory
open StableVotingDistortion.PaperBox
open StableVotingDistortion.PaperBox.Bounds
open StableVotingDistortion.PaperCurve
noncomputable section
set_option maxRecDepth 100000
def physicalXBox (p q z : Bounds) : Bounds := (z.minus p).plus q
end
end StableVotingDistortion.PaperMiddle

namespace StableVotingDistortion.PaperMiddle
open Set MeasureTheory
open StableVotingDistortion.PaperBox
open StableVotingDistortion.PaperBox.Bounds
open StableVotingDistortion.PaperCurve
noncomputable section
set_option maxRecDepth 100000
def affineEntry (col : Knot → ℕ) (k l : Knot) (p : ℚ) : ℚ :=
  qValue col k+qSlope col k l*(p-qRank k)
def fastPenaltyBox (k l : Knot) (i : Bounds) : Bounds :=
  (point 1).plus (((lineRange Knot.eta k l i).minus (point 1)).posPart)
def fastPenaltySlope (k l : Knot) (i : Bounds) : Bounds :=
  (clipSlope ((lineRange Knot.eta k l i).minus (point 1))).times (point (qSlope Knot.eta k l))
def cellKBox (p q z : Bounds) : Bounds :=
  ((quickTotalPrimitiveBox (physicalXBox p q z)).minus (quickTotalPrimitiveBox z)).minus (quickTotalPrimitiveBox q)
def cellP (k l : Knot) (p q z : Bounds) : Bounds :=
  (((point (qSlope Knot.beta k l)).times (cellKBox p q z)).minus
    ((lineRange Knot.beta k l p).times (quickTotalPrimitiveSlope (physicalXBox p q z)))).plus
    ((fastPenaltySlope k l p).times (quickTotalScoreBox z))
def cellQ (k l : Knot) (p q z : Bounds) : Bounds :=
  (point 1).plus ((lineRange Knot.beta k l p).times
    ((quickTotalPrimitiveSlope (physicalXBox p q z)).minus (quickTotalPrimitiveSlope q)))
def cellZ (scoreSlope : Bounds → Bounds) (k l : Knot) (p q z : Bounds) : Bounds :=
  ((point 1).plus ((lineRange Knot.beta k l p).times
    ((quickTotalPrimitiveSlope (physicalXBox p q z)).minus (quickTotalPrimitiveSlope z)))).plus
    ((fastPenaltyBox k l p).times (scoreSlope z))
def cellPoint (k l : Knot) (p q z : ℚ) : ℚ :=
  q+affineEntry Knot.beta k l p*(quickTotalJ (z-p+q)-quickTotalJ z-quickTotalJ q)+z-PaperCurve.lamQ+
    (1+max (affineEntry Knot.eta k l p-1) 0)*quickTotalScore z
end
end StableVotingDistortion.PaperMiddle

namespace StableVotingDistortion.PaperMiddle
open Set MeasureTheory
open StableVotingDistortion.PaperBox
open StableVotingDistortion.PaperBox.Bounds
open StableVotingDistortion.PaperCurve
noncomputable section
set_option maxRecDepth 100000
def fastCellAccept (S : Bounds → Bounds) (k l : Knot) (b c d : Bounds) : Bool :=
  let s := cellP k l b c d
  let t := cellQ k l b c d
  let v := cellZ S k l b c d
  decide (d.hi<b.lo ∨ b.hi<c.lo ∨
    (qRank k ≤ b.lo ∧ b.hi ≤ qRank l ∧ PaperCurve.lamQ ≤ d.lo ∧ d.hi ≤ 1 ∧
      ((d.hi=1 ∧ 0 ≤ v.lo) ∨ cellPoint k l (anchor b s) (anchor c t) (anchor d v)+
        deviation b s+deviation c t+deviation d v ≤ 0)))
def fastRectTest (S : Bounds → Bounds) (k l : Knot) (b : Box 3) := fastCellAccept S k l (b 0) (b 1) (b 2)
end
end StableVotingDistortion.PaperMiddle

namespace StableVotingDistortion.PaperCurve
open Set MeasureTheory
open StableVotingDistortion.PaperBox
open StableVotingDistortion.PaperBox.Bounds
noncomputable section
set_option maxRecDepth 100000
def Piece.qslope (r : Piece) (x : ℚ) : ℚ := qhorner r.slopeCoeffs (x-r.lo)
def endpointSlope (row : ℚ → Piece) (i : Bounds) : Bounds :=
  let upper := if i.lo ≤ lamQ then -1 else (row i.lo).qslope i.lo
  ⟨min ((row i.hi).qslope i.hi) upper,upper⟩
end
end StableVotingDistortion.PaperCurve

namespace StableVotingDistortion.PaperCurve
open Set MeasureTheory
open StableVotingDistortion.PaperBox
open StableVotingDistortion.PaperBox.Bounds
open StableVotingDistortion.PaperCurve
noncomputable section
set_option maxRecDepth 100000
def fastHighSlope (i : Bounds) : Bounds := endpointSlope quickRow i
end
end StableVotingDistortion.PaperCurve

namespace StableVotingDistortion.PaperMiddle
open Set MeasureTheory
open StableVotingDistortion.PaperBox
open StableVotingDistortion.PaperBox.Bounds
noncomputable section
set_option maxRecDepth 100000
def RectWitness (k l : Knot) (p P q Q z Z : ℚ) : Prop :=
  ∃ t : Cover 3, t.verify (fastRectTest PaperCurve.fastHighSlope k l)
    ![⟨p,P⟩,⟨q,Q⟩,⟨z,Z⟩]=true
end
end StableVotingDistortion.PaperMiddle


