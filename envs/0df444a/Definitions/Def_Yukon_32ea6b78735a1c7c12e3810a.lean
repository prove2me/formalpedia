-- Prove2me | Definitions.Def_Yukon_32ea6b78735a1c7c12e3810a
-- name    : Yukon_32ea6b78735a1c7c12e3810a
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T21:45:36.287074+00:00
-- url     : https://prove2.me/theorems/2f62e1da-212e-4da6-9993-af48b2d5ae68
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberArithmetic6814A.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberArithmetic6814A.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberArithmetic6814A.lean
--
--   yukon-proof-operation:certificate-split-52638c9ad84bec267e2865b75dbc4fa1439b362d6cce07a5e0254fb0ffb4f080
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZjI5ZWJiNGJhYzQ4NmI4N2Y0ZGZmNzIwYjgxMWRiYmQ0ZTA4ODNkYTRiMGMyYTdlY2VkZTEzYmY0ZWFhYzc1ZCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LTUyNjM4YzlhZDg0YmVjMjY3ZTI4NjViNzVkYmM0ZmExNDM5YjM2MmQ2Y2NlMDdhNWUwMjU0ZmIwZmZiNGYwODAiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8zMmVhNmI3ODczNWExYzdjMTJlMzgxMGEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_805f46d03627d566202e2c91





































































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G0
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source0,source0,source0]
def scale : ℕ := 18
def denominator : ℕ := 16259616
def gLo0 (b c : ℕ) : ℕ :=
    5325894189560*b +
    46601779286330
def identitySlackLo0 (b c : ℕ) : ℕ :=
    267274674008879040*b +
    2213590617616931820
def helperSlackLo0 (b c : ℕ) : ℕ :=
    5368038863272832160*b^2 +
    10737680814498868416*b*c +
    862889222173617470520*b +
    100781865002298301488*c +
    2447195944991731453152
def gLo1 (b c : ℕ) : ℕ :=
    5325894189560*b +
    5325894189560*c +
    409751459760160
def identitySlackLo1 (b c : ℕ) : ℕ :=
    267274674008879040*b +
    267274674008879040*c +
    20312821108427363640
def helperSlackLo1 (b c : ℕ) : ℕ :=
    5368038863272832160*b^2 +
    10737680814498868416*b*c +
    862889222173617470520*b +
    100781865002298301488*c +
    2447195944991731453152
def gLo2 (b c : ℕ) : ℕ :=
    206161575936*b^2 +
    412323151872*b*c +
    178194171839000*b +
    18099455723173*c +
    629422122403936
def identitySlackLo2 (b c : ℕ) : ℕ :=
    10346012526772224*b^2 +
    20692025053544448*b*c +
    8842437860297773680*b +
    858273856376412672*c +
    31186685571946896024
def helperSlackLo2 (b c : ℕ) : ℕ :=
    5368038863272832160*b^2 +
    10737680814498868416*b*c +
    862889222173617470520*b +
    100781865002298301488*c +
    2447195944991731453152
def conductorLo (b c : ℕ) : ℕ :=
    13142620513440*b^2 +
    26285241026880*b*c +
    1068124033114848*b +
    167126281423056*c +
    3592622223641376
def slopeLo (b : ℕ) : ℕ :=
    10742890850346781728*b +
    100817466921315080568
def interceptLo (b : ℕ) : ℕ :=
    5373248899120745472*b^2 +
    863064193193391928932*b +
    2447941164982072329600
def gHi0 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    18821021238949*a +
    5635136553464*b +
    65113556588511
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    10346012526772224*a^2 +
    20692025053544448*a*b +
    894484900220115456*a +
    282793692799037376*b +
    3092556420114281964
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    184626203135149728*a^3 +
    555481697358653280*a^2*b +
    557084785311857376*a^2*c +
    162524837042154131040*a^2 +
    557084785311857376*a*b^2 +
    1115772658576918848*a*b*c +
    324976574066945994144*a*b +
    35953697095748665776*a*c +
    1698546912329853150480*a +
    5832009535843739520*b^2 +
    11667225247593887232*b*c +
    1187030970784195035768*b +
    135899133553725334272*c +
    3983216415415509871152
def gHi1 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    178606494990872*a +
    5635136553464*b +
    5635136553464*c +
    588048710814264
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    10346012526772224*a^2 +
    20692025053544448*a*b +
    20692025053544448*a*c +
    8863129885351318128*a +
    282793692799037376*b +
    282793692799037376*c +
    29160431896055916456
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    184626203135149728*a^3 +
    555481697358653280*a^2*b +
    557084785311857376*a^2*c +
    162524837042154131040*a^2 +
    557084785311857376*a*b^2 +
    1115772658576918848*a*b*c +
    324976574066945994144*a*b +
    35953697095748665776*a*c +
    1698546912329853150480*a +
    5832009535843739520*b^2 +
    11667225247593887232*b*c +
    1187030970784195035768*b +
    135899133553725334272*c +
    3983216415415509871152
def gHi2 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    178606494990872*a +
    206161575936*b^2 +
    412323151872*b*c +
    178606494990872*b +
    18511778875045*c +
    807822455818872
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    10346012526772224*a^2 +
    20692025053544448*a*b +
    20692025053544448*a*c +
    8863129885351318128*a +
    10346012526772224*b^2 +
    20692025053544448*b*c +
    8863129885351318128*b +
    878965881429957120*c +
    40039469444771441928
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    184626203135149728*a^3 +
    555481697358653280*a^2*b +
    557084785311857376*a^2*c +
    162524837042154131040*a^2 +
    557084785311857376*a*b^2 +
    1115772658576918848*a*b*c +
    324976574066945994144*a*b +
    35953697095748665776*a*c +
    1698546912329853150480*a +
    5832009535843739520*b^2 +
    11667225247593887232*b*c +
    1187030970784195035768*b +
    135899133553725334272*c +
    3983216415415509871152
def conductorHi (a b c : ℕ) : ℕ :=
    1065606453792*a^3 +
    3196819361376*a^2*b +
    3196819361376*a^2*c +
    183644612303040*a^2 +
    3196819361376*a*b^2 +
    6393638722752*a*b*c +
    367289224606080*a*b +
    66956640708816*a*c +
    2088649850626944*a +
    16339439874816*b^2 +
    32678879749632*b*c +
    1432216438359552*b +
    230886102770496*c +
    5498693068419072
def slopeHi (a b : ℕ) : ℕ :=
    558687873265061472*a^2 +
    1117375746530122944*a*b +
    35973602106539397264*a +
    11674038371395004640*b +
    135953037395579640744
def interceptHi (a b : ℕ) : ℕ :=
    186229291088353824*a^3 +
    558687873265061472*a^2*b +
    162595547373260547216*a^2 +
    558687873265061472*a*b^2 +
    325054097521853527728*a*b +
    1699122077968700651832*a +
    5838822659644856928*b^2 +
    1187280259082970619572*b +
    3984467693801545036872
def slope : ℕ → ℕ → ℕ
  | 0, b => slopeLo b
  | a+1, b => slopeHi a b
def intercept : ℕ → ℕ → ℕ
  | 0, b => interceptLo b
  | a+1, b => interceptHi a b
def conductor : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => conductorLo b c
  | a+1, b, c => conductorHi a b c
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq_lo (f : FlagDegree) (b c : ℕ) :
    graphDir cfg scale f 0 b c = f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c := by
  norm_num [cfg,scale,source0,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source0,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80890*identityDegree f a b c ≤ 50184*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50184*graphDir cfg scale f 0 b c = scale*131073*80890*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50184*graphDir cfg scale f (a+1) b c = scale*131073*80890*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50184*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source0,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source0,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source0,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50184
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50184) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50184)*50184 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem full_cap_rounded (a b c : ℕ) : full a b c/denominator ≤ rounded a b c := by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0 < denominator by decide +kernel)).mpr
  have hs := Nat.lt_mul_div_succ (slope a b) (show 0 < denominator by decide +kernel)
  have hi := Nat.lt_mul_div_succ (intercept a b) (show 0 < denominator by decide +kernel)
  have hm := Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G0

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G1
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source1,source1,source1]
def scale : ℕ := 21
def denominator : ℕ := 22131144
def gLo0 (b c : ℕ) : ℕ :=
    5583598518800*b +
    47160143516040
def identitySlackLo0 (b c : ℕ) : ℕ :=
    280207308067459200*b +
    2220766055772656310
def helperSlackLo0 (b c : ℕ) : ℕ :=
    6642512081832485358*b^2 +
    13287312213002501022*b*c +
    1624767250472611949916*b +
    119337647553391444398*c +
    4632386337011535211044
def gLo1 (b c : ℕ) : ℕ :=
    5583598518800*b +
    5583598518800*c +
    662216728304360
def identitySlackLo1 (b c : ℕ) : ℕ :=
    280207308067459200*b +
    280207308067459200*c +
    32940847120353412140
def helperSlackLo1 (b c : ℕ) : ℕ :=
    6642512081832485358*b^2 +
    13287312213002501022*b*c +
    1624767250472611949916*b +
    119337647553391444398*c +
    4632386337011535211044
def gLo2 (b c : ℕ) : ℕ :=
    240521838592*b^2 +
    481043677184*b*c +
    289282056022884*b +
    18297029134004*c +
    1022888262741392
def identitySlackLo2 (b c : ℕ) : ℕ :=
    12070347947900928*b^2 +
    24140695895801856*b*c +
    14400595830303374616*b +
    859850675486338716*c +
    50865684655513083228
def helperSlackLo2 (b c : ℕ) : ℕ :=
    6642512081832485358*b^2 +
    13287312213002501022*b*c +
    1624767250472611949916*b +
    119337647553391444398*c +
    4632386337011535211044
def conductorLo (b c : ℕ) : ℕ :=
    14741035614000*b^2 +
    29482071228000*b*c +
    1702711803076272*b +
    176716793705904*c +
    5795297652979728
def slopeLo (b : ℕ) : ℕ :=
    13294691550932151744*b +
    119387461883040119556
def interceptLo (b : ℕ) : ℕ :=
    6649891419762136080*b^2 +
    1625105887614025290504*b +
    4633895872258293394080
def gHi0 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    19138855569076*a +
    5944381276688*b +
    65938214492220
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    12070347947900928*a^2 +
    24140695895801856*a*b +
    902096893303991964*a +
    298312829989310592*b +
    3104757335066755410
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    251205653420538012*a^3 +
    755889856954524936*a^2*b +
    758162753647435836*a^2*c +
    307057052432929264686*a^2 +
    758162753647435836*a*b^2 +
    1518598403987782572*a*b*c +
    613944545371891887096*a*b +
    42994555518175494732*a*c +
    3217114779400344224214*a +
    7273936182026961450*b^2 +
    14552433310084364106*b*c +
    2237575688093341561932*b +
    161193822423711753150*c +
    7542441788457767047272
def gHi1 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    289763099700068*a +
    5944381276688*b +
    5944381276688*c +
    951619043411532
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    12070347947900928*a^2 +
    24140695895801856*a*b +
    24140695895801856*a*c +
    14424736526199176472*a +
    298312829989310592*b +
    298312829989310592*c +
    47347478032542695748
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    251205653420538012*a^3 +
    755889856954524936*a^2*b +
    758162753647435836*a^2*c +
    307057052432929264686*a^2 +
    758162753647435836*a*b^2 +
    1518598403987782572*a*b*c +
    613944545371891887096*a*b +
    42994555518175494732*a*c +
    3217114779400344224214*a +
    7273936182026961450*b^2 +
    14552433310084364106*b*c +
    2237575688093341561932*b +
    161193822423711753150*c +
    7542441788457767047272
def gHi2 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    289763099700068*a +
    240521838592*b^2 +
    481043677184*b*c +
    289763099700068*b +
    18778072811188*c +
    1312410840602868
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    12070347947900928*a^2 +
    24140695895801856*a*b +
    24140695895801856*a*c +
    14424736526199176472*a +
    12070347947900928*b^2 +
    24140695895801856*b*c +
    14424736526199176472*b +
    883991371382140572*c +
    65278350833764358772
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    251205653420538012*a^3 +
    755889856954524936*a^2*b +
    758162753647435836*a^2*c +
    307057052432929264686*a^2 +
    758162753647435836*a*b^2 +
    1518598403987782572*a*b*c +
    613944545371891887096*a*b +
    42994555518175494732*a*c +
    3217114779400344224214*a +
    7273936182026961450*b^2 +
    14552433310084364106*b*c +
    2237575688093341561932*b +
    161193822423711753150*c +
    7542441788457767047272
def conductorHi (a b c : ℕ) : ℕ :=
    1243207529424*a^3 +
    3729622588272*a^2*b +
    3729622588272*a^2*c +
    290741245083936*a^2 +
    3729622588272*a*b^2 +
    7459245176544*a*b*c +
    581482490167872*a*b +
    72817487044416*a*c +
    3354628527829440*a +
    18470658202272*b^2 +
    36941316404544*b*c +
    2280464670655872*b +
    245804658162048*c +
    8860428143254656
def slopeHi (a b : ℕ) : ℕ :=
    760435650340346736*a^2 +
    1520871300680693472*a*b +
    43022542455677697264*a +
    14562085544706925728*b +
    161269350794169719940
def interceptHi (a b : ℕ) : ℕ :=
    253478550113448912*a^3 +
    760435650340346736*a^2*b +
    307190257931102973696*a^2 +
    760435650340346736*a*b^2 +
    614087403104688157728*a*b +
    3218251501444174354944*a +
    7283588416649523072*b^2 +
    2238052637174165351352*b +
    7544957113146874562928
def slope : ℕ → ℕ → ℕ
  | 0, b => slopeLo b
  | a+1, b => slopeHi a b
def intercept : ℕ → ℕ → ℕ
  | 0, b => interceptLo b
  | a+1, b => interceptHi a b
def conductor : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => conductorLo b c
  | a+1, b, c => conductorHi a b c
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq_lo (f : FlagDegree) (b c : ℕ) :
    graphDir cfg scale f 0 b c = f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c := by
  norm_num [cfg,scale,source1,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source1,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80890*identityDegree f a b c ≤ 50184*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50184*graphDir cfg scale f 0 b c = scale*131073*80890*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50184*graphDir cfg scale f (a+1) b c = scale*131073*80890*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50184*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source1,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source1,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source1,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50184
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50184) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50184)*50184 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem full_cap_rounded (a b c : ℕ) : full a b c/denominator ≤ rounded a b c := by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0 < denominator by decide +kernel)).mpr
  have hs := Nat.lt_mul_div_succ (slope a b) (show 0 < denominator by decide +kernel)
  have hi := Nat.lt_mul_div_succ (intercept a b) (show 0 < denominator by decide +kernel)
  have hm := Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G1

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G2
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source2,source2,source2]
def scale : ℕ := 21
def denominator : ℕ := 22131144
def gLo0 (b c : ℕ) : ℕ :=
    5583598518800*b +
    48233915486690
def identitySlackLo0 (b c : ℕ) : ℕ :=
    280207308067459200*b +
    2274652228347755910
def helperSlackLo0 (b c : ℕ) : ℕ :=
    6642512081832485358*b^2 +
    13287312213002501022*b*c +
    1479803677491696821622*b +
    121963814335572045768*c +
    4214893533844490719164
def gLo1 (b c : ℕ) : ℕ :=
    5583598518800*b +
    5583598518800*c +
    602944515524480
def identitySlackLo1 (b c : ℕ) : ℕ :=
    280207308067459200*b +
    280207308067459200*c +
    29966330394207914220
def helperSlackLo1 (b c : ℕ) : ℕ :=
    6642512081832485358*b^2 +
    13287312213002501022*b*c +
    1479803677491696821622*b +
    121963814335572045768*c +
    4214893533844490719164
def gLo2 (b c : ℕ) : ℕ :=
    240521838592*b^2 +
    481043677184*b*c +
    263202345345456*b +
    18769487660769*c +
    930423204185792
def identitySlackLo2 (b c : ℕ) : ℕ :=
    12070347947900928*b^2 +
    24140695895801856*b*c +
    13091811629667327864*b +
    883560534193513476*c +
    46225418156958852828
def helperSlackLo2 (b c : ℕ) : ℕ :=
    6642512081832485358*b^2 +
    13287312213002501022*b*c +
    1479803677491696821622*b +
    121963814335572045768*c +
    4214893533844490719164
def conductorLo (b c : ℕ) : ℕ :=
    14741035614000*b^2 +
    29482071228000*b*c +
    1555653624798960*b +
    179380891138464*c +
    5280594029009136
def slopeLo (b : ℕ) : ℕ :=
    13294691550932151744*b +
    122014045362947754591
def interceptLo (b : ℕ) : ℕ :=
    6649891419762136080*b^2 +
    1480119729616304937567*b +
    4216290170813052355476
def gHi0 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    19611314095841*a +
    5944381276688*b +
    67484444989635
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    12070347947900928*a^2 +
    24140695895801856*a*b +
    925806752011166724*a +
    298312829989310592*b +
    3182353366349029770
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    251205653420538012*a^3 +
    755889856954524936*a^2*b +
    758162753647435836*a^2*c +
    279556134243108467238*a^2 +
    758162753647435836*a*b^2 +
    1518598403987782572*a*b*c +
    558959134459017728304*a*b +
    43990673524801700292*a*c +
    2927117480890420507626*a +
    7273936182026961450*b^2 +
    14552433310084364106*b*c +
    2037626704199552274846*b +
    164816107212518560080*c +
    6862452604970619636252
def gHi1 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    263683389022640*a +
    5944381276688*b +
    5944381276688*c +
    866267119954224
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    12070347947900928*a^2 +
    24140695895801856*a*b +
    24140695895801856*a*c +
    13115952325563129720*a +
    298312829989310592*b +
    298312829989310592*c +
    43064177105761151076
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    251205653420538012*a^3 +
    755889856954524936*a^2*b +
    758162753647435836*a^2*c +
    279556134243108467238*a^2 +
    758162753647435836*a*b^2 +
    1518598403987782572*a*b*c +
    558959134459017728304*a*b +
    43990673524801700292*a*c +
    2927117480890420507626*a +
    7273936182026961450*b^2 +
    14552433310084364106*b*c +
    2037626704199552274846*b +
    164816107212518560080*c +
    6862452604970619636252
def gHi2 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    263683389022640*a +
    240521838592*b^2 +
    481043677184*b*c +
    263683389022640*b +
    19250531337953*c +
    1193866071369840
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    12070347947900928*a^2 +
    24140695895801856*a*b +
    24140695895801856*a*c +
    13115952325563129720*a +
    12070347947900928*b^2 +
    24140695895801856*b*c +
    13115952325563129720*b +
    907701230089315332*c +
    59329300134574081620
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    251205653420538012*a^3 +
    755889856954524936*a^2*b +
    758162753647435836*a^2*c +
    279556134243108467238*a^2 +
    758162753647435836*a*b^2 +
    1518598403987782572*a*b*c +
    558959134459017728304*a*b +
    43990673524801700292*a*c +
    2927117480890420507626*a +
    7273936182026961450*b^2 +
    14552433310084364106*b*c +
    2037626704199552274846*b +
    164816107212518560080*c +
    6862452604970619636252
def conductorHi (a b c : ℕ) : ℕ :=
    1243207529424*a^3 +
    3729622588272*a^2*b +
    3729622588272*a^2*c +
    266231548704384*a^2 +
    3729622588272*a*b^2 +
    7459245176544*a*b*c +
    532463097408768*a*b +
    73705519521936*a*c +
    3060512171274816*a +
    18470658202272*b^2 +
    36941316404544*b*c +
    2084387099619456*b +
    249356788072128*c +
    8076117859108992
def slopeHi (a b : ℕ) : ℕ :=
    760435650340346736*a^2 +
    1520871300680693472*a*b +
    44018811988750096884*a +
    14562085544706925728*b +
    164892203807149754595
def interceptHi (a b : ℕ) : ℕ :=
    253478550113448912*a^3 +
    760435650340346736*a^2*b +
    279681127007898458196*a^2 +
    760435650340346736*a*b^2 +
    559093779458430280884*a*b +
    2928174137719035912846*a +
    7283588416649523072*b^2 +
    2038072855530187121571*b +
    6864783178899699597726
def slope : ℕ → ℕ → ℕ
  | 0, b => slopeLo b
  | a+1, b => slopeHi a b
def intercept : ℕ → ℕ → ℕ
  | 0, b => interceptLo b
  | a+1, b => interceptHi a b
def conductor : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => conductorLo b c
  | a+1, b, c => conductorHi a b c
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq_lo (f : FlagDegree) (b c : ℕ) :
    graphDir cfg scale f 0 b c = f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c := by
  norm_num [cfg,scale,source2,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source2,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80890*identityDegree f a b c ≤ 50184*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50184*graphDir cfg scale f 0 b c = scale*131073*80890*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50184*graphDir cfg scale f (a+1) b c = scale*131073*80890*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50184*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source2,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source2,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source2,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50184
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50184) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50184)*50184 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem full_cap_rounded (a b c : ℕ) : full a b c/denominator ≤ rounded a b c := by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0 < denominator by decide +kernel)).mpr
  have hs := Nat.lt_mul_div_succ (slope a b) (show 0 < denominator by decide +kernel)
  have hi := Nat.lt_mul_div_succ (intercept a b) (show 0 < denominator by decide +kernel)
  have hm := Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G2

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G3
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source3,source3,source3]
def scale : ℕ := 18
def denominator : ℕ := 16259616
def gLo0 (b c : ℕ) : ℕ :=
    4569960546736*b +
    40915071143710
def identitySlackLo0 (b c : ℕ) : ℕ :=
    229338900077399424*b +
    1928208856187689740
def helperSlackLo0 (b c : ℕ) : ℕ :=
    4685338945298214648*b^2 +
    9372136255331635800*b*c +
    1379259827639337076344*b +
    88643674293001737912*c +
    3938982583018274060976
def gLo1 (b c : ℕ) : ℕ :=
    4569960546736*b +
    4569960546736*c +
    656186410326160
def identitySlackLo1 (b c : ℕ) : ℕ :=
    229338900077399424*b +
    229338900077399424*c +
    32679912667631507640
def helperSlackLo1 (b c : ℕ) : ℕ :=
    4685338945298214648*b^2 +
    9372136255331635800*b*c +
    1379259827639337076344*b +
    88643674293001737912*c +
    3938982583018274060976
def gLo2 (b c : ℕ) : ℕ :=
    206161575936*b^2 +
    412323151872*b*c +
    287048616405656*b +
    16020638205407*c +
    1015363236375136
def identitySlackLo2 (b c : ℕ) : ℕ :=
    10346012526772224*b^2 +
    20692025053544448*b*c +
    14305189306430838384*b +
    753950478064843728*c +
    50554754435477596824
def helperSlackLo2 (b c : ℕ) : ℕ :=
    4685338945298214648*b^2 +
    9372136255331635800*b*c +
    1379259827639337076344*b +
    88643674293001737912*c +
    3938982583018274060976
def conductorLo (b c : ℕ) : ℕ :=
    12432194531424*b^2 +
    24864389062848*b*c +
    1679090377648608*b +
    152562548791728*c +
    5738108689329696
def slopeLo (b : ℕ) : ℕ :=
    9376667205310483488*b +
    88674717429674836848
def interceptLo (b : ℕ) : ℕ :=
    4689869895277062336*b^2 +
    1379497533753020275836*b +
    3940058380800915761760
def gHi0 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    16742203721183*a +
    4879202910640*b +
    57348030928125
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    10346012526772224*a^2 +
    20692025053544448*a*b +
    790161521908546512*a +
    244857918867557760*b +
    2702851280373470940
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    184826589129300240*a^3 +
    555882469346954304*a^2*b +
    557285171306007888*a^2*c +
    260907408565963774200*a^2 +
    557285171306007888*a*b^2 +
    1115973044571069360*a*b*c +
    521689119031704360384*a*b +
    32198552534429464896*a*c +
    2735980718316416301096*a +
    5149510003863272520*b^2 +
    10301881074420805128*b*c +
    1900113720442684706808*b +
    120005597897115419304*c +
    6414054488290800136944
def gHi1 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    287460939557528*a +
    4879202910640*b +
    4879202910640*c +
    943338105946920
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    10346012526772224*a^2 +
    20692025053544448*a*b +
    20692025053544448*a*c +
    14325881331484382832*a +
    244857918867557760*b +
    244857918867557760*c +
    46990274901393125160
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    184826589129300240*a^3 +
    555882469346954304*a^2*b +
    557285171306007888*a^2*c +
    260907408565963774200*a^2 +
    557285171306007888*a*b^2 +
    1115973044571069360*a*b*c +
    521689119031704360384*a*b +
    32198552534429464896*a*c +
    2735980718316416301096*a +
    5149510003863272520*b^2 +
    10301881074420805128*b*c +
    1900113720442684706808*b +
    120005597897115419304*c +
    6414054488290800136944
def gHi2 (a b c : ℕ) : ℕ :=
    206161575936*a^2 +
    412323151872*a*b +
    412323151872*a*c +
    287460939557528*a +
    206161575936*b^2 +
    412323151872*b*c +
    287460939557528*b +
    16432961357279*c +
    1302618014356728
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    10346012526772224*a^2 +
    20692025053544448*a*b +
    20692025053544448*a*c +
    14325881331484382832*a +
    10346012526772224*b^2 +
    20692025053544448*b*c +
    14325881331484382832*b +
    774642503118388176*c +
    64870289754435207432
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    184826589129300240*a^3 +
    555882469346954304*a^2*b +
    557285171306007888*a^2*c +
    260907408565963774200*a^2 +
    557285171306007888*a*b^2 +
    1115973044571069360*a*b*c +
    521689119031704360384*a*b +
    32198552534429464896*a*c +
    2735980718316416301096*a +
    5149510003863272520*b^2 +
    10301881074420805128*b*c +
    1900113720442684706808*b +
    120005597897115419304*c +
    6414054488290800136944
def conductorHi (a b c : ℕ) : ℕ :=
    1065606453792*a^3 +
    3196819361376*a^2*b +
    3196819361376*a^2*c +
    285945953713344*a^2 +
    3196819361376*a*b^2 +
    6393638722752*a*b*c +
    571891907426688*a*b +
    63049297807728*a*c +
    3316265947550592*a +
    15629013892800*b^2 +
    31258027785600*b*c +
    2247785465713920*b +
    212415027238080*c +
    8769494289620736
def slopeHi (a b : ℕ) : ℕ :=
    558687873265061472*a^2 +
    1117375746530122944*a*b +
    32215952720038509072*a +
    10307814726358706400*b +
    120052638517438508832
def interceptHi (a b : ℕ) : ℕ :=
    186229291088353824*a^3 +
    558687873265061472*a^2*b +
    261000120066809413680*a^2 +
    558687873265061472*a*b^2 +
    521787764184487901136*a*b +
    2736784614323117732904*a +
    5155443655801173792*b^2 +
    1900447266305233339884*b +
    6415842873281256683640
def slope : ℕ → ℕ → ℕ
  | 0, b => slopeLo b
  | a+1, b => slopeHi a b
def intercept : ℕ → ℕ → ℕ
  | 0, b => interceptLo b
  | a+1, b => interceptHi a b
def conductor : ℕ → ℕ → ℕ → ℕ
  | 0, b, c => conductorLo b c
  | a+1, b, c => conductorHi a b c
def full (a b c : ℕ) : ℕ := slope a b*c+intercept a b
def rounded (a b c : ℕ) : ℕ := (slope a b/denominator+1)*c+(intercept a b/denominator+1)
theorem positive : 0 < scale := by decide +kernel
theorem divides (j : Fin 3) : 3*(cfg j).d ∣ scale := by
  have h : ∀ j : Fin 3, 3*(cfg j).d ∣ scale := by decide +kernel
  exact h j
theorem graph_eq_lo (f : FlagDegree) (b c : ℕ) :
    graphDir cfg scale f 0 b c = f.zOnly*gLo0 b c+f.yz*gLo1 b c+f.all*gLo2 b c := by
  norm_num [cfg,scale,source3,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source3,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem identity_absorption (f : FlagDegree) (a b c : ℕ) :
    scale*131073*80890*identityDegree f a b c ≤ 50184*graphDir cfg scale f a b c := by
  cases a with
  | zero =>
    have he : 50184*graphDir cfg scale f 0 b c = scale*131073*80890*identityDegree f 0 b c+
        (f.zOnly*identitySlackLo0 b c+f.yz*identitySlackLo1 b c+f.all*identitySlackLo2 b c) := by
      rw [graph_eq_lo]
      simp only [scale,identityDegree,gLo0,gLo1,gLo2,identitySlackLo0,identitySlackLo1,identitySlackLo2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
  | succ a =>
    have he : 50184*graphDir cfg scale f (a+1) b c = scale*131073*80890*identityDegree f (a+1) b c+
        (f.zOnly*identitySlackHi0 a b c+f.yz*identitySlackHi1 a b c+f.all*identitySlackHi2 a b c) := by
      rw [graph_eq_hi]
      simp only [scale,identityDegree,gHi0,gHi1,gHi2,identitySlackHi0,identitySlackHi1,identitySlackHi2]
      ring
    rw [he]
    exact Nat.le_add_right _ _
theorem full_eq (a b c : ℕ) : full a b c =
    scale*50184*graphDir cfg scale ⟨c,b+2,a+3⟩ a b c+
      scale^2*(∑ j : Fin 3, coeff (cfg j) a b c)+conductor a b c := by
  cases a with
  | zero =>
    rw [graph_eq_lo]
    norm_num [cfg,scale,source3,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source3,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source3,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hh := Nat.div_mul_le_self (helper (cfg j) a b c) 50184
  dsimp only [denominator,scale] at he ⊢
  nlinarith
theorem retained_cap (a b c : ℕ) :
    graphDir cfg scale ⟨c,b+2,a+3⟩ a b c/scale+
      (∑ j : Fin 3, coeff (cfg j) a b c/50184) ≤ full a b c/denominator := by
  apply (Nat.le_div_iff_mul_le (show 0 < denominator by decide +kernel)).mpr
  have hx := Nat.div_mul_le_self (graphDir cfg scale ⟨c,b+2,a+3⟩ a b c) scale
  have hy : (∑ j : Fin 3, coeff (cfg j) a b c/50184)*50184 ≤ ∑ j : Fin 3, coeff (cfg j) a b c := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun j _ => Nat.div_mul_le_self _ _)
  rw [full_eq]
  dsimp only [denominator,scale] at hx ⊢
  nlinarith
theorem full_cap_rounded (a b c : ℕ) : full a b c/denominator ≤ rounded a b c := by
  apply Nat.le_of_lt
  apply (Nat.div_lt_iff_lt_mul (show 0 < denominator by decide +kernel)).mpr
  have hs := Nat.lt_mul_div_succ (slope a b) (show 0 < denominator by decide +kernel)
  have hi := Nat.lt_mul_div_succ (intercept a b) (show 0 < denominator by decide +kernel)
  have hm := Nat.mul_le_mul_right c (Nat.le_of_lt hs)
  unfold full rounded
  nlinarith




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G3


