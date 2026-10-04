-- Prove2me | Definitions.Def_Yukon_6221f05308e547988ab7c53a
-- name    : Yukon_6221f05308e547988ab7c53a
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T00:19:23.520387+00:00
-- url     : https://prove2.me/theorems/a482e1ee-6fc2-41f4-867c-a91ef99af4b7
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberArithmetic6814F.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberArithmetic6814F.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberArithmetic6814F.lean
--
--   yukon-proof-operation:certificate-r12-pair-split-e03e0e90eb7236adf907172e50827c891754e9ca6e7bb785d7369643e36fcadd-infrastructure-retry
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNzNiZTBiNDJjMTA3NDEyODFlZjYyM2RlNmI5MTAxNmJkYTk2YjI1MTFhMTY2YTY1N2MzMGZmM2Y1MmU3MTdiYyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMi1wYWlyLXNwbGl0LWUwM2UwZTkwZWI3MjM2YWRmOTA3MTcyZTUwODI3Yzg5MTc1NGU5Y2E2ZTdiYjc4NWQ3MzY5NjQzZTM2ZmNhZGQtaW5mcmFzdHJ1Y3R1cmUtcmV0cnkiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl82MjIxZjA1MzA4ZTU0Nzk4OGFiN2M1M2EiLCJ2IjoyfQ]

import Definitions.Def_Yukon_a79f98a09bde8d3ca4407ea7






































































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G20
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source31,source32,source33]
def scale : ℕ := 840
def denominator : ℕ := 35409830400
def gLo0 (b c : ℕ) : ℕ :=
    211060019056110*b +
    1854450095271620
def identitySlackLo0 (b c : ℕ) : ℕ :=
    10591835996311824240*b +
    87226980123659176080
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10112107805696567212272*b^2 +
    20265793758681343592544*b*c +
    2337484114491377792132592*b +
    187227010253976490593936*c +
    6230917034745601991771592
def gLo1 (b c : ℕ) : ℕ :=
    211060019056110*b +
    212004936109640*c +
    21072391317177060
def identitySlackLo1 (b c : ℕ) : ℕ :=
    10591835996311824240*b +
    10639255713726173760*c +
    1045823398946309975040
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10109853092177199599472*b^2 +
    20263539045161975979744*b*c +
    2337461469963654972702192*b +
    187211336355237683328336*c +
    6230859896379155160395592
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    11310957592667845*b +
    720542160717800*c +
    35183559867987090
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482813917916037120*b^2 +
    965627835832074240*b*c +
    562959701064481691880*b +
    33824990410481354400*c +
    1746974171539026808560
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10105246688212900175472*b^2 +
    20258932641197676555744*b*c +
    2337406404753986438305392*b +
    187184570717308006953936*c +
    6230699489810308713765192
def conductorLo (b c : ℕ) : ℕ :=
    20080306376879472*b^2 +
    40160612753758944*b*c +
    2304954026157346992*b +
    242638195822613136*c +
    7843486960186398792
def slopeLo (b : ℕ) : ℕ :=
    20277091570509572706144*b +
    187303900849833128222736
def interceptLo (b : ℕ) : ℕ :=
    10123405617524796325872*b^2 +
    2338072023529855703223792*b +
    6233575450343713975422792
def gHi0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    758372853156212*a +
    225491329371630*b +
    2598391564711992
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    482813917916037120*a^2 +
    965627835832074240*a*b +
    35723485879810622208*a +
    11316056873185879920*b +
    122226241443074083728
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    402074229067500447360*a^3 +
    1209713856522812484480*a^2*b +
    1213205025843123626880*a^2*c +
    391166184089862100566504*a^2 +
    1213205025843123626880*a*b^2 +
    2429901221006558396160*a*b*c +
    871214291183050672581648*a*b +
    68018676115084604582256*a*c +
    4204998397664937944700768*a +
    11122530986014955248752*b^2 +
    22290131288638430807904*b*c +
    3206880343187173251999360*b +
    253424132712485571318912*c +
    10044745752670379478254016
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    9214246581785476*a +
    225491329371630*b +
    226436246425160*c +
    30272206515246696
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482813917916037120*a^2 +
    965627835832074240*a*b +
    965627835832074240*a*c +
    457738355694360885984*a +
    11316056873185879920*b +
    11363476590600229440*c +
    1502837530080275146464
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401346902125768959360*a^3 +
    1208259202639349508480*a^2*b +
    1212477698901392138880*a^2*c +
    391154445481238710873704*a^2 +
    1212477698901392138880*a*b^2 +
    2429173894064826908160*a*b*c +
    871199570533966183788048*a*b +
    68009729992776456191856*a*c +
    4204936036981003714620768*a +
    11119548945553856147952*b^2 +
    22287149248177331707104*b*c +
    3206844432664249406751360*b +
    253400240018380347150912*c +
    10044637264901680075002816
def gHi2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    9214246581785476*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    11330199339755205*b +
    739783907805160*c +
    44388185576228886
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    482813917916037120*a^2 +
    965627835832074240*a*b +
    965627835832074240*a*c +
    457738355694360885984*a +
    482813917916037120*b^2 +
    965627835832074240*b*c +
    563925328900313766120*b +
    34790618246313428640*c +
    2204229713315471657424
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    399892248242305983360*a^3 +
    1205349894872423556480*a^2*b +
    1211023045017929162880*a^2*c +
    391127671048522748742504*a^2 +
    1211023045017929162880*a*b^2 +
    2427719240181363932160*a*b*c +
    871166735043402459256848*a*b +
    67993583332820314982256*a*c +
    4204779052672596763644768*a +
    11113487887706093747952*b^2 +
    22281088190329569307104*b*c +
    3206759441271784073775360*b +
    253358782374377992542912*c +
    10044345193803259176551616
def conductorHi (a b c : ℕ) : ℕ :=
    1707338340408960*a^3 +
    5122015021226880*a^2*b +
    5122015021226880*a^2*c +
    393821201037159144*a^2 +
    5122015021226880*a*b^2 +
    10244030042453760*a*b*c +
    787642402074318288*a*b +
    100203791962740336*a*c +
    4541461871681742048*a +
    25202321398106352*b^2 +
    50404642796212704*b*c +
    3087474413210438400*b +
    337719972764126592*c +
    11992834969171390656
def slopeHi (a b : ℕ) : ℕ :=
    1216696195163434769280*a^2 +
    2433392390326869538560*a*b +
    68061830851399958092656*a +
    22304920269786971063904*b +
    253540686875337251315712
def interceptHi (a b : ℕ) : ℕ :=
    405565398387811589760*a^3 +
    1216696195163434769280*a^2*b +
    391395526548768344617704*a^2 +
    1216696195163434769280*a*b^2 +
    871458422623105456888848*a*b +
    4206985533142987758137568*a +
    11137319967163495504752*b^2 +
    3207705401327065325112960*b +
    10049165452456955342433216
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
  norm_num [cfg,scale,source31,source32,source33,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source31,source32,source33,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source31,source32,source33,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G20


