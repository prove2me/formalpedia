-- Prove2me | Definitions.Def_Yukon_83e2180d30d6903afaa66681
-- name    : Yukon_83e2180d30d6903afaa66681
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T22:41:07.25177+00:00
-- url     : https://prove2.me/theorems/6c9d3219-c33f-4adf-a788-3110bbe19b6b
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberArithmetic6814C.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberArithmetic6814C.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberArithmetic6814C.lean
--
--   yukon-proof-operation:certificate-split-48d20281e27c2bf5de46bc451e9d5b69a6556f5de499b3cf3493e198ecce5004
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZWFiNzI2ZjkzYWZhOWFlYWI0NTYwNzBhMDdkNTE5ZGI2MDgwMWM2YTJjMTE4YjEzMThlOWRiMGU1ZjRlMGUyZiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LTQ4ZDIwMjgxZTI3YzJiZjVkZTQ2YmM0NTFlOWQ1YjY5YTY1NTZmNWRlNDk5YjNjZjM0OTNlMTk4ZWNjZTUwMDQiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl84M2UyMTgwZDMwZDY5MDNhZmFhNjY2ODEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_00539a3de5b1ad4051dcf52a






































































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G8
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source11,source14,source13]
def scale : ℕ := 840
def denominator : ℕ := 35409830400
def gLo0 (b c : ℕ) : ℕ :=
    223343940752000*b +
    1957274690704500
def identitySlackLo0 (b c : ℕ) : ℕ :=
    11208292322698368000*b +
    92387129620862826000
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10630931104690976299896*b^2 +
    21358211930862403769712*b*c +
    2118853712656170053876880*b +
    196242757201002580795008*c +
    5709823689303579644886600
def gLo1 (b c : ℕ) : ℕ :=
    223343940752000*b +
    225611741680472*c +
    19553175973746050
def identitySlackLo1 (b c : ℕ) : ℕ :=
    11208292322698368000*b +
    11322099644492806848*c +
    969583096151568169200
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10627197493056754661496*b^2 +
    21354478319228182131312*b*c +
    2118804745742669248436880*b +
    196216355227746076579008*c +
    5709671696614664496832200
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    10082092964552080*b +
    748511705502288*c +
    32084677751860130
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482813917916037120*b^2 +
    965627835832074240*b*c +
    501290358567120141120*b +
    35228614045946100192*c +
    1591459871423311447920
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10624845802611822850296*b^2 +
    21352126628783250320112*b*c +
    2118793126611257054027280*b +
    196203129996192795105408*c +
    5709672298721758824592200
def conductorLo (b c : ℕ) : ℕ :=
    26051649056175096*b^2 +
    52103298112350192*b*c +
    2907876896531358480*b +
    318513968395000128*c +
    9887737813754185800
def slopeLo (b : ℕ) : ℕ :=
    21367109563782918972912*b +
    196302313167992668934208
def interceptLo (b : ℕ) : ℕ :=
    10639828737611491503096*b^2 +
    2119304305481102722633680*b +
    5711855184354956965792200
def gHi0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    796736485529530*a +
    237775251067520*b +
    2739579792518190
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    482813917916037120*a^2 +
    965627835832074240*a*b +
    37648726406833212720*a +
    11932513199572423680*b +
    129311631467300324160
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    402802020140042920320*a^3 +
    1211169902798708415360*a^2*b +
    1213933745177288069760*a^2*c +
    362625516988841751516936*a^2 +
    1213933745177288069760*a*b^2 +
    2430631332733155793920*a*b*c +
    790873200496691276517072*a*b +
    70818079380014111892768*a*c +
    3874327705642621986970272*a +
    11642083004343528779256*b^2 +
    23383279572546088382832*b*c +
    2907907394619330221748192*b +
    265238554205107004387616*c +
    9221523110098134065161056
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8538914363627585*a +
    237775251067520*b +
    240043051995992*c +
    28077658953657795
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482813917916037120*a^2 +
    965627835832074240*a*b +
    965627835832074240*a*c +
    423847483658325284040*a +
    11932513199572423680*b +
    12046320521366862528*c +
    1392706355249497738680
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401638297033272539520*a^3 +
    1208842456585167653760*a^2*b +
    1212770022070517688960*a^2*c +
    362602439137241834019336*a^2 +
    1212770022070517688960*a*b^2 +
    2429467609626385413120*a*b*c +
    790845225310350367000272*a*b +
    70803387374311374094368*a*c +
    3874185735782261773008672*a +
    11637185669602536760056*b^2 +
    23378382237805096363632*b*c +
    2907832779965702047552992*b +
    265198623949254532754016*c +
    9221251061677351850261856
def gHi2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8538914363627585*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    10101334711639440*b +
    767753452589648*c +
    40613971241944035
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    482813917916037120*a^2 +
    965627835832074240*a*b +
    965627835832074240*a*c +
    423847483658325284040*a +
    482813917916037120*b^2 +
    965627835832074240*b*c +
    502255986402952215360*b +
    36194241881778174432*c +
    2014824541163720694840
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    400910970091541051520*a^3 +
    1207387802701704677760*a^2*b +
    1212042695128786200960*a^2*c +
    362594967513343269056136*a^2 +
    1212042695128786200960*a*b^2 +
    2428740282684653925120*a*b*c +
    790834674669065138737872*a*b +
    70795411021258867687968*a*c +
    3874164817295289405072672*a +
    11634106652215873460856*b^2 +
    23375303220418433064432*b*c +
    2907812064846888087856992*b +
    265178149691590476362016*c +
    9221237489594430643561056
def conductorHi (a b c : ℕ) : ℕ :=
    2171469151393920*a^3 +
    6514407454181760*a^2*b +
    6514407454181760*a^2*c +
    496593216928260936*a^2 +
    6514407454181760*a*b^2 +
    13028814908363520*a*b*c +
    993186433856521872*a*b +
    130065457811069088*a*c +
    5724599934788587872*a +
    32566056510356856*b^2 +
    65132113020713712*b*c +
    3894548922933698592*b +
    442065018751887456*c +
    15117916000765906656
def slopeHi (a b : ℕ) : ℕ :=
    1216697587555867724160*a^2 +
    2433395175111735448320*a*b +
    70851803109393496020768*a +
    23394941047845183240432*b +
    265329070059097897000416
def interceptHi (a b : ℕ) : ℕ :=
    405565862518622574720*a^3 +
    1216697587555867724160*a^2*b +
    362801808668834257356936*a^2 +
    1216697587555867724160*a*b^2 +
    791061153651982877214672*a*b +
    3875849330757196314519072*a +
    11653744479642623636856*b^2 +
    2908540412914797331893792*b +
    9224902702426471787429856
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
  norm_num [cfg,scale,source11,source13,source14,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source11,source13,source14,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source11,source13,source14,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G8

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G9
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source15,source16,source17]
def scale : ℕ := 840
def denominator : ℕ := 35409830400
def gLo0 (b c : ℕ) : ℕ :=
    230903277180240*b +
    1996961420600300
def identitySlackLo0 (b c : ℕ) : ℕ :=
    11587650062013164160*b +
    94378768473953653200
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10949785726812650070696*b^2 +
    21677066720230194140112*b*c +
    1976304409234956830113632*b +
    198587227893354887323392*c +
    5420251622777623817022432
def gLo1 (b c : ℕ) : ℕ :=
    230903277180240*b +
    225611741680472*c +
    18878804343159600
def identitySlackLo1 (b c : ℕ) : ℕ :=
    11587650062013164160*b +
    11322099644492806848*c +
    935740430242217762400
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10945591474781998489896*b^2 +
    21672872468199542559312*b*c +
    1976266817058806759070432*b +
    198557989344378234542592*c +
    5420167985447053556008032
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    9174972593163280*b +
    753803241002056*c +
    30246151240444080
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482813917916037120*b^2 +
    965627835832074240*b*c +
    455767429849344601920*b +
    35494164463466457504*c +
    1499195256974408394720
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10943239784337066678696*b^2 +
    21670520777754610748112*b*c +
    1976235596466314901059232*b +
    198545030799370254614592*c +
    5420070597393770719115232
def conductorLo (b c : ℕ) : ℕ :=
    26218895172774696*b^2 +
    52437790345549392*b*c +
    2755380348159548832*b +
    322315221016107072*c +
    9352327433286856032
def slopeLo (b : ℕ) : ℕ :=
    21685964353150709343312*b +
    198646917203617626235392
def interceptLo (b : ℕ) : ℕ :=
    10958683359733165273896*b^2 +
    1976739534240262009225632*b +
    5422205787291582415009632
def gHi0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    809965324278950*a +
    245334587495760*b +
    2792495361163410
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    482813917916037120*a^2 +
    965627835832074240*a*b +
    38312602450634106000*a +
    12311870938887219840*b +
    131967146364192044640
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    402802020140042920320*a^3 +
    1211169902798708415360*a^2*b +
    1213933745177288069760*a^2*c +
    349923449421515949121728*a^2 +
    1213933745177288069760*a*b^2 +
    2430631332733155793920*a*b*c +
    739932041232696343222656*a*b +
    71599477490092296681696*a*c +
    3707869035546322213320576*a +
    11960937626465202550056*b^2 +
    23702134361913878753232*b*c +
    2714416931934122064690528*b +
    268364423007537495704928*c +
    8778194441043204266042400
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8237958282078280*a +
    245334587495760*b +
    240043051995992*c +
    27102331241522040
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482813917916037120*a^2 +
    965627835832074240*a*b +
    965627835832074240*a*c +
    408744303661854961920*a +
    12311870938887219840*b +
    12046320521366862528*c +
    1343760509343677009760
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401492831644926241920*a^3 +
    1208551525808475058560*a^2*b +
    1212624556682171391360*a^2*c +
    349903832766032649169728*a^2 +
    1212624556682171391360*a*b^2 +
    2429322144238039115520*a*b*c +
    739906921136687275011456*a*b +
    71583112632238606243296*a*c +
    3707771215563703585915776*a +
    11955434185939434290856*b^2 +
    23696630921388110494032*b*c +
    2714356838038953158792928*b +
    268320128789202269164128*c +
    8778031291197003560896800
def gHi2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8237958282078280*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    9194214340250640*b +
    773044988089416*c +
    38474488648978680
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    482813917916037120*a^2 +
    965627835832074240*a*b +
    965627835832074240*a*c +
    408744303661854961920*a +
    482813917916037120*b^2 +
    965627835832074240*b*c +
    456733057685176676160*b +
    36459792299298531744*c +
    1907456746718347319520
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    400765504703194753920*a^3 +
    1207096871925012082560*a^2*b +
    1211897229740439903360*a^2*c +
    349889233338105115624128*a^2 +
    1211897229740439903360*a*b^2 +
    2428594817296307627520*a*b*c +
    739889242691373078166656*a*b +
    71575233256111664035296*a*c +
    3707680806702455825419776*a +
    11952355168552770991656*b^2 +
    23693551904001447194832*b*c +
    2714309393655030566912928*b +
    268300018195009078516128*c +
    8777857366383458765565600
def conductorHi (a b c : ℕ) : ℕ :=
    2171469151393920*a^3 +
    6514407454181760*a^2*b +
    6514407454181760*a^2*c +
    471065628121892928*a^2 +
    6514407454181760*a*b^2 +
    13028814908363520*a*b*c +
    942131256243785856*a*b +
    131109547195971936*a*c +
    5418268869112171776*a +
    32733302626956456*b^2 +
    65466605253912912*b*c +
    3690997196949152928*b +
    446910360757897248*c +
    14301702143428528800
def slopeHi (a b : ℕ) : ℕ :=
    1216697587555867724160*a^2 +
    2433395175111735448320*a*b +
    71633249707934462908896*a +
    23713795837212973610832*b +
    268455120693263821189728
def interceptHi (a b : ℕ) : ℕ :=
    405565862518622574720*a^3 +
    1216697587555867724160*a^2*b +
    350094116439825731454528*a^2 +
    1216697587555867724160*a*b^2 +
    740114369726305220413056*a*b +
    3709335823063062895109376*a +
    11972599101764297407656*b^2 +
    2715028857748278961684128*b +
    8781447489897972343140000
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
  norm_num [cfg,scale,source15,source16,source17,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source15,source16,source17,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source15,source16,source17,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G9

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G10
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source18,source19,source20]
def scale : ℕ := 216
def denominator : ℕ := 2341384704
def gLo0 (b c : ℕ) : ℕ :=
    57674277721422*b +
    497165824473180
def identitySlackLo0 (b c : ℕ) : ℕ :=
    2894325953171841648*b +
    23448892846303030320
def helperSlackLo0 (b c : ℕ) : ℕ :=
    705552730581557910096*b^2 +
    1392742417078264115232*b*c +
    134392705166619964429344*b +
    12747676493095359668352*c +
    370543814348217000508656
def gLo1 (b c : ℕ) : ℕ :=
    57674277721422*b +
    55973427025068*c +
    5034496663651820
def identitySlackLo1 (b c : ℕ) : ℕ :=
    2894325953171841648*b +
    2808970461826012512*c +
    249649426790584865280
def helperSlackLo1 (b c : ℕ) : ℕ :=
    705275396365653601488*b^2 +
    1392465082862359806624*b*c +
    134390704413976293766752*b +
    12745743168632413647744*c +
    370540708714631831774832
def gLo2 (b c : ℕ) : ℕ :=
    2473938911232*b^2 +
    4947877822464*b*c +
    2414434825109466*b +
    188845957072176*c +
    8029893250079492
def identitySlackLo2 (b c : ℕ) : ℕ :=
    124152150321266688*b^2 +
    248304300642533376*b*c +
    119965295752046213904*b +
    8876694754086466464*c +
    398169352236722488128
def helperSlackLo2 (b c : ℕ) : ℕ :=
    705123103010099212368*b^2 +
    1392312789506805417504*b*c +
    134388654649140556484640*b +
    12744928799738149000896*c +
    370534263814156632860016
def conductorLo (b c : ℕ) : ℕ :=
    1473334106688720*b^2 +
    2946668213377440*b*c +
    157100712385260384*b +
    17973374558184000*c +
    533450412574885872
def slopeLo (b : ℕ) : ℕ :=
    1393422126370422651936*b +
    12752247699354029824512
def interceptLo (b : ℕ) : ℕ :=
    706232439873716446800*b^2 +
    134426626587456413107680*b +
    370696504344921491265648
def gHi0 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    202040345118432*a +
    61385186088270*b +
    695495242350396
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    124152150321266688*a^2 +
    248304300642533376*a*b +
    9538841923799777568*a +
    3080554178653741680*b +
    32801505597429624144
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    26605380469919303808*a^3 +
    80027749019580852096*a^2*b +
    80239356629403792768*a^2*c +
    24008744876021767109232*a^2 +
    80239356629403792768*a*b^2 +
    160690320868630526208*a*b*c +
    50394876720961662089568*a*b +
    4612550915314055765376*a*c +
    254013734894551531750080*a +
    772383654976264900560*b^2 +
    1526615873477501036832*b*c +
    184667328637264637978112*b +
    17239762550482603952256*c +
    600548592473560656285120
def gHi1 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2198461095816616*a +
    61385186088270*b +
    59684335391916*c +
    7229246832227220
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    124152150321266688*a^2 +
    248304300642533376*a*b +
    248304300642533376*a*c +
    109126870121213829504*a +
    3080554178653741680*b +
    2995198687307912544*c +
    358590067739125511040
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    26518813720446282624*a^3 +
    79854615520634809728*a^2*b +
    80152789879930771584*a^2*c +
    24007624114395274828272*a^2 +
    80152789879930771584*a*b^2 +
    160603754119157505024*a*b*c +
    50393392058369792478816*a*b +
    4611468830835566846592*a*c +
    254008986109907802196032*a +
    772019754010887570768*b^2 +
    1526251972512123707040*b*c +
    184664016355528043747136*b +
    17236833708290642034048*c +
    600541772250208777257024
def gHi2 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2198461095816616*a +
    2473938911232*b^2 +
    4947877822464*b*c +
    2419382702931930*b +
    193793834894640*c +
    10225880406984876
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    124152150321266688*a^2 +
    248304300642533376*a*b +
    248304300642533376*a*c +
    109126870121213829504*a +
    124152150321266688*b^2 +
    248304300642533376*b*c +
    120213600052688747280*b +
    9124999054728999840*c +
    507172070207615050944
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    26470721081850159744*a^3 +
    79758430243442563968*a^2*b +
    80104697241334648704*a^2*c +
    24006655558291098855024*a^2 +
    80104697241334648704*a*b^2 +
    160555661480561382144*a*b*c +
    50392223116271465993568*a*b +
    4610960651893247729280*a*c +
    254002984765851780919872*a +
    771819368016737058768*b^2 +
    1526051586517973195040*b*c +
    184660893833871172225536*b +
    17235559253092654392768*c +
    600530246469143136916416
def conductorHi (a b c : ℕ) : ℕ :=
    123610348639872*a^3 +
    370831045919616*a^2*b +
    370831045919616*a^2*c +
    26869969033055856*a^2 +
    370831045919616*a*b^2 +
    741662091839232*a*b*c +
    53739938066111712*a*b +
    7364158790419584*a*c +
    309089710743564096*a +
    1844165152608336*b^2 +
    3688330305216672*b*c +
    210469819405452480*b +
    24966702302683968*c +
    815793764634033984
def slopeHi (a b : ℕ) : ℕ :=
    80450964239226733440*a^2 +
    160901928478453466880*a*b +
    4615138299539602219392*a +
    1527507190379482514208*b +
    17246709533356997621760
def interceptHi (a b : ℕ) : ℕ :=
    26816988079742244480*a^3 +
    80450964239226733440*a^2*b +
    24022036396702949423472*a^2 +
    80450964239226733440*a*b^2 +
    50409059558544825881184*a*b +
    254128224494748481089984*a +
    773274971878246377936*b^2 +
    184715009680464604566720*b +
    600802692157390737008448
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
  norm_num [cfg,scale,source18,source19,source20,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source18,source19,source20,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source18,source19,source20,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G10

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G11
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source21,source5,source22]
def scale : ℕ := 360
def denominator : ℕ := 6503846400
def gLo0 (b c : ℕ) : ℕ :=
    91871669461485*b +
    804299443743210
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4610487860255163240*b +
    37861501803044192640
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1883084224276375258248*b^2 +
    3757802114257672479696*b*c +
    409219363004599583631216*b +
    34493398279412526378288*c +
    1094490455675512188765816
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8672041427089890
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4610487860255163240*b +
    4586778001547988480*c +
    430194804013548923760
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882465254205554787848*b^2 +
    3757183144186852009296*b*c +
    409217089096188362064816*b +
    34488907405749181631088*c +
    1094494470430992207444216
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4595260400707995*b +
    307183925358720*c +
    14396776429013310
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206920250535444480*b^2 +
    413840501070888960*b*c +
    228607378763717974680*b +
    14415133517495981280*c +
    714483143938159385040
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881619180008030403848*b^2 +
    3756337069989327625296*b*c +
    409205970921604179519216*b +
    34483917793305739626288*c +
    1094459982480615975271416
def conductorLo (b c : ℕ) : ℕ :=
    3938845741330248*b^2 +
    7877691482660496*b*c +
    478999356262767216*b +
    47480931378392688*c +
    1632601774206842616
def slopeLo (b : ℕ) : ℕ :=
    3759681289580595058896*b +
    34505953577851560498288
def interceptLo (b : ℕ) : ℕ :=
    1884963399599297837448*b^2 +
    409324961665883174045616*b +
    1094971673378514982788216
def gHi0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    328418638459656*a +
    98056516739565*b +
    1126533203467506
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    206920250535444480*a^2 +
    413840501070888960*a*b +
    15480776359753353504*a +
    4920868236058329960*b +
    53031896208342239904
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73903825166607365760*a^3 +
    222299274415996932480*a^2*b +
    222887073332171767680*a^2*c +
    68976922160695390917624*a^2 +
    222887073332171767680*a*b^2 +
    446361945580518370560*a*b*c +
    152591254445012781344688*a*b +
    12525952987252923774192*a*c +
    739928620515321280379808*a +
    2068725652512167019528*b^2 +
    4129672769645430837456*b*c +
    561476580671592457797024*b +
    46684726689729368138400*c +
    1765441565428482385126560
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3790216755772164*a +
    98056516739565*b +
    97584058212800*c +
    12456073304126694
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206920250535444480*a^2 +
    413840501070888960*a*b +
    413840501070888960*a*c +
    188207068486258231776*a +
    4920868236058329960*b +
    4897158377351155200*c +
    618091490545351849296
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73716798238733554560*a^3 +
    221925220560249310080*a^2*b +
    222700046404297956480*a^2*c +
    68975298347854378274424*a^2 +
    222700046404297956480*a*b^2 +
    446174918652644559360*a*b*c +
    152588824635173074419888*a*b +
    12523517183930653143792*a*c +
    739926086940530851461408*a +
    2067919655513472737928*b^2 +
    4128866772646736555856*b*c +
    561472251007197276928224*b +
    46677987039671626572000*c +
    1765444483395085113718560
def gHi2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3790216755772164*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4603506863745435*b +
    315430388396160*c +
    18182869953266754
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    206920250535444480*a^2 +
    413840501070888960*a*b +
    413840501070888960*a*c +
    188207068486258231776*a +
    206920250535444480*b^2 +
    413840501070888960*b*c +
    229021219264788863640*b +
    14828974018566870240*c +
    902483292173882172336
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73449616913199538560*a^3 +
    221390857909181278080*a^2*b +
    222432865078763940480*a^2*c +
    68970015447094985340024*a^2 +
    222432865078763940480*a*b^2 +
    445907737327110543360*a*b*c +
    152582428478890623085488*a*b +
    12520524752744930948592*a*c +
    739893691317818693301408*a +
    2066806399990414337928*b^2 +
    4127753517123678155856*b*c +
    561455271038981711080224*b +
    46670272177367996388000*c +
    1765382615541430582304160
def conductorHi (a b c : ℕ) : ℕ :=
    333890022188160*a^3 +
    1001670066564480*a^2*b +
    1001670066564480*a^2*c +
    81714844182447864*a^2 +
    1001670066564480*a*b^2 +
    2003340133128960*a*b*c +
    163429688364895728*a*b +
    19590213403437552*a*c +
    944518007793053088*a +
    4940515807894728*b^2 +
    9881031615789456*b*c +
    641427374561098464*b +
    66069474715265760*c +
    2495738827839636000
def slopeHi (a b : ℕ) : ℕ :=
    223474872248346602880*a^2 +
    446949744496693205760*a*b +
    12533095635436297143792*a +
    4132139743884528251856*b +
    46703836837435600792800
def interceptHi (a b : ℕ) : ℕ :=
    74491624082782200960*a^3 +
    223474872248346602880*a^2*b +
    69018002174110599084024*a^2 +
    223474872248346602880*a*b^2 +
    152634801432667086925488*a*b +
    740287175967053832626208*a +
    2071192626751264433928*b^2 +
    561624550722698004121824*b +
    1766240846368718698064160
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
  norm_num [cfg,scale,source5,source21,source22,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source5,source21,source22,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source5,source21,source22,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G11


