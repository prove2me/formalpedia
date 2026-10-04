-- Prove2me | Definitions.Def_Yukon_72032bf8cc70bee019faae40
-- name    : Yukon_72032bf8cc70bee019faae40
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T23:06:31.228395+00:00
-- url     : https://prove2.me/theorems/eb848cf8-8b2b-4179-a952-d6c61d0b85a8
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberArithmetic6814D.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberArithmetic6814D.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberArithmetic6814D.lean
--
--   yukon-proof-operation:certificate-r12-pair-split-26e2cf01efe1427b0809d6d6b36f6b54a850424316c58bbc9dd9469a7268a4d1
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiODUxYjk0ZmVhYTE2MGE4YmJlMDljZmJkYjM3ZWIzNmFiMzk1MGMxOTlmZWIyMmVlMmRmZTg4MTA0ZGViZmZkMSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMi1wYWlyLXNwbGl0LTI2ZTJjZjAxZWZlMTQyN2IwODA5ZDZkNmIzNmY2YjU0YTg1MDQyNDMxNmM1OGJiYzlkZDk0NjlhNzI2OGE0ZDEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl83MjAzMmJmOGNjNzBiZWUwMTlmYWFlNDAiLCJ2IjoyfQ]

import Definitions.Def_Yukon_83e2180d30d6903afaa66681






































































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G12
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source23,source5,source24]
def scale : ℕ := 360
def denominator : ℕ := 6503846400
def gLo0 (b c : ℕ) : ℕ :=
    91871669461485*b +
    809453549202330
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4610487860255163240*b +
    38120155431404670720
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1883226713405449591944*b^2 +
    3723802399270538017488*b*c +
    405820242619304477858352*b +
    34928648339736785021424*c +
    1077491299790608699437432
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    89509376827660*c +
    8483916577832010
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4610487860255163240*b +
    4491938566719289440*c +
    420753946578391473840
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882465246627677646344*b^2 +
    3723040932492766071888*b*c +
    405815460325046217415152*b +
    34923591932080868938224*c +
    1077486344502015453914232
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4595260400707995*b +
    314743261786960*c +
    14208651579755430
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206920250535444480*b^2 +
    413840501070888960*b*c +
    228607378763717974680*b +
    14794491256810777440*c +
    705042286503001935120
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881543471054585291144*b^2 +
    3722119156919673716688*b*c +
    405805369868295730442352*b +
    34918199321036157427824*c +
    1077458886100628659312632
def conductorLo (b c : ℕ) : ℕ :=
    3931267864188744*b^2 +
    7862535728377488*b*c +
    473407830166979952*b +
    47785940933338224*c +
    1613107211643002232
def slopeLo (b : ℕ) : ℕ :=
    3725539077886509121488*b +
    34940638104183247805424
def interceptLo (b : ℕ) : ℕ :=
    1884963392021420695944*b^2 +
    405923332894741029395952*b +
    1077963547449538229258232
def gHi0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    330686439388128*a +
    98056516739565*b +
    1133955109855098
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    206920250535444480*a^2 +
    413840501070888960*a*b +
    15594583681547792352*a +
    4920868236058329960*b +
    53404357158497156832
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73957261431714168960*a^3 +
    222406146946210538880*a^2*b +
    222940509597278570880*a^2*c +
    67481664344807309131896*a^2 +
    222940509597278570880*a*b^2 +
    446415381845625173760*a*b*c +
    151096191635227659967152*a*b +
    12704009071656583555056*a*c +
    726059686131781829069472*a +
    2068921577906348156424*b^2 +
    4095726490923403178448*b*c +
    556582290603982017040224*b +
    47297979398192179759200*c +
    1736068786412192633076768
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3707442021882936*a +
    98056516739565*b +
    95694224105740*c +
    12185173720979586
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206920250535444480*a^2 +
    413840501070888960*a*b +
    413840501070888960*a*c +
    184053101240761213824*a +
    4920868236058329960*b +
    4802318942522456160*c +
    604496665864697381424
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73716798238733554560*a^3 +
    221925220560249310080*a^2*b +
    222700046404297956480*a^2*c +
    67478809393348402344696*a^2 +
    222700046404297956480*a*b^2 +
    446174918652644559360*a*b*c +
    151092334753798000619952*a*b +
    12701110153968772387056*a*c +
    726049039599582833280672*a +
    2067919647935595596424*b^2 +
    4094724560952650618448*b*c +
    556574132354680058478624*b +
    47290264536041433122400*c +
    1736055799079666317937568
def gHi2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3707442021882936*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4603506863745435*b +
    322989724824400*c +
    17911970370119646
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    206920250535444480*a^2 +
    413840501070888960*a*b +
    413840501070888960*a*c +
    184053101240761213824*a +
    206920250535444480*b^2 +
    413840501070888960*b*c +
    229021219264788863640*b +
    15208331757881666400*c +
    888888467493227704464
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73422898780646136960*a^3 +
    221337421644074474880*a^2*b +
    222406146946210538880*a^2*c +
    67473752544455494488696*a^2 +
    222406146946210538880*a*b^2 +
    445881019194557141760*a*b*c +
    151086062229873912991152*a*b +
    12697846088401449820656*a*c +
    726020780919491322509472*a +
    2066703972904415823624*b^2 +
    4093508885921470845648*b*c +
    556558357172921658712224*b +
    47281901758887486463200*c +
    1736004844947622833003168
def conductorHi (a b c : ℕ) : ℕ :=
    333890022188160*a^3 +
    1001670066564480*a^2*b +
    1001670066564480*a^2*c +
    80787975084577656*a^2 +
    1001670066564480*a*b^2 +
    2003340133128960*a*b*c +
    161575950169155312*a*b +
    19701987091274736*a*c +
    933395578618610592*a +
    4932937930753224*b^2 +
    9865875861506448*b*c +
    633982110269570784*b +
    66486257958048480*c +
    2466048705199223328
def slopeHi (a b : ℕ) : ℕ :=
    223474872248346602880*a^2 +
    446949744496693205760*a*b +
    12710688605474416387056*a +
    4097997532190442314448*b +
    47316114333805407343200
def interceptHi (a b : ℕ) : ℕ :=
    74491624082782200960*a^3 +
    223474872248346602880*a^2*b +
    67521513219604623154296*a^2 +
    223474872248346602880*a*b^2 +
    151138311551292013125552*a*b +
    726410128626105814445472*a +
    2071192619173387292424*b^2 +
    556726432070180785672224*b +
    1736852162053299902283168
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
  norm_num [cfg,scale,source5,source23,source24,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source5,source23,source24,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source5,source23,source24,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G12

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G13
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source25,source5,source24]
def scale : ℕ := 360
def denominator : ℕ := 6503846400
def gLo0 (b c : ℕ) : ℕ :=
    91871669461485*b +
    809453549202330
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4610487860255163240*b +
    38120155431404670720
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1883159929914499121544*b^2 +
    3757877824158352235088*b*c +
    405819623126180190280752*b +
    34586916652424462266224*c +
    1077489870506862227095032
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8483916577832010
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4610487860255163240*b +
    4586778001547988480*c +
    420753946578391473840
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882474164512295147144*b^2 +
    3757192058756148260688*b*c +
    405816164309752933605552*b +
    34582116293640771979824*c +
    1077489632182764878887032
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4595260400707995*b +
    307183925358720*c +
    14208651579755430
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206920250535444480*b^2 +
    413840501070888960*b*c +
    228607378763717974680*b +
    14415133517495981280*c +
    705042286503001935120
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881552388939202791944*b^2 +
    3756270283183055905488*b*c +
    405806073853002446632752*b +
    34576723682596060469424*c +
    1077462173781378084285432
def conductorLo (b c : ℕ) : ℕ :=
    3943108297222344*b^2 +
    7886216594444688*b*c +
    475515427246960752*b +
    47549132272666224*c +
    1620365397092599032
def slopeLo (b : ℕ) : ℕ :=
    3759690204149891310288*b +
    34599162465743150847024
def interceptLo (b : ℕ) : ℕ :=
    1884972309906038196744*b^2 +
    405924036879447745586352*b +
    1077966835130287654231032
def gHi0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    330686439388128*a +
    98056516739565*b +
    1133955109855098
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    206920250535444480*a^2 +
    413840501070888960*a*b +
    15594583681547792352*a +
    4920868236058329960*b +
    53404357158497156832
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73930543299160767360*a^3 +
    222352710681103735680*a^2*b +
    222913791464725169280*a^2*c +
    67481267316953439480696*a^2 +
    222913791464725169280*a*b^2 +
    446388663713071772160*a*b*c +
    151095701437282411384752*a*b +
    12567195274530745699056*a*c +
    726057770435432987031072*a +
    2068828076282844284424*b^2 +
    4129775197678663994448*b*c +
    556581234349177587683424*b +
    46819460631886572549600*c +
    1736065811741818634945568
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3707442021882936*a +
    98056516739565*b +
    97584058212800*c +
    12185173720979586
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206920250535444480*a^2 +
    413840501070888960*a*b +
    413840501070888960*a*c +
    184053101240761213824*a +
    4920868236058329960*b +
    4897158377351155200*c +
    604496665864697381424
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73716798238733554560*a^3 +
    221925220560249310080*a^2*b +
    222700046404297956480*a^2*c +
    67479041293869756466296*a^2 +
    222700046404297956480*a*b^2 +
    446174918652644559360*a*b*c +
    151092575903736097183152*a*b +
    12564514554959428099056*a*c +
    726051319863023951213472*a +
    2067928565820213097224*b^2 +
    4128875687216032807248*b*c +
    556575077489324871232224*b +
    46812193298591991876000*c +
    1736061135123335506721568
def gHi2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3707442021882936*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4603506863745435*b +
    315430388396160*c +
    17911970370119646
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    206920250535444480*a^2 +
    413840501070888960*a*b +
    413840501070888960*a*c +
    184053101240761213824*a +
    206920250535444480*b^2 +
    413840501070888960*b*c +
    229021219264788863640*b +
    14828974018566870240*c +
    888888467493227704464
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73422898780646136960*a^3 +
    221337421644074474880*a^2*b +
    222406146946210538880*a^2*c +
    67473984444976848610296*a^2 +
    222406146946210538880*a*b^2 +
    445881019194557141760*a*b*c +
    151086303379812009554352*a*b +
    12561250489392105532656*a*c +
    726023061182932440442272*a +
    2066712890789033324424*b^2 +
    4127660012184853034448*b*c +
    556559302307566471465824*b +
    46803830521438045216800*c +
    1736010180991292021787168
def conductorHi (a b c : ℕ) : ℕ :=
    333890022188160*a^3 +
    1001670066564480*a^2*b +
    1001670066564480*a^2*c +
    81131347642552056*a^2 +
    1001670066564480*a*b^2 +
    2003340133128960*a*b*c +
    162262695285104112*a*b +
    19607263627005936*a*c +
    937516049314303392*a +
    4944778363786824*b^2 +
    9889556727573648*b*c +
    636776452465500384*b +
    66154725833107680*c +
    2477083988786538528
def slopeHi (a b : ℕ) : ℕ :=
    223474872248346602880*a^2 +
    446949744496693205760*a*b +
    12574093006465072099056*a +
    4132148658453824503248*b +
    46838043096355966096800
def interceptHi (a b : ℕ) : ℕ :=
    74491624082782200960*a^3 +
    223474872248346602880*a^2*b +
    67521745120125977275896*a^2 +
    223474872248346602880*a*b^2 +
    151138552701230109688752*a*b +
    726412408889546932378272*a +
    2071201537058004793224*b^2 +
    556727377204825598425824*b +
    1736857498096969091067168
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
  norm_num [cfg,scale,source5,source24,source25,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source5,source24,source25,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source5,source24,source25,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G13

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G14
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source25,source5,source26]
def scale : ℕ := 360
def denominator : ℕ := 6503846400
def gLo0 (b c : ℕ) : ℕ :=
    91871669461485*b +
    806876496472770
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4610487860255163240*b +
    37990828617224431680
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1883151019607758762248*b^2 +
    3757868909589055983696*b*c +
    407729378013307381700784*b +
    34540289934834600609264*c +
    1087038864512670607373304
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8589575739743970
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4610487860255163240*b +
    4586778001547988480*c +
    426056345959781274480
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882465254205554787848*b^2 +
    3757183144186852009296*b*c +
    407725919196880125025584*b +
    34535489576050910322864*c +
    1087038626188573259165304
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4595260400707995*b +
    307183925358720*c +
    14314310741667390
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206920250535444480*b^2 +
    413840501070888960*b*c +
    228607378763717974680*b +
    14415133517495981280*c +
    710344685884391735760
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881619180008030403848*b^2 +
    3756337069989327625296*b*c +
    407715560262562668308784*b +
    34530475471985961033264*c +
    1087007932862822046902904
def conductorLo (b c : ℕ) : ℕ :=
    3938845741330248*b^2 +
    7877691482660496*b*c +
    476546965772847984*b +
    47506506713745264*c +
    1624018407492125304
def slopeLo (b : ℕ) : ℕ :=
    3759681289580595058896*b +
    34552535748153289190064
def interceptLo (b : ℕ) : ℕ :=
    1884963399599297837448*b^2 +
    407833791766574937006384*b +
    1087515829136096034509304
def gHi0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    329552538923892*a +
    98056516739565*b +
    1130244156661302
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    206920250535444480*a^2 +
    413840501070888960*a*b +
    15537680020650572928*a +
    4920868236058329960*b +
    53218126683419698368
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73930543299160767360*a^3 +
    222352710681103735680*a^2*b +
    222913791464725169280*a^2*c +
    68321512862284383975672*a^2 +
    222913791464725169280*a*b^2 +
    446388663713071772160*a*b*c +
    151935938251333962988464*a*b +
    12546692135994265987824*a*c +
    733849287986966491380384*a +
    2068819165976103925128*b^2 +
    4129766283109367743056*b*c +
    559331226050356330707168*b +
    46752330775760231181408*c +
    1752566077753829575078176
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3753931940916612*a +
    98056516739565*b +
    97584058212800*c +
    12337322801925222
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206920250535444480*a^2 +
    413840501070888960*a*b +
    413840501070888960*a*c +
    186386151337547210208*a +
    4920868236058329960*b +
    4897158377351155200*c +
    612132115342873178448
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73716798238733554560*a^3 +
    221925220560249310080*a^2*b +
    222700046404297956480*a^2*c +
    68319286839200700961272*a^2 +
    222700046404297956480*a*b^2 +
    446174918652644559360*a*b*c +
    151932812717787648786864*a*b +
    12544011416422948387824*a*c +
    733842837414557455562784*a +
    2067919655513472737928*b^2 +
    4128866772646736555856*b*c +
    559325069190503614255968*b +
    46745063442465650507808*c +
    1752561401135346446854176
def gHi2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3753931940916612*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4603506863745435*b +
    315430388396160*c +
    18064119451065282
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    206920250535444480*a^2 +
    413840501070888960*a*b +
    413840501070888960*a*c +
    186386151337547210208*a +
    206920250535444480*b^2 +
    413840501070888960*b*c +
    229021219264788863640*b +
    14828974018566870240*c +
    896523916971403501488
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73449616913199538560*a^3 +
    221390857909181278080*a^2*b +
    222432865078763940480*a^2*c +
    68314280025811026510072*a^2 +
    222432865078763940480*a*b^2 +
    445907737327110543360*a*b*c +
    151926692648874915935664*a*b +
    12541010079193041725424*a*c +
    733813133118130516202784*a +
    2066806399990414337928*b^2 +
    4127753517123678155856*b*c +
    559309124549924492719968*b +
    46737315182496328571808*c +
    1752505743145232435666976
def conductorHi (a b c : ℕ) : ℕ :=
    333890022188160*a^3 +
    1001670066564480*a^2*b +
    1001670066564480*a^2*c +
    81306112434127992*a^2 +
    1001670066564480*a*b^2 +
    2003340133128960*a*b*c +
    162612224868255984*a*b +
    19598738515221744*a*c +
    939613226813214624*a +
    4940515807894728*b^2 +
    9881031615789456*b*c +
    638157520574539488*b +
    66103575162402528*c +
    2482659411893400096
def slopeHi (a b : ℕ) : ℕ :=
    223474872248346602880*a^2 +
    446949744496693205760*a*b +
    12553589867928592387824*a +
    4132139743884528251856*b +
    46770913240229624728608
def interceptHi (a b : ℕ) : ℕ :=
    74491624082782200960*a^3 +
    223474872248346602880*a^2*b +
    68361990665456921770872*a^2 +
    223474872248346602880*a*b^2 +
    151978789515281661292464*a*b +
    734203926441080436727584*a +
    2071192626751264433928*b^2 +
    559477368906004341449568*b +
    1753357764108980031199776
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
  norm_num [cfg,scale,source5,source25,source26,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source5,source25,source26,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source5,source25,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G14

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G15
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source21,source5,source26]
def scale : ℕ := 360
def denominator : ℕ := 6503846400
def gLo0 (b c : ℕ) : ℕ :=
    91871669461485*b +
    806876496472770
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4610487860255163240*b +
    37990828617224431680
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1883084224276375258248*b^2 +
    3757802114257672479696*b*c +
    407728758046565772779184*b +
    34539980449714255070064*c +
    1087037433689667840662904
def gLo1 (b c : ℕ) : ℕ :=
    91871669461485*b +
    91399210934720*c +
    8589575739743970
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4610487860255163240*b +
    4586778001547988480*c +
    426056345959781274480
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1882465254205554787848*b^2 +
    3757183144186852009296*b*c +
    407726484138154551212784*b +
    34535489576050910322864*c +
    1087041448445147859341304
def gLo2 (b c : ℕ) : ℕ :=
    4123231518720*b^2 +
    8246463037440*b*c +
    4595260400707995*b +
    307183925358720*c +
    14314310741667390
def identitySlackLo2 (b c : ℕ) : ℕ :=
    206920250535444480*b^2 +
    413840501070888960*b*c +
    228607378763717974680*b +
    14415133517495981280*c +
    710344685884391735760
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1881619180008030403848*b^2 +
    3756337069989327625296*b*c +
    407716125203837094495984*b +
    34530475471985961033264*c +
    1087010755119396647078904
def conductorLo (b c : ℕ) : ℕ :=
    3938845741330248*b^2 +
    7877691482660496*b*c +
    478180945531484784*b +
    47506506713745264*c +
    1629737336647354104
def slopeLo (b : ℕ) : ℕ :=
    3759681289580595058896*b +
    34552535748153289190064
def interceptLo (b : ℕ) : ℕ :=
    1884963399599297837448*b^2 +
    407834356707849363193584*b +
    1087518651392670634685304
def gHi0 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    329552538923892*a +
    98056516739565*b +
    1130244156661302
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    206920250535444480*a^2 +
    413840501070888960*a*b +
    15537680020650572928*a +
    4920868236058329960*b +
    53218126683419698368
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    73903825166607365760*a^3 +
    222299274415996932480*a^2*b +
    222887073332171767680*a^2*c +
    68321115763387916122872*a^2 +
    222887073332171767680*a*b^2 +
    446361945580518370560*a*b*c +
    151935447911303518002864*a*b +
    12546447219745219018224*a*c +
    733847371438106470922784*a +
    2068725652512167019528*b^2 +
    4129672769645430837456*b*c +
    559330169179849383603168*b +
    46751803092523392074208*c +
    1752563100762730702361376
def gHi1 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3753931940916612*a +
    98056516739565*b +
    97584058212800*c +
    12337322801925222
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    206920250535444480*a^2 +
    413840501070888960*a*b +
    413840501070888960*a*c +
    186386151337547210208*a +
    4920868236058329960*b +
    4897158377351155200*c +
    612132115342873178448
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    73716798238733554560*a^3 +
    221925220560249310080*a^2*b +
    222700046404297956480*a^2*c +
    68319491950546903479672*a^2 +
    222700046404297956480*a*b^2 +
    446174918652644559360*a*b*c +
    151933018101463811078064*a*b +
    12544011416422948387824*a*c +
    733844837863316042004384*a +
    2067919655513472737928*b^2 +
    4128866772646736555856*b*c +
    559325839515454202734368*b +
    46745063442465650507808*c +
    1752566018729333430953376
def gHi2 (a b c : ℕ) : ℕ :=
    4123231518720*a^2 +
    8246463037440*a*b +
    8246463037440*a*c +
    3753931940916612*a +
    4123231518720*b^2 +
    8246463037440*b*c +
    4603506863745435*b +
    315430388396160*c +
    18064119451065282
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    206920250535444480*a^2 +
    413840501070888960*a*b +
    413840501070888960*a*c +
    186386151337547210208*a +
    206920250535444480*b^2 +
    413840501070888960*b*c +
    229021219264788863640*b +
    14828974018566870240*c +
    896523916971403501488
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    73449616913199538560*a^3 +
    221390857909181278080*a^2*b +
    222432865078763940480*a^2*c +
    68314485137157229028472*a^2 +
    222432865078763940480*a*b^2 +
    445907737327110543360*a*b*c +
    151926898032551078226864*a*b +
    12541010079193041725424*a*c +
    733815133566889102644384*a +
    2066806399990414337928*b^2 +
    4127753517123678155856*b*c +
    559309894874875081198368*b +
    46737315182496328571808*c +
    1752510360739219419766176
def conductorHi (a b c : ℕ) : ℕ :=
    333890022188160*a^3 +
    1001670066564480*a^2*b +
    1001670066564480*a^2*c +
    81578442393900792*a^2 +
    1001670066564480*a*b^2 +
    2003340133128960*a*b*c +
    163156884787801584*a*b +
    19598738515221744*a*c +
    942881186330488224*a +
    4940515807894728*b^2 +
    9881031615789456*b*c +
    640336160252721888*b +
    66103575162402528*c +
    2491373970606129696
def slopeHi (a b : ℕ) : ℕ :=
    223474872248346602880*a^2 +
    446949744496693205760*a*b +
    12553589867928592387824*a +
    4132139743884528251856*b +
    46770913240229624728608
def interceptHi (a b : ℕ) : ℕ :=
    74491624082782200960*a^3 +
    223474872248346602880*a^2*b +
    68362195776803124289272*a^2 +
    223474872248346602880*a*b^2 +
    151978994898957823583664*a*b +
    734205926889839023169184*a +
    2071192626751264433928*b^2 +
    559478139230954929927968*b +
    1753362381702967015298976
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
  norm_num [cfg,scale,source5,source21,source26,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source5,source21,source26,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source5,source21,source26,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G15


