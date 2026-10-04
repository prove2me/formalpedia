-- Prove2me | Definitions.Def_Yukon_00539a3de5b1ad4051dcf52a
-- name    : Yukon_00539a3de5b1ad4051dcf52a
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T22:12:58.079962+00:00
-- url     : https://prove2.me/theorems/06071e7f-50da-4d4c-b174-9e0c2db18540
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberArithmetic6814B.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberArithmetic6814B.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberArithmetic6814B.lean
--
--   yukon-proof-operation:certificate-split-ca29e37eaee22b7c57a23b170f100f7881117589ebca3301bde052073b03f864
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMWJmYjRmOWYxNTI1ZDUxZjgzMzFjOTE0MWM4NzJmMzZiZTNiYzAwNDZkYTFjZDk0YTVkMThlYzU5NmQ4M2RlMCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LWNhMjllMzdlYWVlMjJiN2M1N2EyM2IxNzBmMTAwZjc4ODExMTc1ODllYmNhMzMwMWJkZTA1MjA3M2IwM2Y4NjQiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8wMDUzOWEzZGU1YjFhZDQwNTFkY2Y1MmEiLCJ2IjoyfQ]

import Definitions.Def_Yukon_32ea6b78735a1c7c12e3810a






































































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G4
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source4,source5,source6]
def scale : ℕ := 216
def denominator : ℕ := 2341384704
def gLo0 (b c : ℕ) : ℕ :=
    55123001676891*b +
    475020311572550
def identitySlackLo0 (b c : ℕ) : ℕ :=
    2766292716153097944*b +
    22337542426897814400
def helperSlackLo0 (b c : ℕ) : ℕ :=
    677902339247786174088*b^2 +
    1340509622835310879824*b*c +
    154226260357147205020656*b +
    12458280926287046686896*c +
    428553184567950137621880
def gLo1 (b c : ℕ) : ℕ :=
    55123001676891*b +
    53705626096596*c +
    5840444094516470
def identitySlackLo1 (b c : ℕ) : ℕ :=
    2766292716153097944*b +
    2695163140031573664*c +
    290095092661096460880
def helperSlackLo1 (b c : ℕ) : ℕ :=
    677652257527086335112*b^2 +
    1340259541114611040848*b*c +
    154224885945246320297520*b +
    12456572034174241291056*c +
    428552535008270889067896
def gLo2 (b c : ℕ) : ℕ :=
    2473938911232*b^2 +
    4947877822464*b*c +
    2757156240424797*b +
    188845957072176*c +
    9275285095670522
def identitySlackLo2 (b c : ℕ) : ℕ :=
    124152150321266688*b^2 +
    248304300642533376*b*c +
    137164427258230784808*b +
    8876694754086466464*c +
    460668096615862737648
def helperSlackLo2 (b c : ℕ) : ℕ :=
    677499964171531945992*b^2 +
    1340107247759056651728*b*c +
    154222236625516084683504*b +
    12455757665279976644208*c +
    428543092332075668748408
def conductorLo (b c : ℕ) : ℕ :=
    1451932523980488*b^2 +
    2903865047960976*b*c +
    179266180630655088*b +
    17604485867022192*c +
    611243567260849656
def slopeLo (b : ℕ) : ℕ :=
    1341158873456358538704*b +
    12462708656131097683248
def interceptLo (b : ℕ) : ℕ :=
    678551589868833832968*b^2 +
    154263720070336452610608*b +
    428724328069379088191736
def gHi0 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    193725075047368*a +
    58833910043739*b +
    665034459378702
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    124152150321266688*a^2 +
    248304300642533376*a*b +
    9121548410553501792*a +
    2952520941634997976*b +
    31272861664778132448
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    26614998997638528384*a^3 +
    80046986075019301248*a^2*b +
    80248975157123017344*a^2*c +
    27871037959685541969528*a^2 +
    80248975157123017344*a*b^2 +
    160699939396349750784*a*b*c +
    57972200346265312473264*a*b +
    4522413818949684234480*a*c +
    294556634154178198041888*a +
    744742882170212389128*b^2 +
    1474392697762267026000*b*c +
    212078188216040090503968*b +
    16860220268782200215328*c +
    695238578487784404054432
def gHi1 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2554505841586720*a +
    58833910043739*b +
    57416534463444*c +
    8391239008861974
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    124152150321266688*a^2 +
    248304300642533376*a*b +
    248304300642533376*a*c +
    126994619642940728640*a +
    2952520941634997976*b +
    2881391365513473696*c +
    416903483131364005776
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    26538050775884731776*a^3 +
    79893089631511708032*a^2*b +
    80172026935369220736*a^2*c +
    27870198117264539186040*a^2 +
    80172026935369220736*a*b^2 +
    160622991174595954176*a*b*c +
    57971033473901856054192*a*b +
    4521458378431729123056*a*c +
    294553930179738432645792*a +
    744415852227758753544*b^2 +
    1474065667819813390416*b*c +
    212075800828219256954976*b +
    16857632884373193504672*c +
    695235987847864639091232
def gHi2 (a b c : ℕ) : ℕ :=
    2473938911232*a^2 +
    4947877822464*a*b +
    4947877822464*a*c +
    2554505841586720*a +
    2473938911232*b^2 +
    4947877822464*b*c +
    2762104118247261*b +
    193793834894640*c +
    11827316998346010
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    124152150321266688*a^2 +
    248304300642533376*a*b +
    248304300642533376*a*c +
    126994619642940728640*a +
    124152150321266688*b^2 +
    248304300642533376*b*c +
    137412731558873318184*b +
    9124999054728999840*c +
    587538564108482199600
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    26489958137288608896*a^3 +
    79796904354319462272*a^2*b +
    80123934296773097856*a^2*c +
    27869011541198727455736*a^2 +
    80123934296773097856*a*b^2 +
    160574898535999831296*a*b*c +
    57969646511841893811888*a*b +
    4520950199489410005744*a*c +
    294545803140640619489952*a +
    744215466233608241544*b^2 +
    1473865281825662878416*b*c +
    212071860731706251344416*b +
    16856358429175205863392*c +
    695219556615998821223328
def conductorHi (a b c : ℕ) : ℕ :=
    123610348639872*a^3 +
    370831045919616*a^2*b +
    370831045919616*a^2*c +
    30578481462427128*a^2 +
    370831045919616*a*b^2 +
    741662091839232*a*b*c +
    61156962924854256*a*b +
    7269731336976624*a*c +
    353591859896019360*a +
    1822763569900104*b^2 +
    3645527139800208*b*c +
    240052312509589728*b +
    24503386158079200*c +
    934380556043081760
def slopeHi (a b : ℕ) : ℕ :=
    80450964239226733440*a^2 +
    160901928478453466880*a*b +
    4524906620973760963056*a +
    1475243937465418400976*b +
    16866938811568224224160
def interceptHi (a b : ℕ) : ℕ :=
    26816988079742244480*a^3 +
    80450964239226733440*a^2*b +
    27885571494716778677496*a^2 +
    80450964239226733440*a*b^2 +
    57987585120999700556208*a*b +
    294683922229286705865120*a +
    745594121873363764104*b^2 +
    212130628725799518744672*b +
    695522678518372729455648
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
  norm_num [cfg,scale,source4,source5,source6,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source4,source5,source6,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source4,source5,source6,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G4

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G5
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source7,source8,source9]
def scale : ℕ := 378
def denominator : ℕ := 7170490656
def gLo0 (b c : ℕ) : ℕ :=
    97103071945692*b +
    862162941984460
def identitySlackLo0 (b c : ℕ) : ℕ :=
    4873020562522607328*b +
    40640250524694829740
def helperSlackLo0 (b c : ℕ) : ℕ :=
    2088136022456612528208*b^2 +
    4192654615077277827864*b*c +
    457920744280446355044804*b +
    38776340240582241270348*c +
    1198577700363445120309824
def gLo1 (b c : ℕ) : ℕ :=
    97103071945692*b +
    97953497293869*c +
    8871642825456940
def identitySlackLo1 (b c : ℕ) : ℕ :=
    4873020562522607328*b +
    4915698308195521896*c +
    439961454441024455160
def helperSlackLo1 (b c : ℕ) : ℕ :=
    2087679442968940586616*b^2 +
    4192198035589605886272*b*c +
    457918264920574003066524*b +
    38773139274074921017572*c +
    1198576658893516671127032
def gLo2 (b c : ℕ) : ℕ :=
    4329393094656*b^2 +
    8658786189312*b*c +
    5021684282509326*b +
    328496099063895*c +
    15132102108497296
def identitySlackLo2 (b c : ℕ) : ℕ :=
    217266263062216704*b^2 +
    434532526124433408*b*c +
    249906976388765367264*b +
    15434634413081182320*c +
    750984493618611510264
def helperSlackLo2 (b c : ℕ) : ℕ :=
    2086746646166169953256*b^2 +
    4191265238786835252912*b*c +
    457909247374620355589040*b +
    38767584222330602644296*c +
    1198554833662470173500200
def conductorLo (b c : ℕ) : ℕ :=
    4689810204280632*b^2 +
    9379620408561264*b*c +
    533925562539377088*b +
    57065442598299888*c +
    1816504276921196256
def slopeLo (b : ℕ) : ℕ :=
    4194662582931663033360*b +
    38789971350391525885128
def interceptLo (b : ℕ) : ℕ :=
    2090143990310997733704*b^2 +
    458026103477979613908432*b +
    1199054528760389200708104
def gHi0 (a b c : ℕ) : ℕ :=
    4329393094656*a^2 +
    8658786189312*a*b +
    352247720082314*a +
    103597161587676*b +
    1207916539394646
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    217266263062216704*a^2 +
    434532526124433408*a*b +
    16626585762269521416*a +
    5198919957115932384*b +
    56940935234786279604
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    81508451213569640400*a^3 +
    245143945204651551744*a^2*b +
    245762536768594182288*a^2*c +
    74080230489371058798600*a^2 +
    245762536768594182288*a*b^2 +
    492143665101130995120*a*b*c +
    169995567017794462651152*a*b +
    14063039770148776180224*a*c +
    802275704705297984711328*a +
    2292835235506447753440*b^2 +
    4602671632740890908872*b*c +
    627547976755312855097556*b +
    52470426876239112221628*c +
    1926772555130014029597864
def gHi1 (a b c : ℕ) : ℕ :=
    4329393094656*a^2 +
    8658786189312*a*b +
    8658786189312*a*c +
    3876410362927802*a +
    103597161587676*b +
    104447586935853*c +
    12741559065712614
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    217266263062216704*a^2 +
    434532526124433408*a*b +
    434532526124433408*a*c +
    192432550008486166848*a +
    5198919957115932384*b +
    5241597702788846952*c +
    632068103397332550456
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    81361167507869014080*a^3 +
    244849377793250299104*a^2*b +
    245615253062893555968*a^2*c +
    74078619296394465642672*a^2 +
    245615253062893555968*a*b^2 +
    491996381395430368800*a*b*c +
    169993351961624496927312*a*b +
    14061218361467662756080*a*c +
    802270543372120138004208*a +
    2292231372313075185528*b^2 +
    4602067769547518340960*b*c +
    627543576906681938648076*b +
    52465551784756379171028*c +
    1926767816236178626237560
def gHi2 (a b c : ℕ) : ℕ :=
    4329393094656*a^2 +
    8658786189312*a*b +
    8658786189312*a*c +
    3876410362927802*a +
    4329393094656*b^2 +
    8658786189312*b*c +
    5030343068698638*b +
    337154885253207*c +
    19004183078330442
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    217266263062216704*a^2 +
    434532526124433408*a*b +
    434532526124433408*a*c +
    192432550008486166848*a +
    217266263062216704*b^2 +
    434532526124433408*b*c +
    250341508914889800672*b +
    15869166939205615728*c +
    943199777364035460408
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    81066600096467761440*a^3 +
    244260242970447793824*a^2*b +
    245320685651492303328*a^2*c +
    74073973167952839943056*a^2 +
    245320685651492303328*a*b^2 +
    491701813984029116160*a*b*c +
    169987478468968699341696*a*b +
    14057899568257977285696*a*c +
    802246314169330042301928*a +
    2291004008098903299528*b^2 +
    4600840405333346454960*b*c +
    627529275002895296090256*b +
    52456972507213776580008*c +
    1926726113363372257355424
def conductorHi (a b c : ℕ) : ℕ :=
    395339994356832*a^3 +
    1186019983070496*a^2*b +
    1186019983070496*a^2*c +
    91198143544192992*a^2 +
    1186019983070496*a*b^2 +
    2372039966140992*a*b*c +
    182396287088385984*a*b +
    23442913774693584*a*c +
    1051681003139778048*a +
    5875830187351128*b^2 +
    11751660374702256*b*c +
    715135829644692576*b +
    79322336389922976*c +
    2777382476511138144
def slopeHi (a b : ℕ) : ℕ :=
    246381128332536812832*a^2 +
    492762256665073625664*a*b +
    14070683795261224536576*a +
    4605298192159218744912*b +
    52491083419596902562216
def interceptHi (a b : ℕ) : ℕ :=
    82127042777512270944*a^3 +
    246381128332536812832*a^2*b +
    74121283182777113185776*a^2 +
    246381128332536812832*a*b^2 +
    170039246270618844874368*a*b +
    802631870682031303883496*a +
    2295461794924775589480*b^2 +
    627695778022542610923312*b +
    1927565115401849317411680
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
  norm_num [cfg,scale,source7,source8,source9,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source7,source8,source9,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source7,source8,source9,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G5

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G6
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source10,source10,source10]
def scale : ℕ := 27
def denominator : ℕ := 36584136
def gLo0 (b c : ℕ) : ℕ :=
    7138415936163*b +
    60552249349760
def identitySlackLo0 (b c : ℕ) : ℕ :=
    358234265340403992*b +
    2851144470235976490
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10924475144038585848*b^2 +
    21853859744933859240*b*c +
    2283774484546487994318*b +
    197005732386300730836*c +
    6500518496668996009884
def gLo1 (b c : ℕ) : ℕ :=
    7138415936163*b +
    7138415936163*c +
    723499064029070
def identitySlackLo1 (b c : ℕ) : ℕ :=
    358234265340403992*b +
    358234265340403992*c +
    35932857806970090180
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10924475144038585848*b^2 +
    21853859744933859240*b*c +
    2283774484546487994318*b +
    197005732386300730836*c +
    6500518496668996009884
def gLo2 (b c : ℕ) : ℕ :=
    309242363904*b^2 +
    618484727808*b*c +
    315671010899236*b +
    23511252928669*c +
    1115662567593104
def identitySlackLo2 (b c : ℕ) : ℕ :=
    15519018790158336*b^2 +
    31038037580316672*b*c +
    15691546322061355944*b +
    1104844872519373356*c +
    55388058963933988836
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10924475144038585848*b^2 +
    21853859744933859240*b*c +
    2283774484546487994318*b +
    197005732386300730836*c +
    6500518496668996009884
def conductorLo (b c : ℕ) : ℕ :=
    18914701540392*b^2 +
    37829403080784*b*c +
    1871792709847344*b +
    226978954984800*c +
    6340548938372496
def slopeLo (b : ℕ) : ℕ :=
    21869439755979061548*b +
    197111047772424021426
def interceptLo (b : ℕ) : ℕ :=
    10940055155083788156*b^2 +
    2284411080615110934237*b +
    6503313744431563421394
def gHi0 (a b c : ℕ) : ℕ :=
    309242363904*a^2 +
    618484727808*a*b +
    24593601202333*a +
    7602279482019*b +
    84681984646941
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    15519018790158336*a^2 +
    31038037580316672*a*b +
    1159161438284927532*a +
    381512793525641496*b +
    3987027261936756054
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    414205841884343472*a^3 +
    1247426789512642704*a^2*b +
    1252236053372254992*a^2*c +
    431367719117626962720*a^2 +
    1252236053372254992*a*b^2 +
    2509281370604122272*a*b*c +
    862434547685882171496*a*b +
    71032994052254628048*a*c +
    4514415298889103951552*a +
    11967204443743703304*b^2 +
    23944127608203706440*b*c +
    3144333081985085527974*b +
    266157966927411108756*c +
    10583561262381481902060
def gHi1 (a b c : ℕ) : ℕ :=
    309242363904*a^2 +
    618484727808*a*b +
    618484727808*a*c +
    316289495627044*a +
    7602279482019*b +
    7602279482019*c +
    1039324693750962
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    15519018790158336*a^2 +
    31038037580316672*a*b +
    31038037580316672*a*c +
    15722584359641672616*a +
    381512793525641496*b +
    381512793525641496*c +
    51632163520027614828
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    414205841884343472*a^3 +
    1247426789512642704*a^2*b +
    1252236053372254992*a^2*c +
    431367719117626962720*a^2 +
    1252236053372254992*a*b^2 +
    2509281370604122272*a*b*c +
    862434547685882171496*a*b +
    71032994052254628048*a*c +
    4514415298889103951552*a +
    11967204443743703304*b^2 +
    23944127608203706440*b*c +
    3144333081985085527974*b +
    266157966927411108756*c +
    10583561262381481902060
def gHi2 (a b c : ℕ) : ℕ :=
    309242363904*a^2 +
    618484727808*a*b +
    618484727808*a*c +
    316289495627044*a +
    309242363904*b^2 +
    618484727808*b*c +
    316289495627044*b +
    24129737656477*c +
    1431642820856244
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    15519018790158336*a^2 +
    31038037580316672*a*b +
    31038037580316672*a*c +
    15722584359641672616*a +
    15519018790158336*b^2 +
    31038037580316672*b*c +
    15722584359641672616*b +
    1135882910099690028*c +
    71095124304785503116
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    414205841884343472*a^3 +
    1247426789512642704*a^2*b +
    1252236053372254992*a^2*c +
    431367719117626962720*a^2 +
    1252236053372254992*a*b^2 +
    2509281370604122272*a*b*c +
    862434547685882171496*a*b +
    71032994052254628048*a*c +
    4514415298889103951552*a +
    11967204443743703304*b^2 +
    23944127608203706440*b*c +
    3144333081985085527974*b +
    266157966927411108756*c +
    10583561262381481902060
def conductorHi (a b c : ℕ) : ℕ :=
    1598409680688*a^3 +
    4795229042064*a^2*b +
    4795229042064*a^2*c +
    320934181303584*a^2 +
    4795229042064*a*b^2 +
    9590458084128*a*b*c +
    641868362607168*a*b +
    93597110986320*a*c +
    3678581930128704*a +
    23709930582456*b^2 +
    47419861164912*b*c +
    2508865843412448*b +
    315780836929056*c +
    9699795096878304
def slopeHi (a b : ℕ) : ℕ :=
    1257045317231867280*a^2 +
    2514090634463734560*a*b +
    71092208119641446232*a +
    23964516883108521036*b +
    266317687117061605242
def interceptHi (a b : ℕ) : ℕ :=
    419015105743955760*a^3 +
    1257045317231867280*a^2*b +
    431620595263090148688*a^2 +
    1257045317231867280*a*b^2 +
    862707813106250172060*a*b +
    4516537918806640776528*a +
    11987593718648517900*b^2 +
    3145233324946357243881*b +
    10588231063179982564866
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
  norm_num [cfg,scale,source10,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source10,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source10,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G6

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G7
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source11,source12,source13]
def scale : ℕ := 840
def denominator : ℕ := 35409830400
def gLo0 (b c : ℕ) : ℕ :=
    227123608966120*b +
    1962085248063300
def identitySlackLo0 (b c : ℕ) : ℕ :=
    11397971192355766080*b +
    92628542631356845200
def helperSlackLo0 (b c : ℕ) : ℕ :=
    10790309891027704920696*b^2 +
    21517590764560864524912*b*c +
    2079212533473913419491280*b +
    196445118624455663169408*c +
    5659068719531646531405000
def gLo1 (b c : ℕ) : ℕ :=
    227123608966120*b +
    225611741680472*c +
    19557986531104850
def identitySlackLo1 (b c : ℕ) : ℕ :=
    11397971192355766080*b +
    11322099644492806848*c +
    969824509162062188400
def helperSlackLo1 (b c : ℕ) : ℕ :=
    10786527790930701183096*b^2 +
    21513808664463860787312*b*c +
    2079174946362564560564880*b +
    196419140925156017212608*c +
    5658974881054271908288200
def gLo2 (b c : ℕ) : ℕ :=
    9620873543680*b^2 +
    19241747087360*b*c +
    9764600834566000*b +
    748511705502288*c +
    31680590933720930
def identitySlackLo2 (b c : ℕ) : ℕ :=
    482813917916037120*b^2 +
    965627835832074240*b*c +
    485357333515898702400*b +
    35228614045946100192*c +
    1571181178541813835120
def helperSlackLo2 (b c : ℕ) : ℕ :=
    10784224588948551471096*b^2 +
    21511505462481711075312*b*c +
    2079151947429000419641680*b +
    196405491419645877479808*c +
    5658917328949825711110600
def conductorLo (b c : ℕ) : ℕ :=
    26099010788309496*b^2 +
    52198021576618992*b*c +
    2884196030464158480*b +
    317282563359505728*c +
    9804381165197641800
def slopeLo (b : ℕ) : ℕ :=
    21526488397481379728112*b +
    196504674591445751308608
def interceptLo (b : ℕ) : ℕ :=
    10799207523948220123896*b^2 +
    2079663126298846088248080*b +
    5661100214583023852310600
def gHi0 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    796736485529530*a +
    241554919281640*b +
    2744390349876990
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    482813917916037120*a^2 +
    965627835832074240*a*b +
    37648726406833212720*a +
    12122192069229821760*b +
    129553044477794343360
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    402802020140042920320*a^3 +
    1211169902798708415360*a^2*b +
    1213933745177288069760*a^2*c +
    362621246025731427497736*a^2 +
    1213933745177288069760*a*b^2 +
    2430631332733155793920*a*b*c +
    777485233000632226782672*a*b +
    70817884952545662151968*a*c +
    3857252050414261290663072*a +
    11801461790680257400056*b^2 +
    23542658406244549138032*b*c +
    2854878247941014537628192*b +
    265440721201091637021216*c +
    9153696756060950579391456
def gHi1 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8538914363627585*a +
    241554919281640*b +
    240043051995992*c +
    28082469511016595
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    482813917916037120*a^2 +
    965627835832074240*a*b +
    965627835832074240*a*c +
    423847483658325284040*a +
    12122192069229821760*b +
    12046320521366862528*c +
    1392947768259991757880
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    401638297033272539520*a^3 +
    1208842456585167653760*a^2*b +
    1212770022070517688960*a^2*c +
    362602435158856334729736*a^2 +
    1212770022070517688960*a*b^2 +
    2429467609626385413120*a*b*c +
    777461476310553359896272*a*b +
    70803386900694052750368*a*c +
    3857151586021177786781472*a +
    11796515967476483281656*b^2 +
    23537712583040775019632*b*c +
    2854819231585800352576992*b +
    265401409173047152043616*c +
    9153520100334260774780256
def gHi2 (a b c : ℕ) : ℕ :=
    9620873543680*a^2 +
    19241747087360*a*b +
    19241747087360*a*c +
    8538914363627585*a +
    9620873543680*b^2 +
    19241747087360*b*c +
    9783842581653360*b +
    767753452589648*c +
    40209884423804835
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    482813917916037120*a^2 +
    965627835832074240*a*b +
    965627835832074240*a*c +
    423847483658325284040*a +
    482813917916037120*b^2 +
    965627835832074240*b*c +
    486322961351730776640*b +
    36194241881778174432*c +
    1994545848282223082040
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    400910970091541051520*a^3 +
    1207387802701704677760*a^2*b +
    1212042695128786200960*a^2*c +
    362590696550232945036936*a^2 +
    1212042695128786200960*a*b^2 +
    2428740282684653925120*a*b*c +
    777446707173006089003472*a*b +
    70795216593790417947168*a*c +
    3857089162066928708765472*a +
    11793485438552602081656*b^2 +
    23534682054116893819632*b*c +
    2854782918168572403736992*b +
    265380316687575108995616*c +
    9153411135557247157791456
def conductorHi (a b c : ℕ) : ℕ :=
    2171469151393920*a^3 +
    6514407454181760*a^2*b +
    6514407454181760*a^2*c +
    492614831428971336*a^2 +
    6514407454181760*a*b^2 +
    13028814908363520*a*b*c +
    985229662857942672*a*b +
    129591840489725088*a*c +
    5676859308797112672*a +
    32613418242491256*b^2 +
    65226836484982512*b*c +
    3862911285867919392*b +
    440359996395049056*c +
    14990797111717177056
def slopeHi (a b : ℕ) : ℕ :=
    1216697587555867724160*a^2 +
    2433395175111735448320*a*b +
    70851608681925046279968*a +
    23554319881543643995632*b +
    265531237055082529634016
def interceptHi (a b : ℕ) : ℕ :=
    405565862518622574720*a^3 +
    1216697587555867724160*a^2*b +
    362797537705723933337736*a^2 +
    1216697587555867724160*a*b^2 +
    777673186155923827480272*a*b +
    3858773675528835618211872*a +
    11813123265979352257656*b^2 +
    2855511266236481647773792*b +
    9157076348389288301660256
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
  norm_num [cfg,scale,source11,source12,source13,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source11,source12,source13,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source11,source12,source13,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G7


