-- Prove2me | Definitions.Def_Yukon_a79f98a09bde8d3ca4407ea7
-- name    : Yukon_a79f98a09bde8d3ca4407ea7
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T23:30:33.461081+00:00
-- url     : https://prove2.me/theorems/82fcbb85-51b7-4000-8c38-dab72ca30b82
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberArithmetic6814E.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberArithmetic6814E.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberArithmetic6814E.lean
--
--   yukon-proof-operation:certificate-r12-pair-split-53a62c25a684d81f4515f3aa85d1dec7999618189271b5a64c67de14c31f1aeb
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMDBkNWNmZmRkMWFmMzc4YTZiN2RkNzZkMmI1ZmE3Y2ZhZjdiZTRjZWJjNjlmMWNkOTZiMjdlNzEyZDM0MzVmOSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMi1wYWlyLXNwbGl0LTUzYTYyYzI1YTY4NGQ4MWY0NTE1ZjNhYTg1ZDFkZWM3OTk5NjE4MTg5MjcxYjVhNjRjNjdkZTE0YzMxZjFhZWIiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9hNzlmOThhMDliZGU4ZDNjYTQ0MDdlYTciLCJ2IjoyfQ]

import Definitions.Def_Yukon_72032bf8cc70bee019faae40






































































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G16
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source27,source27,source27]
def scale : ℕ := 9
def denominator : ℕ := 4064904
def gLo0 (b c : ℕ) : ℕ :=
    3135405621545*b +
    25727621663120
def identitySlackLo0 (b c : ℕ) : ℕ :=
    157347195711614280*b +
    1228578428497887630
def helperSlackLo0 (b c : ℕ) : ℕ :=
    1555563595904991468*b^2 +
    3111366541747440492*b*c +
    229894654946226982038*b +
    27804766032226551942*c +
    651074633578070211348
def gLo1 (b c : ℕ) : ℕ :=
    3135405621545*b +
    3135405621545*c +
    218362313197730
def identitySlackLo1 (b c : ℕ) : ℕ :=
    157347195711614280*b +
    157347195711614280*c +
    10833221251426629420
def helperSlackLo1 (b c : ℕ) : ℕ :=
    1555563595904991468*b^2 +
    3111366541747440492*b*c +
    229894654946226982038*b +
    27804766032226551942*c +
    651074633578070211348
def gLo2 (b c : ℕ) : ℕ :=
    103080787968*b^2 +
    206161575936*b*c +
    94766588240680*b +
    9852907357087*c +
    334812160887968
def identitySlackLo2 (b c : ℕ) : ℕ :=
    5173006263386112*b^2 +
    10346012526772224*b*c +
    4705737234634983960*b +
    469443687990403428*c +
    16602096372615672012
def helperSlackLo2 (b c : ℕ) : ℕ :=
    1555563595904991468*b^2 +
    3111366541747440492*b*c +
    229894654946226982038*b +
    27804766032226551942*c +
    651074633578070211348
def conductorLo (b c : ℕ) : ℕ :=
    7015326495480*b^2 +
    14030652990960*b*c +
    567807250703184*b +
    89868171301920*c +
    1909979268943248
def slopeLo (b : ℕ) : ℕ :=
    3112123555503120204*b +
    27809836912206391167
def interceptLo (b : ℕ) : ℕ :=
    1556320609660671180*b^2 +
    229918560531312722589*b +
    651175319053669267458
def gHi0 (a b c : ℕ) : ℕ :=
    103080787968*a^2 +
    206161575936*a*b +
    10213690114975*a +
    3290026803497*b +
    35786689809711
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    5173006263386112*a^2 +
    10346012526772224*a*b +
    487549209912254820*a +
    165106705106693448*b +
    1708368089548759794
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    46323805513859640*a^3 +
    139205200201421184*a^2*b +
    139438983861263448*a^2*c +
    43183487773745317476*a^2 +
    139438983861263448*a*b^2 +
    279111751382369160*a*b*c +
    86357466420045400440*a*b +
    9714326007449435328*a*c +
    451545623211979141236*a +
    1671724051581017412*b^2 +
    3343921236759334644*b*c +
    316043080226318517390*b +
    37309817116062279918*c +
    1059436535055053956956
def gHi1 (a b c : ℕ) : ℕ :=
    103080787968*a^2 +
    206161575936*a*b +
    206161575936*a*c +
    94972749816616*a +
    3290026803497*b +
    3290026803497*c +
    313180441045962
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    5173006263386112*a^2 +
    10346012526772224*a*b +
    10346012526772224*a*c +
    4716083247161756184*a +
    165106705106693448*b +
    165106705106693448*c +
    15541544949727002948
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    46323805513859640*a^3 +
    139205200201421184*a^2*b +
    139438983861263448*a^2*c +
    43183487773745317476*a^2 +
    139438983861263448*a*b^2 +
    279111751382369160*a*b*c +
    86357466420045400440*a*b +
    9714326007449435328*a*c +
    451545623211979141236*a +
    1671724051581017412*b^2 +
    3343921236759334644*b*c +
    316043080226318517390*b +
    37309817116062279918*c +
    1059436535055053956956
def gHi2 (a b c : ℕ) : ℕ :=
    103080787968*a^2 +
    206161575936*a*b +
    206161575936*a*c +
    94972749816616*a +
    103080787968*b^2 +
    206161575936*b*c +
    94972749816616*b +
    10059068933023*c +
    429681829916616
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    5173006263386112*a^2 +
    10346012526772224*a*b +
    10346012526772224*a*c +
    4716083247161756184*a +
    5173006263386112*b^2 +
    10346012526772224*b*c +
    4716083247161756184*b +
    479789700517175652*c +
    21313006613514042084
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    46323805513859640*a^3 +
    139205200201421184*a^2*b +
    139438983861263448*a^2*c +
    43183487773745317476*a^2 +
    139438983861263448*a*b^2 +
    279111751382369160*a*b*c +
    86357466420045400440*a*b +
    9714326007449435328*a*c +
    451545623211979141236*a +
    1671724051581017412*b^2 +
    3343921236759334644*b*c +
    316043080226318517390*b +
    37309817116062279918*c +
    1059436535055053956956
def conductorHi (a b c : ℕ) : ℕ :=
    532803226896*a^3 +
    1598409680688*a^2*b +
    1598409680688*a^2*c +
    97150501016640*a^2 +
    1598409680688*a*b^2 +
    3196819361376*a*b*c +
    194301002033280*a*b +
    34987975566192*a*c +
    1108263263694912*a +
    8613736176168*b^2 +
    17227472352336*b*c +
    760509843055776*b +
    123257737187424*c +
    2921624834848416
def slopeHi (a b : ℕ) : ℕ :=
    139672767521105712*a^2 +
    279345535042211424*a*b +
    9717187074440968980*a +
    3344912034174856620*b +
    37317515279373810531
def interceptHi (a b : ℕ) : ℕ :=
    46557589173701904*a^3 +
    139672767521105712*a^2*b +
    43193221268016147408*a^2 +
    139672767521105712*a*b^2 +
    86368190711731752348*a*b +
    451623853122163190784*a +
    1672714848996539388*b^2 +
    316077242535770925321*b +
    1059605950730226074946
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
  norm_num [cfg,scale,source27,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source27,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source27,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source27,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source27,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G16

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G17
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source28,source28,source28]
def scale : ℕ := 15
def denominator : ℕ := 11291400
def gLo0 (b c : ℕ) : ℕ :=
    4595731333555*b +
    37496182803960
def identitySlackLo0 (b c : ℕ) : ℕ :=
    230632181243124120*b +
    1777480876093717890
def helperSlackLo0 (b c : ℕ) : ℕ :=
    3846425611537127070*b^2 +
    7693894900127121390*b*c +
    664735440555592963884*b +
    67684558157055143604*c +
    1887208737590526041304
def gLo1 (b c : ℕ) : ℕ :=
    4595731333555*b +
    4595731333555*c +
    378955669470660
def identitySlackLo1 (b c : ℕ) : ℕ :=
    230632181243124120*b +
    230632181243124120*c +
    18809056193235179940
def helperSlackLo1 (b c : ℕ) : ℕ :=
    3846425611537127070*b^2 +
    7693894900127121390*b*c +
    664735440555592963884*b +
    67684558157055143604*c +
    1887208737590526041304
def gLo2 (b c : ℕ) : ℕ :=
    171801313280*b^2 +
    343602626560*b*c +
    164905202695471*b +
    14405689214281*c +
    582699951649980
def identitySlackLo2 (b c : ℕ) : ℕ :=
    8621677105643520*b^2 +
    17243354211287040*b*c +
    8192220642677348064*b +
    681244082833393404*c +
    28908685857959072820
def helperSlackLo2 (b c : ℕ) : ℕ :=
    3846425611537127070*b^2 +
    7693894900127121390*b*c +
    664735440555592963884*b +
    67684558157055143604*c +
    1887208737590526041304
def conductorLo (b c : ℕ) : ℕ :=
    11100189174120*b^2 +
    22200378348240*b*c +
    983228366738304*b +
    136045383184224*c +
    3318309319237704
def slopeLo (b : ℕ) : ℕ :=
    7697025931285723140*b +
    67705358258595445029
def interceptLo (b : ℕ) : ℕ :=
    3849556642695728820*b^2 +
    664844784843077867484*b +
    1887677514961238985354
def gHi0 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    15006993810761*a +
    4853433303475*b +
    52245473334081
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    8621677105643520*a^2 +
    17243354211287040*a*b +
    711419952703145724*a +
    243564696901589400*b +
    2475968247361225854
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    128351946007354860*a^3 +
    386029936604740680*a^2*b +
    387004035187416780*a^2*c +
    125213665304562662574*a^2 +
    387004035187416780*a*b^2 +
    774982168957509660*a*b*c +
    250380457621988037048*a*b +
    23948151496190288388*a*c +
    1309766721702334068258*a +
    4168767068432217450*b^2 +
    8339551912499978250*b*c +
    914535879519441693852*b +
    91051716896523448812*c +
    3071760818804404974648
def gHi1 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    165248805322031*a +
    4853433303475*b +
    4853433303475*c +
    543946771512051
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    8621677105643520*a^2 +
    17243354211287040*a*b +
    17243354211287040*a*c +
    8209463996888635104*a +
    243564696901589400*b +
    243564696901589400*c +
    27005587608688177284
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    128351946007354860*a^3 +
    386029936604740680*a^2*b +
    387004035187416780*a^2*c +
    125213665304562662574*a^2 +
    387004035187416780*a*b^2 +
    774982168957509660*a*b*c +
    250380457621988037048*a*b +
    23948151496190288388*a*c +
    1309766721702334068258*a +
    4168767068432217450*b^2 +
    8339551912499978250*b*c +
    914535879519441693852*b +
    91051716896523448812*c +
    3071760818804404974648
def gHi2 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    165248805322031*a +
    171801313280*b^2 +
    343602626560*b*c +
    165248805322031*b +
    14749291840841*c +
    747776955658731
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    8621677105643520*a^2 +
    17243354211287040*a*b +
    17243354211287040*a*c +
    8209463996888635104*a +
    8621677105643520*b^2 +
    17243354211287040*b*c +
    8209463996888635104*b +
    698487437044680444*c +
    37109528177742064404
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    128351946007354860*a^3 +
    386029936604740680*a^2*b +
    387004035187416780*a^2*c +
    125213665304562662574*a^2 +
    387004035187416780*a*b^2 +
    774982168957509660*a*b*c +
    250380457621988037048*a*b +
    23948151496190288388*a*c +
    1309766721702334068258*a +
    4168767068432217450*b^2 +
    8339551912499978250*b*c +
    914535879519441693852*b +
    91051716896523448812*c +
    3071760818804404974648
def conductorHi (a b c : ℕ) : ℕ :=
    888005378160*a^3 +
    2664016134480*a^2*b +
    2664016134480*a^2*c +
    168459340945464*a^2 +
    2664016134480*a*b^2 +
    5328032268960*a*b*c +
    336918681890928*a*b +
    54524354039568*a*c +
    1925607510504288*a +
    13764205308600*b^2 +
    27528410617200*b*c +
    1317483032494752*b +
    187905721089312*c +
    5076345494174688
def slopeHi (a b : ℕ) : ℕ :=
    387978133770092880*a^2 +
    775956267540185760*a*b +
    23959972106420291388*a +
    8343657042241256100*b +
    91083363509711077137
def interceptHi (a b : ℕ) : ℕ :=
    129326044590030960*a^3 +
    387978133770092880*a^2*b +
    125257824149258795724*a^2 +
    387978133770092880*a*b^2 +
    250428721596425448048*a*b +
    1310127747078594979458*a +
    4172872198173495300*b^2 +
    914691539584198656252*b +
    3072547436805265372848
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
  norm_num [cfg,scale,source28,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source28,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source28,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source28,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source28,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G17

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G18
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source29,source29,source29]
def scale : ℕ := 15
def denominator : ℕ := 11291400
def gLo0 (b c : ℕ) : ℕ :=
    4406747922849*b +
    36826146147760
def identitySlackLo0 (b c : ℕ) : ℕ :=
    221148237760254216*b +
    1743855756538977090
def helperSlackLo0 (b c : ℕ) : ℕ :=
    3704166281687583006*b^2 +
    7409376240428033262*b*c +
    718288987756511586636*b +
    66468798786101377914*c +
    2042411149966707206136
def gLo1 (b c : ℕ) : ℕ :=
    4406747922849*b +
    4406747922849*c +
    409639774357440
def identitySlackLo1 (b c : ℕ) : ℕ :=
    221148237760254216*b +
    221148237760254216*c +
    20348907312873347460
def helperSlackLo1 (b c : ℕ) : ℕ :=
    3704166281687583006*b^2 +
    7409376240428033262*b*c +
    718288987756511586636*b +
    66468798786101377914*c +
    2042411149966707206136
def gLo2 (b c : ℕ) : ℕ :=
    171801313280*b^2 +
    343602626560*b*c +
    178512008266303*b +
    14216705803575*c +
    630942590896380
def identitySlackLo2 (b c : ℕ) : ℕ :=
    8621677105643520*b^2 +
    17243354211287040*b*c +
    8875064573443981152*b +
    671760139350523500*c +
    31329694465900410420
def helperSlackLo2 (b c : ℕ) : ℕ :=
    3704166281687583006*b^2 +
    7409376240428033262*b*c +
    718288987756511586636*b +
    66468798786101377914*c +
    2042411149966707206136
def conductorLo (b c : ℕ) : ℕ :=
    10922582678616*b^2 +
    21845165357232*b*c +
    1059243946814016*b +
    134269318229184*c +
    3586139914457736
def slopeLo (b : ℕ) : ℕ :=
    7412507271586635012*b +
    66489556367465451414
def interceptLo (b : ℕ) : ℕ :=
    3707297312846184756*b^2 +
    718404454949373311436*b +
    2042910539136960513786
def gHi0 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    14818010400055*a +
    4664449892769*b +
    51386453267175
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    8621677105643520*a^2 +
    17243354211287040*a*b +
    701936009220275820*a +
    234080753418719496*b +
    2432859184323615150
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    128351946007354860*a^3 +
    386029936604740680*a^2*b +
    387004035187416780*a^2*c +
    135460790075822068782*a^2 +
    387004035187416780*a*b^2 +
    774982168957509660*a*b*c +
    270870254142414615864*a*b +
    23663601912726670860*a*c +
    1417824032151132837954*a +
    4026507738582673386*b^2 +
    8055033252800890122*b*c +
    988579223240786895420*b +
    89551407942106065594*c +
    3324773416858125502968
def gHi1 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    178855610892863*a +
    4664449892769*b +
    4664449892769*c +
    588237681969663
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    8621677105643520*a^2 +
    17243354211287040*a*b +
    17243354211287040*a*c +
    8892307927655268192*a +
    234080753418719496*b +
    234080753418719496*c +
    29228282659092977892
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    128351946007354860*a^3 +
    386029936604740680*a^2*b +
    387004035187416780*a^2*c +
    135460790075822068782*a^2 +
    387004035187416780*a*b^2 +
    774982168957509660*a*b*c +
    270870254142414615864*a*b +
    23663601912726670860*a*c +
    1417824032151132837954*a +
    4026507738582673386*b^2 +
    8055033252800890122*b*c +
    988579223240786895420*b +
    89551407942106065594*c +
    3324773416858125502968
def gHi2 (a b c : ℕ) : ℕ :=
    171801313280*a^2 +
    343602626560*a*b +
    343602626560*a*c +
    178855610892863*a +
    171801313280*b^2 +
    343602626560*b*c +
    178855610892863*b +
    14560308430135*c +
    809626400475963
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    8621677105643520*a^2 +
    17243354211287040*a*b +
    17243354211287040*a*c +
    8892307927655268192*a +
    8621677105643520*b^2 +
    17243354211287040*b*c +
    8892307927655268192*b +
    689003493561810540*c +
    40213380716450035092
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    128351946007354860*a^3 +
    386029936604740680*a^2*b +
    387004035187416780*a^2*c +
    135460790075822068782*a^2 +
    387004035187416780*a*b^2 +
    774982168957509660*a*b*c +
    270870254142414615864*a*b +
    23663601912726670860*a*c +
    1417824032151132837954*a +
    4026507738582673386*b^2 +
    8055033252800890122*b*c +
    988579223240786895420*b +
    89551407942106065594*c +
    3324773416858125502968
def conductorHi (a b c : ℕ) : ℕ :=
    888005378160*a^3 +
    2664016134480*a^2*b +
    2664016134480*a^2*c +
    181247008621752*a^2 +
    2664016134480*a*b^2 +
    5328032268960*a*b*c +
    362494017243504*a*b +
    54169141048560*a*c +
    2079059522619744*a +
    13586598813096*b^2 +
    27173197626192*b*c +
    1419073947923040*b +
    185774443143264*c +
    5484840433833888
def slopeHi (a b : ℕ) : ℕ :=
    387978133770092880*a^2 +
    775956267540185760*a*b +
    23675407061074409160*a +
    8059138382542167972*b +
    89582996573235201294
def interceptHi (a b : ℕ) : ℕ :=
    129326044590030960*a^3 +
    387978133770092880*a^2*b +
    135507175431564318732*a^2 +
    387978133770092880*a*b^2 +
    270920744627898143664*a*b +
    1418206765100978807154*a +
    4030612868323951236*b^2 +
    988743232721966795820*b +
    3325610127721065205968
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
  norm_num [cfg,scale,source29,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source29,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source29,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source29,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source29,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G18

namespace ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G19
open scoped BigOperators
open RCN095 MovingFiberProfile6814 MovingFiberArithmeticBase6814
open MovingFiberCatalog6814 HFreeDirArith6814
def cfg : Fin 3 → Params := ![source30,source30,source30]
def scale : ℕ := 21
def denominator : ℕ := 22131144
def gLo0 (b c : ℕ) : ℕ :=
    6056057045565*b +
    49049989550670
def identitySlackLo0 (b c : ℕ) : ℕ :=
    303917166774633960*b +
    2315606089174528230
def helperSlackLo0 (b c : ℕ) : ℕ :=
    7140146811096244770*b^2 +
    14282854419133169154*b*c +
    1329638194517815099998*b +
    124117208948074302090*c +
    3778993204823162503152
def gLo1 (b c : ℕ) : ℕ :=
    6056057045565*b +
    6056057045565*c +
    541481815290760
def identitySlackLo1 (b c : ℕ) : ℕ :=
    303917166774633960*b +
    303917166774633960*c +
    26881886245678909740
def helperSlackLo1 (b c : ℕ) : ℕ :=
    7140146811096244770*b^2 +
    14282854419133169154*b*c +
    1329638194517815099998*b +
    124117208948074302090*c +
    3778993204823162503152
def gLo2 (b c : ℕ) : ℕ :=
    240521838592*b^2 +
    481043677184*b*c +
    235894242498439*b +
    18863979366122*c +
    833602907364892
def identitySlackLo2 (b c : ℕ) : ℕ :=
    12070347947900928*b^2 +
    24140695895801856*b*c +
    11721381796392626736*b +
    888302505934948428*c +
    41366588381298807228
def helperSlackLo2 (b c : ℕ) : ℕ :=
    7140146811096244770*b^2 +
    14282854419133169154*b*c +
    1329638194517815099998*b +
    124117208948074302090*c +
    3778993204823162503152
def conductorLo (b c : ℕ) : ℕ :=
    15185051852760*b^2 +
    30370103705520*b*c +
    1403444858152032*b +
    181689775580016*c +
    4743423183357288
def slopeLo (b : ℕ) : ℕ :=
    14290779252269118492*b +
    124170000773142132036
def interceptLo (b : ℕ) : ℕ :=
    7148071644232194108*b^2 +
    1329935223042086601699*b +
    3780281075617771757658
def gHi0 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    19705805801194*a +
    6416839803453*b +
    68395010758968
def identitySlackHi0 (a b c : ℕ) : ℕ :=
    12070347947900928*a^2 +
    24140695895801856*a*b +
    930548723752601676*a +
    322022688696485352*b +
    3228049198917237042
def helperSlackHi0 (a b c : ℕ) : ℕ :=
    251023821685105140*a^3 +
    755526193483659192*a^2*b +
    757980921912002964*a^2*c +
    250756982512220432682*a^2 +
    757980921912002964*a*b^2 +
    1518416572252349700*a*b*c +
    501380475985883787552*a*b +
    44188351556144549220*a*c +
    2623446312998970354210*a +
    7771389079555287990*b^2 +
    15547793684479599366*b*c +
    1829882926416007478214*b +
    167167361688099098202*c +
    6151680077956993868508
def gHi1 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    236375286175623*a +
    6416839803453*b +
    6416839803453*c +
    777496316873487
def identitySlackHi1 (a b c : ℕ) : ℕ :=
    12070347947900928*a^2 +
    24140695895801856*a*b +
    24140695895801856*a*c +
    11745522492288428592*a +
    322022688696485352*b +
    322022688696485352*c +
    38609303123957445468
def helperSlackHi1 (a b c : ℕ) : ℕ :=
    251023821685105140*a^3 +
    755526193483659192*a^2*b +
    757980921912002964*a^2*c +
    250756982512220432682*a^2 +
    757980921912002964*a*b^2 +
    1518416572252349700*a*b*c +
    501380475985883787552*a*b +
    44188351556144549220*a*c +
    2623446312998970354210*a +
    7771389079555287990*b^2 +
    15547793684479599366*b*c +
    1829882926416007478214*b +
    167167361688099098202*c +
    6151680077956993868508
def gHi2 (a b c : ℕ) : ℕ :=
    240521838592*a^2 +
    481043677184*a*b +
    481043677184*a*c +
    236375286175623*a +
    240521838592*b^2 +
    481043677184*b*c +
    236375286175623*b +
    19345023043306*c +
    1069737671701923
def identitySlackHi2 (a b c : ℕ) : ℕ :=
    12070347947900928*a^2 +
    24140695895801856*a*b +
    24140695895801856*a*c +
    11745522492288428592*a +
    12070347947900928*b^2 +
    24140695895801856*b*c +
    11745522492288428592*b +
    912443201830750284*c +
    53100040525639334892
def helperSlackHi2 (a b c : ℕ) : ℕ :=
    251023821685105140*a^3 +
    755526193483659192*a^2*b +
    757980921912002964*a^2*c +
    250756982512220432682*a^2 +
    757980921912002964*a*b^2 +
    1518416572252349700*a*b*c +
    501380475985883787552*a*b +
    44188351556144549220*a*c +
    2623446312998970354210*a +
    7771389079555287990*b^2 +
    15547793684479599366*b*c +
    1829882926416007478214*b +
    167167361688099098202*c +
    6151680077956993868508
def conductorHi (a b c : ℕ) : ℕ :=
    1243207529424*a^3 +
    3729622588272*a^2*b +
    3729622588272*a^2*c +
    240567410104056*a^2 +
    3729622588272*a*b^2 +
    7459245176544*a*b*c +
    481134820208112*a*b +
    73883126017440*a*c +
    2752542508070880*a +
    18914674441032*b^2 +
    37829348882064*b*c +
    1880850055771872*b +
    251843279009184*c +
    7256641488853536
def slopeHi (a b : ℕ) : ℕ :=
    760435650340346736*a^2 +
    1520871300680693472*a*b +
    44218247727100009680*a +
    15558173246043892476*b +
    167247594955694044836
def interceptHi (a b : ℕ) : ℕ :=
    253478550113448912*a^3 +
    760435650340346736*a^2*b +
    250875981990956517048*a^2 +
    760435650340346736*a*b^2 +
    501509855026184165028*a*b +
    2624431443386846077404*a +
    7781768641119581100*b^2 +
    1830304424523722669847*b +
    6153836534389171105614
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
  norm_num [cfg,scale,source30,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_zero,firstLo,gLo0,gLo1,gLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  <;> ring
theorem graph_eq_hi (f : FlagDegree) (a b c : ℕ) :
    graphDir cfg scale f (a+1) b c = f.zOnly*gHi0 a b c+f.yz*gHi1 a b c+f.all*gHi2 a b c := by
  norm_num [cfg,scale,source30,graphDir,normal,raw,MovingFiberThreeSources6811.weight,MovingFiberThreeSources6811.direction,Params.d,Params.flag,SecondJetRelaxedFlag.budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag,firstDir_succ,firstHi,gHi0,gHi1,gHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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
    norm_num [cfg,scale,source30,full,slope,intercept,slopeLo,interceptLo,gLo0,gLo1,gLo2,coeff,pairNumerator,
      conductor,conductorLo,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
  | succ a =>
    rw [graph_eq_hi]
    norm_num [cfg,scale,source30,full,slope,intercept,slopeHi,interceptHi,gHi0,gHi1,gHi2,coeff,pairNumerator,
      conductor,conductorHi,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
    <;> ring
theorem helper_cap (a b c : ℕ) (j : Fin 3) :
    helper (cfg j) a b c/50184 ≤ full a b c/denominator := by
  have he : scale^2*helper (cfg j) a b c ≤ full a b c := by
    cases a with
    | zero =>
      fin_cases j
      · have h : full 0 b c = scale^2*helper (cfg 0) 0 b c+helperSlackLo0 b c := by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 1) 0 b c+helperSlackLo1 b c := by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full 0 b c = scale^2*helper (cfg 2) 0 b c+helperSlackLo2 b c := by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeLo,interceptLo,helper,pairNumerator,helperSlackLo2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
    | succ a =>
      fin_cases j
      · have h : full (a+1) b c = scale^2*helper (cfg 0) (a+1) b c+helperSlackHi0 a b c := by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi0,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 1) (a+1) b c+helperSlackHi1 a b c := by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi1,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
          <;> ring
        rw [h]
        exact Nat.le_add_right _ _
      · have h : full (a+1) b c = scale^2*helper (cfg 2) (a+1) b c+helperSlackHi2 a b c := by
          norm_num [cfg,scale,source30,full,slope,intercept,slopeHi,interceptHi,helper,pairNumerator,helperSlackHi2,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
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




end ProximityPrize.SubmissionLower.MovingFiberArithmetic6814.G19


