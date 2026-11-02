-- Prove2me | Definitions.Def_OAIQ098D000
-- name    : OAIQ098D000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-01T14:21:36.643434+00:00
-- url     : https://prove2.me/theorems/889fe81a-1092-42f4-bb73-005478dd99e8
-- title:
--   Definitions bundle OAIQ098D000 of the split of OpenAI, A sharp Fourier certificate for planar circle packing (result family 090)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.sharp_fourier_certificate`, carved from OpenAI's openai/math development (OpenAI, *A sharp Fourier certificate for planar circle packing (result family 090)*, OpenAI Math Release, September 23, 2026, result family 90, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 1945 declarations of OpenAI's Lean: 1496 definitions, 1 inductive type or structure and 448 theorems. The definitions and types are `OAI.SharpPlanar.B`, `OAI.SharpPlanar.Bernstein0.N1_right.t0`, `OAI.SharpPlanar.Bernstein0.N1_right.t1`, `OAI.SharpPlanar.Bernstein0.N1_right.t10`, `OAI.SharpPlanar.Bernstein0.N1_right.t11`, `OAI.SharpPlanar.Bernstein0.N1_right.t12`, `OAI.SharpPlanar.Bernstein0.N1_right.t13`, `OAI.SharpPlanar.Bernstein0.N1_right.t14`, `OAI.SharpPlanar.Bernstein0.N1_right.t15`, `OAI.SharpPlanar.Bernstein0.N1_right.t16`, `OAI.SharpPlanar.Bernstein0.N1_right.t17`, `OAI.SharpPlanar.Bernstein0.N1_right.t18`, `OAI.SharpPlanar.Bernstein0.N1_right.t19`, `OAI.SharpPlanar.Bernstein0.N1_right.t2`, `OAI.SharpPlanar.Bernstein0.N1_right.t20`, `OAI.SharpPlanar.Bernstein0.N1_right.t21`, `OAI.SharpPlanar.Bernstein0.N1_right.t22`, `OAI.SharpPlanar.Bernstein0.N1_right.t23`, `OAI.SharpPlanar.Bernstein0.N1_right.t24`, `OAI.SharpPlanar.Bernstein0.N1_right.t25`, `OAI.SharpPlanar.Bernstein0.N1_right.t26`, `OAI.SharpPlanar.Bernstein0.N1_right.t27`, `OAI.SharpPlanar.Bernstein0.N1_right.t28`, `OAI.SharpPlanar.Bernstein0.N1_right.t3`, `OAI.SharpPlanar.Bernstein0.N1_right.t4`, `OAI.SharpPlanar.Bernstein0.N1_right.t5`, `OAI.SharpPlanar.Bernstein0.N1_right.t6`, `OAI.SharpPlanar.Bernstein0.N1_right.t7`, `OAI.SharpPlanar.Bernstein0.N1_right.t8`, `OAI.SharpPlanar.Bernstein0.N1_right.t9`, `OAI.SharpPlanar.Bernstein0.N1_right.ts`, `OAI.SharpPlanar.Bernstein1.N0_right.t0`, `OAI.SharpPlanar.Bernstein1.N0_right.t1`, `OAI.SharpPlanar.Bernstein1.N0_right.t10`, `OAI.SharpPlanar.Bernstein1.N0_right.t11`, `OAI.SharpPlanar.Bernstein1.N0_right.t12`, `OAI.SharpPlanar.Bernstein1.N0_right.t13`, `OAI.SharpPlanar.Bernstein1.N0_right.t14`, `OAI.SharpPlanar.Bernstein1.N0_right.t15`, `OAI.SharpPlanar.Bernstein1.N0_right.t16` and 1457 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `PlanarPacking_Cardinal`, `PlanarPacking_Certificate_Bernstein0`, `PlanarPacking_Certificate_Bernstein1`, `PlanarPacking_Certificate_Bernstein12`, `PlanarPacking_Certificate_Bernstein13`, `PlanarPacking_Certificate_Bernstein15`, `PlanarPacking_Certificate_Bernstein16`, `PlanarPacking_Certificate_Bernstein19`, `PlanarPacking_Certificate_Bernstein21`, `PlanarPacking_Certificate_Bernstein24`, `PlanarPacking_Certificate_Bernstein25`, `PlanarPacking_Certificate_HighMoments0_0`, `PlanarPacking_Certificate_HighMoments0_1`, `PlanarPacking_Certificate_HighMoments0_2`, `PlanarPacking_Certificate_HighMoments0_3`, `PlanarPacking_Certificate_HighMoments0_4`, `PlanarPacking_Certificate_HighMoments0_5`, `PlanarPacking_Certificate_HighMoments0_6`, `PlanarPacking_Certificate_HighMoments0_7`, `PlanarPacking_Certificate_HighMoments1_0`, `PlanarPacking_Certificate_HighMoments1_1`, `PlanarPacking_Certificate_HighMoments1_2`, `PlanarPacking_Certificate_HighMoments1_3`, `PlanarPacking_Certificate_HighMoments1_4`, `PlanarPacking_Certificate_HighMoments1_5`, `PlanarPacking_Certificate_HighMoments1_6`, `PlanarPacking_Certificate_HighMoments1_7`, `PlanarPacking_Certificate_LowBlock12_0`, `PlanarPacking_Certificate_LowBlock12_1`, `PlanarPacking_Certificate_LowBlock12_10`, `PlanarPacking_Certificate_LowBlock12_11`, `PlanarPacking_Certificate_LowBlock13_0`, `PlanarPacking_Certificate_LowBlock13_1`, `PlanarPacking_Certificate_LowBlock13_10`, `PlanarPacking_Certificate_LowBlock13_11`, `PlanarPacking_Certificate_LowBlock15_0`, `PlanarPacking_Certificate_LowBlock15_1`, `PlanarPacking_Certificate_LowBlock15_10`, `PlanarPacking_Certificate_LowBlock15_11`, `PlanarPacking_Certificate_LowBlock16_0`, `PlanarPacking_Certificate_LowBlock16_1`, `PlanarPacking_Certificate_LowBlock16_10`, `PlanarPacking_Certificate_LowBlock16_11`, `PlanarPacking_Certificate_LowBlock19_0`, `PlanarPacking_Certificate_LowBlock19_1`, `PlanarPacking_Certificate_LowBlock19_10`, `PlanarPacking_Certificate_LowBlock19_11`, `PlanarPacking_Certificate_LowBlock21_0`, `PlanarPacking_Certificate_LowBlock21_1`, `PlanarPacking_Certificate_LowBlock21_10`, `PlanarPacking_Certificate_LowBlock21_11`, `PlanarPacking_Certificate_LowBlock24_0`, `PlanarPacking_Certificate_LowBlock24_1`, `PlanarPacking_Certificate_LowBlock24_10`, `PlanarPacking_Certificate_LowBlock24_11`, `PlanarPacking_Certificate_LowBlock25_0`, `PlanarPacking_Certificate_LowBlock25_1`, `PlanarPacking_Certificate_LowBlock25_10`, `PlanarPacking_Intervals`, `PlanarPacking_Roots`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ098D003`, `OAIQ098D004` and `OAIQ098D005`.
-- source:
--   OpenAI, A sharp Fourier certificate for planar circle packing (result family 090), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 90; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-sharp-Fourier-certificate-for-planar-circle-packing-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar

noncomputable def B : ℝ := 4 / 3

theorem B_pos : 0 < B := by norm_num [B]

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Intervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Integer interval arithmetic for a planar Fourier certificate

Real and complex interval operations with precision `10^30`, including checked
Taylor bounds for the complex exponential and rational Fourier kernels.
-/

namespace SharpPlanar
namespace IntegerIntervals

structure RBox where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

end IntegerIntervals
end SharpPlanar

namespace SharpPlanar.IntegerIntervals

def RBox.add (a b : RBox) : RBox := ⟨a.lo+b.lo,a.hi+b.hi⟩
def RBox.scale (a : RBox) (m n : ℤ) : RBox :=
  ⟨min (m*a.lo) (m*a.hi)/n,-((-max (m*a.lo) (m*a.hi))/n)⟩

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Roots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Certified roots of unity

Integer enclosures for the 1024th roots of unity, obtained from a certified
Taylor approximation and repeated squaring.
-/

namespace SharpPlanar
noncomputable def rootPhase (n : ℕ) : ℂ := Complex.exp (Complex.I*Real.pi*((n:ℂ)/512))


end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm0_1_0_0
 def realAnswer : RBox := ⟨(-24448959631044601),24448954619137686⟩
end hm0_1_0_0
namespace hm0_1_0_1
 def realAnswer : RBox := ⟨(-1210671473200344404375778537057),(-1210671473200244910121720325821)⟩
end hm0_1_0_1
namespace hm0_1_0_2
 def realAnswer : RBox := ⟨1214162363742902447548229809196,1214162363743013634603649998732⟩
end hm0_1_0_2
namespace hm0_1_0_3
 def realAnswer : RBox := ⟨428718573182907768069444814185,428718573182993679139231138008⟩
end hm0_1_0_3
namespace hm0_1_0_4
 def realAnswer : RBox := ⟨(-496044856818584438499117885099),(-496044856818533951524540136447)⟩
end hm0_1_0_4
namespace hm0_1_0_5
 def realAnswer : RBox := ⟨(-58295461630874463886179161019),(-58295461630850584496504718929)⟩
end hm0_1_0_5
namespace hm0_1_0_6
 def realAnswer : RBox := ⟨80679092179569339833294724496,80679092179578783028477903224⟩
end hm0_1_0_6
namespace hm0_1_0_7
 def realAnswer : RBox := ⟨3761398410713277041522667687,3761398410716485438735447639⟩
end hm0_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm0_1_0_8
 def realAnswer : RBox := ⟨(-6508966480212281669360378082),(-6508966480211325931029241111)⟩
end hm0_1_0_8
namespace hm0_1_0_9
 def realAnswer : RBox := ⟨(-106944874300176853550358949),(-106944874299923307162459031)⟩
end hm0_1_0_9
namespace hm0_1_0_10
 def realAnswer : RBox := ⟨221951738524540590623502677,221951738524601238618449189⟩
end hm0_1_0_10
namespace hm0_1_0_11
 def realAnswer : RBox := ⟨(-152632981748537872273203),(-152632981735325695175005)⟩
end hm0_1_0_11
namespace hm0_1_0_12
 def realAnswer : RBox := ⟨6400061130279449545453534,6400061130282092834939028⟩
end hm0_1_0_12
namespace hm0_1_0_13
 def realAnswer : RBox := ⟨74521836071232748500632,74521836071721904649074⟩
end hm0_1_0_13
namespace hm0_1_0_14
 def realAnswer : RBox := ⟨(-1169580228323601051241149),(-1169580228323516709208056)⟩
end hm0_1_0_14
namespace hm0_1_0_15
 def realAnswer : RBox := ⟨826454586247845063089,826454586261583235202⟩
end hm0_1_0_15
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm0_1_0_16
 def realAnswer : RBox := ⟨71325706393882425452530,71325706393884671138174⟩
end hm0_1_0_16
namespace hm0_1_0_17
 def realAnswer : RBox := ⟨(-221057097607106827754),(-221057097606615388913)⟩
end hm0_1_0_17
namespace hm0_1_0_18
 def realAnswer : RBox := ⟨(-2831610887005531949278),(-2831610887005292667953)⟩
end hm0_1_0_18
namespace hm0_1_0_19
 def realAnswer : RBox := ⟨10763421339855441549,10763421340060466252⟩
end hm0_1_0_19
namespace hm0_1_0_20
 def realAnswer : RBox := ⟨83580132483208129517,83580132483408741371⟩
end hm0_1_0_20
namespace hm0_1_0_21
 def realAnswer : RBox := ⟨(-319805900833919711),(-319805900633848428)⟩
end hm0_1_0_21
namespace hm0_1_0_22
 def realAnswer : RBox := ⟨(-1944951469728229068),(-1944951469528220914)⟩
end hm0_1_0_22
namespace hm0_1_0_23
 def realAnswer : RBox := ⟨6916554039350288,6916554239351392⟩
end hm0_1_0_23
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm0_1_0_24
 def realAnswer : RBox := ⟨36936424804293756,36936425004294103⟩
end hm0_1_0_24
namespace hm0_1_0_25
 def realAnswer : RBox := ⟨(-117074113195878),(-117073913195606)⟩
end hm0_1_0_25
namespace hm0_1_0_26
 def realAnswer : RBox := ⟨(-586147330974888),(-586147130974626)⟩
end hm0_1_0_26
namespace hm0_1_0_27
 def realAnswer : RBox := ⟨1614966286308,1615166286570⟩
end hm0_1_0_27
namespace hm0_1_0_28
 def realAnswer : RBox := ⟨7910727178869,7910927179130⟩
end hm0_1_0_28
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm0_0_1_0
 def realAnswer : RBox := ⟨3010659550390328347580891333668,3010659550390456194254402638350⟩
end hm0_0_1_0
namespace hm0_0_1_1
 def realAnswer : RBox := ⟨(-1104357602907533951072884969254),(-1104357602906827178053854241991)⟩
end hm0_0_1_1
namespace hm0_0_1_2
 def realAnswer : RBox := ⟨(-17550085680319701709756418293605),(-17550085680317701027309256824172)⟩
end hm0_0_1_2
namespace hm0_0_1_3
 def realAnswer : RBox := ⟨45345852481434039722628389604683,45345852481438507834976365581269⟩
end hm0_0_1_3
namespace hm0_0_1_4
 def realAnswer : RBox := ⟨(-85630948272253578176113465121898),(-85630948272246677304576204891476)⟩
end hm0_0_1_4
namespace hm0_0_1_5
 def realAnswer : RBox := ⟨168182116509874963835979184943702,168182116509885700295468145064431⟩
end hm0_0_1_5
namespace hm0_0_1_6
 def realAnswer : RBox := ⟨(-298396026175443591787164581241329),(-298396026175430225249612134385756)⟩
end hm0_0_1_6
namespace hm0_0_1_7
 def realAnswer : RBox := ⟨431980992491815693618313067907276,431980992491830267323752932558489⟩
end hm0_0_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm0_0_1_8
 def realAnswer : RBox := ⟨(-514767496895185195312324312923660),(-514767496895170881377804925461262)⟩
end hm0_0_1_8
namespace hm0_0_1_9
 def realAnswer : RBox := ⟨521611502763516504042754962131435,521611502763528878646427694865593⟩
end hm0_0_1_9
namespace hm0_0_1_10
 def realAnswer : RBox := ⟨(-459492216934036899295484007287020),(-459492216934027106344745170211737)⟩
end hm0_0_1_10
namespace hm0_0_1_11
 def realAnswer : RBox := ⟨355545467394844363862219513540572,355545467394851416009086092940961⟩
end hm0_0_1_11
namespace hm0_0_1_12
 def realAnswer : RBox := ⟨(-243741828999452007878028467011855),(-243741828999447338972492377144575)⟩
end hm0_0_1_12
namespace hm0_0_1_13
 def realAnswer : RBox := ⟨150599365923713264029135229374003,150599365923716124744103393099605⟩
end hm0_0_1_13
namespace hm0_0_1_14
 def realAnswer : RBox := ⟨(-86512568353885195007184005987837),(-86512568353883564104085655604358)⟩
end hm0_0_1_14
namespace hm0_0_1_15
 def realAnswer : RBox := ⟨48128028202517417023954886841337,48128028202518284600577988971039⟩
end hm0_0_1_15
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm0_0_1_16
 def realAnswer : RBox := ⟨(-26777102368603967035116093614676),(-26777102368603532915793069511404)⟩
end hm0_0_1_16
namespace hm0_0_1_17
 def realAnswer : RBox := ⟨14956371457860130028248334176224,14956371457860334655044767134212⟩
end hm0_0_1_17
namespace hm0_0_1_18
 def realAnswer : RBox := ⟨(-8202264556067755731914800218880),(-8202264556067664580206858725215)⟩
end hm0_0_1_18
namespace hm0_0_1_19
 def realAnswer : RBox := ⟨4295649154011866640960536104256,4295649154011905192654452623028⟩
end hm0_0_1_19
namespace hm0_0_1_20
 def realAnswer : RBox := ⟨(-2108233165876322154586930455870),(-2108233165876306645690147764441)⟩
end hm0_0_1_20
namespace hm0_0_1_21
 def realAnswer : RBox := ⟨961936152241727756945143968822,961936152241733712009435290838⟩
end hm0_0_1_21
namespace hm0_0_1_22
 def realAnswer : RBox := ⟨(-407950579738183056577665640195),(-407950579738180872937663944940)⟩
end hm0_0_1_22
namespace hm0_0_1_23
 def realAnswer : RBox := ⟨161506054516561138635748433906,161506054516561907083494326939⟩
end hm0_0_1_23
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments0_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm0_0_1_24
 def realAnswer : RBox := ⟨(-60111018390569534337579576698),(-60111018390569274520504832233)⟩
end hm0_0_1_24
namespace hm0_0_1_25
 def realAnswer : RBox := ⟨21219246659894634740476188456,21219246659894719244400633586⟩
end hm0_0_1_25
namespace hm0_0_1_26
 def realAnswer : RBox := ⟨(-7174788953643087880237373880),(-7174788953643061346939911995)⟩
end hm0_0_1_26
namespace hm0_0_1_27
 def realAnswer : RBox := ⟨2347091485270828437404879883,2347091485270836498186018224⟩
end hm0_0_1_27
namespace hm0_0_1_28
 def realAnswer : RBox := ⟨(-749247023254399595302799217),(-749247023254397220897118485)⟩
end hm0_0_1_28
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein0
open IntegerIntervals CachedData
namespace N1_right
noncomputable def t0 : RBox := {lo := 3010659550390303898621260289067, hi := 3010659550390480643209021776036}
lemma t0_checked : ((hm0_1_0_0.realAnswer).add hm0_0_1_0.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -1157514538053939177724331753156, hi := -1157514538053536044087787283906}
lemma t1_checked : ((hm0_1_0_1.realAnswer).add hm0_0_1_1.realAnswer).scale (1) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -4083980829144199815552047121103, hi := -4083980829143671848176401706360}
lemma t2_checked : ((hm0_1_0_2.realAnswer).add hm0_0_1_2.realAnswer).scale (1) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 5721821381827118436337229302358, hi := 5721821381827687689264449589910}
lemma t3_checked : ((hm0_1_0_3.realAnswer).add hm0_0_1_3.realAnswer).scale (1) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := -5382937070567010163413286437938, hi := -5382937070566575703506296564245}
lemma t4_checked : ((hm0_1_0_4.realAnswer).add hm0_0_1_4.realAnswer).scale (1) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := 5253869407757627792877906430708, hi := 5253869407757964053467863760797}
lemma t5_checked : ((hm0_1_0_5.realAnswer).add hm0_0_1_5.realAnswer).scale (1) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -4661177298176000350739551351826, hi := -4661177298175791351040369632539}
lemma t6_checked : ((hm0_1_0_6.realAnswer).add hm0_0_1_6.realAnswer).scale (1) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 3374880889767393803869957738866, hi := 3374880889767507686009309906298}
lemma t7_checked : ((hm0_1_0_7.realAnswer).add hm0_0_1_7.realAnswer).scale (1) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := -2010835960397130498414037786335, hi := -2010835960397074580873968573056}
lemma t8_checked : ((hm0_1_0_8.realAnswer).add hm0_0_1_8.realAnswer).scale (1) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 1018772257458285554425588694868, hi := 1018772257458309724068594789857}
lemma t9_checked : ((hm0_1_0_9.realAnswer).add hm0_0_1_9.realAnswer).scale (1) 512=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := -448722651349900756596575570102, hi := -448722651349891193108893116955}
lemma t10_checked : ((hm0_1_0_10.realAnswer).add hm0_0_1_10.realAnswer).scale (1) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := 173606185176861026422696113900, hi := 173606185176864469860234569222}
lemma t11_checked : ((hm0_1_0_11.realAnswer).add hm0_0_1_11.realAnswer).scale (1) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -59507280908054413476215557022, hi := -59507280908053273606054575733}
lemma t12_checked : ((hm0_1_0_12.realAnswer).add hm0_0_1_12.realAnswer).scale (1) 4096=t12 := by decide +kernel
noncomputable def t13 : RBox := {lo := 18383711669706433117720700424, hi := 18383711669706782326150549042}
lemma t13_checked : ((hm0_1_0_13.realAnswer).add hm0_0_1_13.realAnswer).scale (1) 8192=t13 := by decide +kernel
noncomputable def t14 : RBox := {lo := -5280308198453700154466861404, hi := -5280308198453600612036277149}
lemma t14_checked : ((hm0_1_0_14.realAnswer).add hm0_0_1_14.realAnswer).scale (1) 16384=t14 := by decide +kernel
noncomputable def t15 : RBox := {lo := 1468750860697749988104331417, hi := 1468750860697776464442125617}
lemma t15_checked : ((hm0_1_0_15.realAnswer).add hm0_0_1_15.realAnswer).scale (1) 32768=t15 := by decide +kernel
noncomputable def t16 : RBox := {lo := -408586155659153146991480533, hi := -408586155659146522856268285}
lemma t16_checked : ((hm0_1_0_16.realAnswer).add hm0_0_1_16.realAnswer).scale (1) 65536=t16 := by decide +kernel
noncomputable def t17 : RBox := {lo := 114108058606255134053354090, hi := 114108058606256695231919493}
lemma t17_checked : ((hm0_1_0_17.realAnswer).add hm0_0_1_17.realAnswer).scale (1) 131072=t17 := by decide +kernel
noncomputable def t18 : RBox := {lo := -31289156184766260600739793, hi := -31289156184765912884567838}
lemma t18_checked : ((hm0_1_0_18.realAnswer).add hm0_0_1_18.realAnswer).scale (1) 262144=t18 := by decide +kernel
noncomputable def t19 : RBox := {lo := 8193300540967235684014113, hi := 8193300540967309215535189}
lemma t19_checked : ((hm0_1_0_19.realAnswer).add hm0_0_1_19.realAnswer).scale (1) 524288=t19 := by decide +kernel
noncomputable def t20 : RBox := {lo := -2010567823212377569297526, hi := -2010567823212362778860796}
lemma t20_checked : ((hm0_1_0_20.realAnswer).add hm0_0_1_20.realAnswer).scale (1) 1048576=t20 := by decide +kernel
noncomputable def t21 : RBox := {lo := 458686901207641578218607, hi := 458686901207644417814637}
lemma t21_checked : ((hm0_1_0_21.realAnswer).add hm0_0_1_21.realAnswer).scale (1) 2097152=t21 := by decide +kernel
noncomputable def t22 : RBox := {lo := -97262997565299989711617, hi := -97262997565299469091222}
lemma t22_checked : ((hm0_1_0_22.realAnswer).add hm0_0_1_22.realAnswer).scale (1) 4194304=t22 := by decide +kernel
noncomputable def t23 : RBox := {lo := 19253022017069823168490, hi := 19253022017069914774625}
lemma t23_checked : ((hm0_1_0_23.realAnswer).add hm0_0_1_23.realAnswer).scale (1) 8388608=t23 := by decide +kernel
noncomputable def t24 : RBox := {lo := -3582895898254668588208, hi := -3582895898254653101891}
lemma t24_checked : ((hm0_1_0_24.realAnswer).add hm0_0_1_24.realAnswer).scale (1) 16777216=t24 := by decide +kernel
noncomputable def t25 : RBox := {lo := 632382829782203366350, hi := 632382829782205884770}
lemma t25_checked : ((hm0_1_0_25.realAnswer).add hm0_0_1_25.realAnswer).scale (1) 33554432=t25 := by decide +kernel
noncomputable def t26 : RBox := {lo := -106912686730081946069, hi := -106912686730081550688}
lemma t26_checked : ((hm0_1_0_26.realAnswer).add hm0_0_1_26.realAnswer).scale (1) 67108864=t26 := by decide +kernel
noncomputable def t27 : RBox := {lo := 17487194279363975319, hi := 17487194279364035379}
lemma t27_checked : ((hm0_1_0_27.realAnswer).add hm0_0_1_27.realAnswer).scale (1) 134217728=t27 := by decide +kernel
noncomputable def t28 : RBox := {lo := -2791162666881053465, hi := -2791162666881044618}
lemma t28_checked : ((hm0_1_0_28.realAnswer).add hm0_0_1_28.realAnswer).scale (1) 268435456=t28 := by decide +kernel
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_right
end SharpPlanar.Bernstein0

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm1_0_0_1
 def realAnswer : RBox := ⟨(-1225758922461319426931572838031),(-1225758922461149016321987231850)⟩
end hm1_0_0_1
namespace hm1_0_0_2
 def realAnswer : RBox := ⟨1680574261399774028471233911113,1680574261399964523433255358643⟩
end hm1_0_0_2
namespace hm1_1_0_2
 def realAnswer : RBox := ⟨54478416604604515435712638689,54478416604760935657242113910⟩
end hm1_1_0_2
namespace hm1_0_0_3
 def realAnswer : RBox := ⟨(-773780270448736356370006686208),(-773780270448589159371996683733)⟩
end hm1_0_0_3
namespace hm1_1_0_3
 def realAnswer : RBox := ⟨(-739019591200013506333598869115),(-739019591199892646865147446884)⟩
end hm1_1_0_3
namespace hm1_0_0_4
 def realAnswer : RBox := ⟨16364212703555157063475202609,16364212703641654919736793766⟩
end hm1_0_0_4
namespace hm1_1_0_4
 def realAnswer : RBox := ⟨133942695107026407899169581996,133942695107097429856090733322⟩
end hm1_1_0_4
namespace hm1_0_0_5
 def realAnswer : RBox := ⟨219577098621116062718362857792,219577098621156970358711037936⟩
end hm1_0_0_5
namespace hm1_1_0_5
 def realAnswer : RBox := ⟨185765629491042936599943064335,185765629491076526533835309972⟩
end hm1_1_0_5
namespace hm1_0_0_6
 def realAnswer : RBox := ⟨(-104934782193729699166911380043),(-104934782193713524187448081055)⟩
end hm1_0_0_6
namespace hm1_1_0_6
 def realAnswer : RBox := ⟨(-34633529171800247698261834755),(-34633529171786965540536939162)⟩
end hm1_1_0_6
namespace hm1_0_0_7
 def realAnswer : RBox := ⟨(-17379845234895947909623001487),(-17379845234890453161894529461)⟩
end hm1_0_0_7
namespace hm1_1_0_7
 def realAnswer : RBox := ⟨(-23660241970889155890234415281),(-23660241970884643635250013982)⟩
end hm1_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm1_0_0_8
 def realAnswer : RBox := ⟨20681404341724455315015388166,20681404341726091853018676224⟩
end hm1_0_0_8
namespace hm1_1_0_8
 def realAnswer : RBox := ⟨3047549066815183075486235838,3047549066816527053965696369⟩
end hm1_1_0_8
namespace hm1_0_0_9
 def realAnswer : RBox := ⟨(-192157740189679552738353743),(-192157740189245477410856970)⟩
end hm1_0_0_9
namespace hm1_1_0_9
 def realAnswer : RBox := ⟨1915053209130798947974597225,1915053209131155440931575377⟩
end hm1_1_0_9
namespace hm1_0_0_10
 def realAnswer : RBox := ⟨(-2118750738657134773328463959),(-2118750738657030963704018648)⟩
end hm1_0_0_10
namespace hm1_1_0_10
 def realAnswer : RBox := ⟨(-46163689266106730583253268),(-46163689266021471171594131)⟩
end hm1_1_0_10
namespace hm1_0_0_11
 def realAnswer : RBox := ⟨134720674306592185858891110,134720674306614795887670167⟩
end hm1_0_0_11
namespace hm1_1_0_11
 def realAnswer : RBox := ⟨(-109973097246079516208266025),(-109973097246060945690847975)⟩
end hm1_1_0_11
namespace hm1_0_0_12
 def realAnswer : RBox := ⟨142433008547267620532466221,142433008547272142855578753⟩
end hm1_0_0_12
namespace hm1_1_0_12
 def realAnswer : RBox := ⟨(-12985594244454144300326603),(-12985594244450429763701046)⟩
end hm1_1_0_12
namespace hm1_0_0_13
 def realAnswer : RBox := ⟨(-12114505194272512278577166),(-12114505194271675713947341)⟩
end hm1_0_0_13
namespace hm1_1_0_13
 def realAnswer : RBox := ⟨4774567117637221843092704,4774567117637909032006367⟩
end hm1_1_0_13
namespace hm1_0_0_14
 def realAnswer : RBox := ⟨(-6924816862509831528552993),(-6924816862509687439679326)⟩
end hm1_0_0_14
namespace hm1_1_0_14
 def realAnswer : RBox := ⟨1364698690041321615036853,1364698690041440009236674⟩
end hm1_1_0_14
namespace hm1_0_0_15
 def realAnswer : RBox := ⟨642540306510718984877646,642540306510742329895215⟩
end hm1_0_0_15
namespace hm1_1_0_15
 def realAnswer : RBox := ⟨(-163045281845760766221900),(-163045281845741553729503)⟩
end hm1_1_0_15
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm1_0_0_16
 def realAnswer : RBox := ⟨257361890922195798413154,257361890922199494743073⟩
end hm1_0_0_16
namespace hm1_1_0_16
 def realAnswer : RBox := ⟨(-76163293351750522581626),(-76163293351747450432766)⟩
end hm1_1_0_16
namespace hm1_0_0_17
 def realAnswer : RBox := ⟨(-24127968632305518498428),(-24127968632304820540406)⟩
end hm1_0_0_17
namespace hm1_1_0_17
 def realAnswer : RBox := ⟨4495498017964760747323,4495498017965369816632⟩
end hm1_1_0_17
namespace hm1_0_0_18
 def realAnswer : RBox := ⟨(-7584661952056071707019),(-7584661952055804611391)⟩
end hm1_0_0_18
namespace hm1_1_0_18
 def realAnswer : RBox := ⟨2935921515465229489200,2935921515465484609290⟩
end hm1_1_0_18
namespace hm1_0_0_19
 def realAnswer : RBox := ⟨691676549797732804235,691676549797941383930⟩
end hm1_0_0_19
namespace hm1_1_0_19
 def realAnswer : RBox := ⟨(-101971891019461110697),(-101971891019254062210)⟩
end hm1_1_0_19
namespace hm1_0_0_20
 def realAnswer : RBox := ⟨182004607731453938105,182004607731654982353⟩
end hm1_0_0_20
namespace hm1_1_0_20
 def realAnswer : RBox := ⟨(-85569319015377837425),(-85569319015176979487)⟩
end hm1_1_0_20
namespace hm1_0_0_21
 def realAnswer : RBox := ⟨(-15805389286352378155),(-15805389286152256690)⟩
end hm1_0_0_21
namespace hm1_1_0_21
 def realAnswer : RBox := ⟨1931018218645742308,1931018218845842134⟩
end hm1_1_0_21
namespace hm1_0_0_22
 def realAnswer : RBox := ⟨(-3629044586589288882),(-3629044586389275124)⟩
end hm1_0_0_22
namespace hm1_1_0_22
 def realAnswer : RBox := ⟨1978496832232552888,1978496832432564232⟩
end hm1_1_0_22
namespace hm1_0_0_23
 def realAnswer : RBox := ⟨296353767725826611,296353767925828313⟩
end hm1_0_0_23
namespace hm1_1_0_23
 def realAnswer : RBox := ⟨(-30907396157424946),(-30907395957423507)⟩
end hm1_1_0_23
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm1_0_0_24
 def realAnswer : RBox := ⟨61108770539377101,61108770739377574⟩
end hm1_0_0_24
namespace hm1_1_0_24
 def realAnswer : RBox := ⟨(-37433506369303035),(-37433506169302597)⟩
end hm1_1_0_24
namespace hm1_0_0_25
 def realAnswer : RBox := ⟨(-4657446321134645),(-4657446121134359)⟩
end hm1_0_0_25
namespace hm1_1_0_25
 def realAnswer : RBox := ⟨422702839195894,422703039196168⟩
end hm1_1_0_25
namespace hm1_0_0_26
 def realAnswer : RBox := ⟨(-880669436170530),(-880669236170190)⟩
end hm1_0_0_26
namespace hm1_1_0_26
 def realAnswer : RBox := ⟨592588231936338,592588431936669⟩
end hm1_1_0_26
namespace hm1_0_0_27
 def realAnswer : RBox := ⟨62370023444710,62370223444978⟩
end hm1_0_0_27
namespace hm1_1_0_27
 def realAnswer : RBox := ⟨(-4988399822129),(-4988199821864)⟩
end hm1_1_0_27
namespace hm1_0_0_28
 def realAnswer : RBox := ⟨10985052041717,10985252042064⟩
end hm1_0_0_28
namespace hm1_1_0_28
 def realAnswer : RBox := ⟨(-7983855440568),(-7983655440229)⟩
end hm1_1_0_28
namespace hm1_0_0_29
 def realAnswer : RBox := ⟨(-721317018351),(-721117018084)⟩
end hm1_0_0_29
namespace hm1_1_0_29
 def realAnswer : RBox := ⟨51145506138,51345506402⟩
end hm1_1_0_29
namespace hm1_1_0_30
 def realAnswer : RBox := ⟨92696498070,92896498429⟩
end hm1_1_0_30
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm1_1_1_1
 def realAnswer : RBox := ⟨(-537276096718696872011556700675),(-537276096718592567153537579701)⟩
end hm1_1_1_1
namespace hm1_0_1_2
 def realAnswer : RBox := ⟨1693598192195609481090992443152,1693598192195915649744484734274⟩
end hm1_0_1_2
namespace hm1_1_1_2
 def realAnswer : RBox := ⟨(-90625941314257419550125777709),(-90625941314006068843914756252)⟩
end hm1_1_1_2
namespace hm1_0_1_3
 def realAnswer : RBox := ⟨(-1827917254587326196718548783166),(-1827917254586861892328084393595)⟩
end hm1_0_1_3
namespace hm1_1_1_3
 def realAnswer : RBox := ⟨1290431608008775614037273174962,1290431608009156813447492106963⟩
end hm1_1_1_3
namespace hm1_0_1_4
 def realAnswer : RBox := ⟨654072430715487968464727243207,654072430715985087789648732260⟩
end hm1_0_1_4
namespace hm1_1_1_4
 def realAnswer : RBox := ⟨(-818148655064871311849864466175),(-818148655064463137884116122728)⟩
end hm1_1_1_4
namespace hm1_0_1_5
 def realAnswer : RBox := ⟨615707699688660305455905478176,615707699689084821696765069301⟩
end hm1_0_1_5
namespace hm1_1_1_5
 def realAnswer : RBox := ⟨(-374488189203004736652197884744),(-374488189202656135621875227946)⟩
end hm1_1_1_5
namespace hm1_0_1_6
 def realAnswer : RBox := ⟨(-954985873374019900007561855377),(-954985873373701685928855635981)⟩
end hm1_0_1_6
namespace hm1_1_1_6
 def realAnswer : RBox := ⟨726875200046644446308717547392,726875200046905740045181732071⟩
end hm1_1_1_6
namespace hm1_0_1_7
 def realAnswer : RBox := ⟨534962416767509733377126107209,534962416767734572272770671540⟩
end hm1_0_1_7
namespace hm1_1_1_7
 def realAnswer : RBox := ⟨(-396614713705414111219740611113),(-396614713705229450286994233685)⟩
end hm1_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm1_0_1_8
 def realAnswer : RBox := ⟨9536241476494365306427558671,9536241476637883270511919224⟩
end hm1_0_1_8
namespace hm1_1_1_8
 def realAnswer : RBox := ⟨(-39756100421500686816921492250),(-39756100421382761059939274089)⟩
end hm1_1_1_8
namespace hm1_0_1_9
 def realAnswer : RBox := ⟨(-217310356125980448721868751322),(-217310356125899588952714774157)⟩
end hm1_0_1_9
namespace hm1_1_1_9
 def realAnswer : RBox := ⟨209989946721956553748258073490,209989946722023035209884255282⟩
end hm1_1_1_9
namespace hm1_0_1_10
 def realAnswer : RBox := ⟨113442319809766456824674060484,113442319809810134010239530169⟩
end hm1_0_1_10
namespace hm1_1_1_10
 def realAnswer : RBox := ⟨(-110361601934805464610983234588),(-110361601934769518325467716502)⟩
end hm1_1_1_10
namespace hm1_0_1_11
 def realAnswer : RBox := ⟨20142947865294712466006847916,20142947865317163857954486225⟩
end hm1_0_1_11
namespace hm1_1_1_11
 def realAnswer : RBox := ⟨(-17925007359987001654928190090),(-17925007359968508742373653853)⟩
end hm1_1_1_11
namespace hm1_0_1_12
 def realAnswer : RBox := ⟨(-53025370889192954069064058639),(-53025370889181181897933210735)⟩
end hm1_0_1_12
namespace hm1_1_1_12
 def realAnswer : RBox := ⟨50997627076823128590767159752,50997627076832833485123340366⟩
end hm1_1_1_12
namespace hm1_0_1_13
 def realAnswer : RBox := ⟨30712121082681719841786824909,30712121082687821590613362463⟩
end hm1_0_1_13
namespace hm1_1_1_13
 def realAnswer : RBox := ⟨(-30140000485058313128823846127),(-30140000485053279232138475846)⟩
end hm1_1_1_13
namespace hm1_0_1_14
 def realAnswer : RBox := ⟨(-10939836103931689934296851676),(-10939836103928595704000767730)⟩
end hm1_0_1_14
namespace hm1_1_1_14
 def realAnswer : RBox := ⟨11053904591415818172170704441,11053904591418372065633260348⟩
end hm1_1_1_14
namespace hm1_0_1_15
 def realAnswer : RBox := ⟨5042925002204020738956576486,5042925002205536330547524649⟩
end hm1_0_1_15
namespace hm1_1_1_15
 def realAnswer : RBox := ⟨(-5163412113654279646419998090),(-5163412113653028284299326355)⟩
end hm1_1_1_15
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm1_0_1_16
 def realAnswer : RBox := ⟨(-4434344312561729249155314858),(-4434344312561012777361356355)⟩
end hm1_0_1_16
namespace hm1_1_1_16
 def realAnswer : RBox := ⟨4403335006708829551827545272,4403335006709421158795812030⟩
end hm1_1_1_16
namespace hm1_0_1_17
 def realAnswer : RBox := ⟨3581717630923415434399835945,3581717630923738398082880991⟩
end hm1_0_1_17
namespace hm1_1_1_17
 def realAnswer : RBox := ⟨(-3488730042443162258687933091),(-3488730042442895587977993906)⟩
end hm1_1_1_17
namespace hm1_0_1_18
 def realAnswer : RBox := ⟨(-2135393603148081474548568120),(-2135393603147941924686630700)⟩
end hm1_0_1_18
namespace hm1_1_1_18
 def realAnswer : RBox := ⟨2062006729196205958996023042,2062006729196321160714862921⟩
end hm1_1_1_18
namespace hm1_0_1_19
 def realAnswer : RBox := ⟨961417623030564462881568885,961417623030621860231327771⟩
end hm1_0_1_19
namespace hm1_1_1_19
 def realAnswer : RBox := ⟨(-924500234476551800729329758),(-924500234476504433170275094)⟩
end hm1_1_1_19
namespace hm1_0_1_20
 def realAnswer : RBox := ⟨(-338082815733786076192929830),(-338082815733763523123105915)⟩
end hm1_0_1_20
namespace hm1_1_1_20
 def realAnswer : RBox := ⟨324455019678639613681675588,324455019678658215983808361⟩
end hm1_1_1_20
namespace hm1_0_1_21
 def realAnswer : RBox := ⟨95488670921474232437123607,95488670921482703975385166⟩
end hm1_0_1_21
namespace hm1_1_1_21
 def realAnswer : RBox := ⟨(-91545103264281148574598921),(-91545103264274166017859338)⟩
end hm1_1_1_21
namespace hm1_0_1_22
 def realAnswer : RBox := ⟨(-23066022508310039617466442),(-23066022508306994044675264)⟩
end hm1_0_1_22
namespace hm1_1_1_22
 def realAnswer : RBox := ⟨22045528425897430508283975,22045528425899938245515196⟩
end hm1_1_1_22
namespace hm1_0_1_23
 def realAnswer : RBox := ⟨5944787935393112790788963,5944787935394162412964175⟩
end hm1_0_1_23
namespace hm1_1_1_23
 def realAnswer : RBox := ⟨(-5609036332973759165746942),(-5609036332972896081498887)⟩
end hm1_1_1_23
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighMoments1_7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm1_0_1_24
 def realAnswer : RBox := ⟨(-2277348847943361150094668),(-2277348847943013302302551)⟩
end hm1_0_1_24
namespace hm1_1_1_24
 def realAnswer : RBox := ⟨2109415693315465776034020,2109415693315751279659990⟩
end hm1_1_1_24
namespace hm1_0_1_25
 def realAnswer : RBox := ⟨1149887104059844110663726,1149887104059955124488302⟩
end hm1_0_1_25
namespace hm1_1_1_25
 def realAnswer : RBox := ⟨(-1058619217946539715283979),(-1058619217946448812587912)⟩
end hm1_1_1_25
namespace hm1_0_1_26
 def realAnswer : RBox := ⟨(-565156860994932894920550),(-565156860994898608041220)⟩
end hm1_0_1_26
namespace hm1_1_1_26
 def realAnswer : RBox := ⟨521543549539227575571412,521543549539255576053535⟩
end hm1_1_1_26
namespace hm1_0_1_27
 def realAnswer : RBox := ⟨245650501089237831379538,245650501089248153680064⟩
end hm1_0_1_27
namespace hm1_1_1_27
 def realAnswer : RBox := ⟨(-227865089494631365052488),(-227865089494622950083792)⟩
end hm1_1_1_27
namespace hm1_0_1_28
 def realAnswer : RBox := ⟨(-94467326654999760424040),(-94467326654996645404072)⟩
end hm1_0_1_28
namespace hm1_1_1_28
 def realAnswer : RBox := ⟨88178579395611613817378,88178579395614163846089⟩
end hm1_1_1_28
namespace hm1_0_1_29
 def realAnswer : RBox := ⟨32713979064960038085301,32713979064961052745917⟩
end hm1_0_1_29
namespace hm1_1_1_29
 def realAnswer : RBox := ⟨(-30745284987295833487790),(-30745284987294982627322)⟩
end hm1_1_1_29
namespace hm1_0_1_30
 def realAnswer : RBox := ⟨(-10364206612620393619505),(-10364206612619972080104)⟩
end hm1_0_1_30
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein1
open IntegerIntervals CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 1763035019179741583475524811551, hi := 1763035019180016298943129538706}
lemma t0_checked : ((hm1_0_0_1.realAnswer).add hm1_1_1_1.realAnswer).scale (-1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -1589948320085958454589340602391, hi := -1589948320085516608921108133404}
lemma t1_checked : ((hm1_0_0_2.realAnswer).add hm1_1_1_2.realAnswer).scale (-1) 1=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -516651337560567654075495423230, hi := -516651337560039257667266488754}
lemma t2_checked : ((hm1_0_0_3.realAnswer).add hm1_1_1_3.realAnswer).scale (-1) 1=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 801784442360821482964379328962, hi := 801784442361316154786389263566}
lemma t3_checked : ((hm1_0_0_4.realAnswer).add hm1_1_1_4.realAnswer).scale (-1) 1=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 154911090581499165263164190010, hi := 154911090581888673933835026952}
lemma t4_checked : ((hm1_0_0_5.realAnswer).add hm1_1_1_5.realAnswer).scale (-1) 1=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := -621940417853192215857733651016, hi := -621940417852914747141806167349}
lemma t5_checked : ((hm1_0_0_6.realAnswer).add hm1_1_1_6.realAnswer).scale (-1) 1=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := 413994558940119903448888763146, hi := 413994558940310059129363612600}
lemma t6_checked : ((hm1_0_0_7.realAnswer).add hm1_1_1_7.realAnswer).scale (-1) 1=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 19074696079656669206920597865, hi := 19074696079776231501906104084}
lemma t7_checked : ((hm1_0_0_8.realAnswer).add hm1_1_1_8.realAnswer).scale (-1) 1=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := -209797788981833789732473398312, hi := -209797788981766874195519719747}
lemma t8_checked : ((hm1_0_0_9.realAnswer).add hm1_1_1_9.realAnswer).scale (-1) 1=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 112480352673426549289171735150, hi := 112480352673462599384311698547}
lemma t9_checked : ((hm1_0_0_10.realAnswer).add hm1_1_1_10.realAnswer).scale (-1) 1=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := 17790286685661893946485983686, hi := 17790286685680409469069298980}
lemma t10_checked : ((hm1_0_0_11.realAnswer).add hm1_1_1_11.realAnswer).scale (-1) 1=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -51140060085380105627978919119, hi := -51140060085370396211299625973}
lemma t11_checked : ((hm1_0_0_12.realAnswer).add hm1_1_1_12.realAnswer).scale (-1) 1=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := 30152114990247550907852423187, hi := 30152114990252585641102423293}
lemma t12_checked : ((hm1_0_0_13.realAnswer).add hm1_1_1_13.realAnswer).scale (-1) 1=t12 := by decide +kernel
noncomputable def t13 : RBox := {lo := -11046979774555862378193581022, hi := -11046979774553308340642151448}
lemma t13_checked : ((hm1_0_0_14.realAnswer).add hm1_1_1_14.realAnswer).scale (-1) 1=t13 := by decide +kernel
noncomputable def t14 : RBox := {lo := 5162769573346517541969431140, hi := 5162769573347768927435120444}
lemma t14_checked : ((hm1_0_0_15.realAnswer).add hm1_1_1_15.realAnswer).scale (-1) 1=t14 := by decide +kernel
noncomputable def t15 : RBox := {lo := -4403592368600343358290555103, hi := -4403592368599751747625958426}
lemma t15_checked : ((hm1_0_0_16.realAnswer).add hm1_1_1_16.realAnswer).scale (-1) 1=t15 := by decide +kernel
noncomputable def t16 : RBox := {lo := 3488754170411527892798534312, hi := 3488754170411794564206431519}
lemma t16_checked : ((hm1_0_0_17.realAnswer).add hm1_1_1_17.realAnswer).scale (-1) 1=t16 := by decide +kernel
noncomputable def t17 : RBox := {lo := -2061999144534369104910251530, hi := -2061999144534253902924316023}
lemma t17_checked : ((hm1_0_0_18.realAnswer).add hm1_1_1_18.realAnswer).scale (-1) 1=t17 := by decide +kernel
noncomputable def t18 : RBox := {lo := 924499542799954635228891164, hi := 924499542800002002996525523}
lemma t18_checked : ((hm1_0_0_19.realAnswer).add hm1_1_1_19.realAnswer).scale (-1) 1=t18 := by decide +kernel
noncomputable def t19 : RBox := {lo := -324455201683265947638790714, hi := -324455201683247345135613693}
lemma t19_checked : ((hm1_0_0_20.realAnswer).add hm1_1_1_20.realAnswer).scale (-1) 1=t19 := by decide +kernel
noncomputable def t20 : RBox := {lo := 91545119069663452170116028, hi := 91545119069670434926977076}
lemma t20_checked : ((hm1_0_0_21.realAnswer).add hm1_1_1_21.realAnswer).scale (-1) 1=t20 := by decide +kernel
noncomputable def t21 : RBox := {lo := -22045524796855351856240072, hi := -22045524796852843918995093}
lemma t21_checked : ((hm1_0_0_22.realAnswer).add hm1_1_1_22.realAnswer).scale (-1) 1=t21 := by decide +kernel
noncomputable def t22 : RBox := {lo := 5609036036619128155670574, hi := 5609036036619991439920331}
lemma t22_checked : ((hm1_0_0_23.realAnswer).add hm1_1_1_23.realAnswer).scale (-1) 1=t22 := by decide +kernel
noncomputable def t23 : RBox := {lo := -2109415754424522019037564, hi := -2109415754424236315411121}
lemma t23_checked : ((hm1_0_0_24.realAnswer).add hm1_1_1_24.realAnswer).scale (-1) 1=t23 := by decide +kernel
noncomputable def t24 : RBox := {lo := 1058619222603894933722271, hi := 1058619222603986036418624}
lemma t24_checked : ((hm1_0_0_25.realAnswer).add hm1_1_1_25.realAnswer).scale (-1) 1=t24 := by decide +kernel
noncomputable def t25 : RBox := {lo := -521543548658586339883345, hi := -521543548658558139400882}
lemma t25_checked : ((hm1_0_0_26.realAnswer).add hm1_1_1_26.realAnswer).scale (-1) 1=t25 := by decide +kernel
noncomputable def t26 : RBox := {lo := 227865089432252726638814, hi := 227865089432261341607778}
lemma t26_checked : ((hm1_0_0_27.realAnswer).add hm1_1_1_27.realAnswer).scale (-1) 1=t26 := by decide +kernel
noncomputable def t27 : RBox := {lo := -88178579406599415888153, hi := -88178579406596665859095}
lemma t27_checked : ((hm1_0_0_28.realAnswer).add hm1_1_1_28.realAnswer).scale (-1) 1=t27 := by decide +kernel
noncomputable def t28 : RBox := {lo := 30745284988016099645406, hi := 30745284988017150506141}
lemma t28_checked : ((hm1_0_0_29.realAnswer).add hm1_1_1_29.realAnswer).scale (-1) 1=t28 := by decide +kernel
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N0_right
namespace N1_right
noncomputable def t0 : RBox := {lo := 1748076608800213996526705081841, hi := 1748076608800676585401726848184}
lemma t0_checked : ((hm1_1_0_2.realAnswer).add hm1_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -2566936845787339703052147652281, hi := -2566936845786754539193231840479}
lemma t1_checked : ((hm1_1_0_3.realAnswer).add hm1_0_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := 788015125822514376363896825203, hi := 788015125823082517645739465582}
lemma t2_checked : ((hm1_1_0_4.realAnswer).add hm1_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 801473329179703242055848542511, hi := 801473329180161348230600379273}
lemma t3_checked : ((hm1_1_0_5.realAnswer).add hm1_0_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := -989619402545820147705823690132, hi := -989619402545488651469392575143}
lemma t4_checked : ((hm1_1_0_6.realAnswer).add hm1_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := 511302174796620577486891691928, hi := 511302174796849928637520657558}
lemma t5_checked : ((hm1_1_0_7.realAnswer).add hm1_0_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := 12583790543309548381913794509, hi := 12583790543454410324477615593}
lemma t6_checked : ((hm1_1_0_8.realAnswer).add hm1_0_1_8.realAnswer).scale (1) 1=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := -215395302916849649773894154097, hi := -215395302916768433511783198780}
lemma t7_checked : ((hm1_1_0_9.realAnswer).add hm1_0_1_9.realAnswer).scale (1) 1=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 113396156120500350094090807216, hi := 113396156120544112539067936038}
lemma t8_checked : ((hm1_1_0_10.realAnswer).add hm1_0_1_10.realAnswer).scale (1) 1=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 20032974768048632949798581891, hi := 20032974768071102912263638250}
lemma t9_checked : ((hm1_1_0_11.realAnswer).add hm1_0_1_11.realAnswer).scale (1) 1=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := -53038356483437408213364385242, hi := -53038356483425632327696911781}
lemma t10_checked : ((hm1_1_0_12.realAnswer).add hm1_0_1_12.realAnswer).scale (1) 1=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := 30716895649799357063629917613, hi := 30716895649805459499645368830}
lemma t11_checked : ((hm1_1_0_13.realAnswer).add hm1_0_1_13.realAnswer).scale (1) 1=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -10938471405241648612681814823, hi := -10938471405238554263991531056}
lemma t12_checked : ((hm1_1_0_14.realAnswer).add hm1_0_1_14.realAnswer).scale (1) 1=t12 := by decide +kernel
noncomputable def t13 : RBox := {lo := 5042761956922174978190354586, hi := 5042761956923690588993795146}
lemma t13_checked : ((hm1_1_0_15.realAnswer).add hm1_0_1_15.realAnswer).scale (1) 1=t13 := by decide +kernel
noncomputable def t14 : RBox := {lo := -4434420475855080999677896484, hi := -4434420475854364524811789121}
lemma t14_checked : ((hm1_1_0_16.realAnswer).add hm1_0_1_16.realAnswer).scale (1) 1=t14 := by decide +kernel
noncomputable def t15 : RBox := {lo := 3581722126421433399160583268, hi := 3581722126421756363452697623}
lemma t15_checked : ((hm1_1_0_17.realAnswer).add hm1_0_1_17.realAnswer).scale (1) 1=t15 := by decide +kernel
noncomputable def t16 : RBox := {lo := -2135390667226566009319078920, hi := -2135390667226426459202021410}
lemma t16_checked : ((hm1_1_0_18.realAnswer).add hm1_0_1_18.realAnswer).scale (1) 1=t16 := by decide +kernel
noncomputable def t17 : RBox := {lo := 961417521058673443420458188, hi := 961417521058730840977265561}
lemma t17_checked : ((hm1_1_0_19.realAnswer).add hm1_0_1_19.realAnswer).scale (1) 1=t17 := by decide +kernel
noncomputable def t18 : RBox := {lo := -338082901303105091570767255, hi := -338082901303082538300085402}
lemma t18_checked : ((hm1_1_0_20.realAnswer).add hm1_0_1_20.realAnswer).scale (1) 1=t18 := by decide +kernel
noncomputable def t19 : RBox := {lo := 95488672852492451082865915, hi := 95488672852500922821227300}
lemma t19_checked : ((hm1_1_0_21.realAnswer).add hm1_0_1_21.realAnswer).scale (1) 1=t19 := by decide +kernel
noncomputable def t20 : RBox := {lo := -23066020529813207384913554, hi := -23066020529810161612111032}
lemma t20_checked : ((hm1_1_0_22.realAnswer).add hm1_0_1_22.realAnswer).scale (1) 1=t20 := by decide +kernel
noncomputable def t21 : RBox := {lo := 5944787904485716633364017, hi := 5944787904486766455540668}
lemma t21_checked : ((hm1_1_0_23.realAnswer).add hm1_0_1_23.realAnswer).scale (1) 1=t21 := by decide +kernel
noncomputable def t22 : RBox := {lo := -2277348885376867519397703, hi := -2277348885376519471605148}
lemma t22_checked : ((hm1_1_0_24.realAnswer).add hm1_0_1_24.realAnswer).scale (1) 1=t22 := by decide +kernel
noncomputable def t23 : RBox := {lo := 1149887104482546949859620, hi := 1149887104482658163684470}
lemma t23_checked : ((hm1_1_0_25.realAnswer).add hm1_0_1_25.realAnswer).scale (1) 1=t23 := by decide +kernel
noncomputable def t24 : RBox := {lo := -565156860402344662984212, hi := -565156860402310176104551}
lemma t24_checked : ((hm1_1_0_26.realAnswer).add hm1_0_1_26.realAnswer).scale (1) 1=t24 := by decide +kernel
noncomputable def t25 : RBox := {lo := 245650501084249431557409, hi := 245650501084259953858200}
lemma t25_checked : ((hm1_1_0_27.realAnswer).add hm1_0_1_27.realAnswer).scale (1) 1=t25 := by decide +kernel
noncomputable def t26 : RBox := {lo := -94467326662983615864608, hi := -94467326662980300844301}
lemma t26_checked : ((hm1_1_0_28.realAnswer).add hm1_0_1_28.realAnswer).scale (1) 1=t26 := by decide +kernel
noncomputable def t27 : RBox := {lo := 32713979065011183591439, hi := 32713979065012398252319}
lemma t27_checked : ((hm1_1_0_29.realAnswer).add hm1_0_1_29.realAnswer).scale (1) 1=t27 := by decide +kernel
noncomputable def t28 : RBox := {lo := -10364206612527697121435, hi := -10364206612527075581675}
lemma t28_checked : ((hm1_1_0_30.realAnswer).add hm1_0_1_30.realAnswer).scale (1) 1=t28 := by decide +kernel
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_right
namespace N1_left
noncomputable def t0 : RBox := {lo := 1748076608800213996526705081841, hi := 1748076608800676585401726848184}
lemma t0_checked : ((hm1_1_0_2.realAnswer).add hm1_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := 1283468422893377269596615920239, hi := 1283468422893669851526073826141}
lemma t1_checked : ((hm1_1_0_3.realAnswer).add hm1_0_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := 197003781455628594090974206300, hi := 197003781455770629411434866396}
lemma t2_checked : ((hm1_1_0_4.realAnswer).add hm1_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := -100184166147520168528825047410, hi := -100184166147462905256981067813}
lemma t3_checked : ((hm1_1_0_5.realAnswer).add hm1_0_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := -61851212659113759231613980634, hi := -61851212659093040716837035946}
lemma t4_checked : ((hm1_1_0_6.realAnswer).add hm1_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := -15978192962401560269922520549, hi := -15978192962394393046465365372}
lemma t5_checked : ((hm1_1_0_7.realAnswer).add hm1_0_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := 196621727239211693467403039, hi := 196621727241475161319962744}
lemma t6_checked : ((hm1_1_0_8.realAnswer).add hm1_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 1682775804037253386810806240, hi := 1682775804037887888858548079}
lemma t7_checked : ((hm1_1_0_9.realAnswer).add hm1_0_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 442953734845704492555042215, hi := 442953734845875439605734126}
lemma t8_checked : ((hm1_1_0_10.realAnswer).add hm1_0_1_10.realAnswer).scale (1) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := -39126903843888872875514919, hi := -39126903843844986230075355}
lemma t9_checked : ((hm1_1_0_11.realAnswer).add hm1_0_1_11.realAnswer).scale (-1) 512=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := -51795270003356843958363658, hi := -51795270003345344070016515}
lemma t10_checked : ((hm1_1_0_12.realAnswer).add hm1_0_1_12.realAnswer).scale (1) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -14998484204006572021311216, hi := -14998484204003592316225545}
lemma t11_checked : ((hm1_1_0_13.realAnswer).add hm1_0_1_13.realAnswer).scale (-1) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -2670525245420324368330522, hi := -2670525245419568912107307}
lemma t12_checked : ((hm1_1_0_14.realAnswer).add hm1_0_1_14.realAnswer).scale (1) 4096=t12 := by decide +kernel
noncomputable def t13 : RBox := {lo := -615571527944786448851782, hi := -615571527944601437767377}
lemma t13_checked : ((hm1_1_0_15.realAnswer).add hm1_0_1_15.realAnswer).scale (-1) 8192=t13 := by decide +kernel
noncomputable def t14 : RBox := {lo := -270655546622014221171747, hi := -270655546621970491016344}
lemma t14_checked : ((hm1_1_0_16.realAnswer).add hm1_0_1_16.realAnswer).scale (1) 16384=t14 := by decide +kernel
noncomputable def t15 : RBox := {lo := -109305484815117076521384, hi := -109305484815107220433367}
lemma t15_checked : ((hm1_1_0_17.realAnswer).add hm1_0_1_17.realAnswer).scale (-1) 32768=t15 := by decide +kernel
noncomputable def t16 : RBox := {lo := -32583475757241302632433, hi := -32583475757239173266632}
lemma t16_checked : ((hm1_1_0_18.realAnswer).add hm1_0_1_18.realAnswer).scale (1) 65536=t16 := by decide +kernel
noncomputable def t17 : RBox := {lo := -7335033577413412788218, hi := -7335033577412974879611}
lemma t17_checked : ((hm1_1_0_19.realAnswer).add hm1_0_1_19.realAnswer).scale (-1) 131072=t17 := by decide +kernel
noncomputable def t18 : RBox := {lo := -1289683919155521742138, hi := -1289683919155435708237}
lemma t18_checked : ((hm1_1_0_20.realAnswer).add hm1_0_1_20.realAnswer).scale (1) 262144=t18 := by decide +kernel
noncomputable def t19 : RBox := {lo := -182130189614297719615, hi := -182130189614281561055}
lemma t19_checked : ((hm1_1_0_21.realAnswer).add hm1_0_1_21.realAnswer).scale (-1) 524288=t19 := by decide +kernel
noncomputable def t20 : RBox := {lo := -21997471360982139001, hi := -21997471360979234325}
lemma t20_checked : ((hm1_1_0_22.realAnswer).add hm1_0_1_22.realAnswer).scale (1) 1048576=t20 := by decide +kernel
noncomputable def t21 : RBox := {lo := -2834695770495780209, hi := -2834695770495279614}
lemma t21_checked : ((hm1_1_0_23.realAnswer).add hm1_0_1_23.realAnswer).scale (-1) 2097152=t21 := by decide +kernel
noncomputable def t22 : RBox := {lo := -542962285370079880, hi := -542962285369996898}
lemma t22_checked : ((hm1_1_0_24.realAnswer).add hm1_0_1_24.realAnswer).scale (1) 4194304=t22 := by decide +kernel
noncomputable def t23 : RBox := {lo := -137077224788982650, hi := -137077224788969391}
lemma t23_checked : ((hm1_1_0_25.realAnswer).add hm1_0_1_25.realAnswer).scale (-1) 8388608=t23 := by decide +kernel
noncomputable def t24 : RBox := {lo := -33685973906656782, hi := -33685973906654726}
lemma t24_checked : ((hm1_1_0_26.realAnswer).add hm1_0_1_26.realAnswer).scale (1) 16777216=t24 := by decide +kernel
noncomputable def t25 : RBox := {lo := -7320955428012013, hi := -7320955428011698}
lemma t25_checked : ((hm1_1_0_27.realAnswer).add hm1_0_1_27.realAnswer).scale (-1) 33554432=t25 := by decide +kernel
noncomputable def t26 : RBox := {lo := -1407672862156982, hi := -1407672862156932}
lemma t26_checked : ((hm1_1_0_28.realAnswer).add hm1_0_1_28.realAnswer).scale (1) 67108864=t26 := by decide +kernel
noncomputable def t27 : RBox := {lo := -243738137669954, hi := -243738137669944}
lemma t27_checked : ((hm1_1_0_29.realAnswer).add hm1_0_1_29.realAnswer).scale (-1) 134217728=t27 := by decide +kernel
noncomputable def t28 : RBox := {lo := -38609678344905, hi := -38609678344901}
lemma t28_checked : ((hm1_1_0_30.realAnswer).add hm1_0_1_30.realAnswer).scale (1) 268435456=t28 := by decide +kernel
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_left
end SharpPlanar.Bernstein1

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock12_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm12_0_0_2
 def realAnswer : RBox := ⟨(-66569330712034534472233866952),(-66569330711862005784074953665)⟩
end hm12_0_0_2
namespace hm12_1_0_2
 def realAnswer : RBox := ⟨66591716817251220454588192274,66591716817392883309317954788⟩
end hm12_1_0_2
namespace hm12_0_0_3
 def realAnswer : RBox := ⟨168128051555241720586735692318,168128051555375037183542480501⟩
end hm12_0_0_3
namespace hm12_1_0_3
 def realAnswer : RBox := ⟨(-163352103562487131409390076270),(-163352103562377672189858077967)⟩
end hm12_1_0_3
namespace hm12_0_0_4
 def realAnswer : RBox := ⟨(-58932716623473954279030819195),(-58932716623395610238073434109)⟩
end hm12_0_0_4
namespace hm12_1_0_4
 def realAnswer : RBox := ⟨53105749317548182468820899171,53105749317612507625879614357⟩
end hm12_1_0_4
namespace hm12_0_0_5
 def realAnswer : RBox := ⟨(-68916183675019110466349813521),(-68916183674982056931404145215)⟩
end hm12_0_0_5
namespace hm12_1_0_5
 def realAnswer : RBox := ⟨67108379718465058145482814596,67108379718495482544915164637⟩
end hm12_1_0_5
namespace hm12_0_0_6
 def realAnswer : RBox := ⟨35629093946423521613305439003,35629093946438173783753339605⟩
end hm12_0_0_6
namespace hm12_1_0_6
 def realAnswer : RBox := ⟨(-32662087059247941663668626242),(-32662087059235910302702916982)⟩
end hm12_1_0_6
namespace hm12_0_0_7
 def realAnswer : RBox := ⟨11968682354929977198763713606,11968682354934955113283415994⟩
end hm12_0_0_7
namespace hm12_1_0_7
 def realAnswer : RBox := ⟨(-11781311596101691924477890759),(-11781311596097604206801281942)⟩
end hm12_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock12_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm12_0_0_8
 def realAnswer : RBox := ⟨(-7715693632947556947874218382),(-7715693632946074171560323428)⟩
end hm12_0_0_8
namespace hm12_1_0_8
 def realAnswer : RBox := ⟨7068572860885892732505054505,7068572860887110401264154859⟩
end hm12_1_0_8
namespace hm12_0_0_9
 def realAnswer : RBox := ⟨(-1159058388541415845892779678),(-1159058388541022502077212959)⟩
end hm12_0_0_9
namespace hm12_1_0_9
 def realAnswer : RBox := ⟨1167999745297123137734327381,1167999745297446169231303772⟩
end hm12_1_0_9
namespace hm12_0_0_10
 def realAnswer : RBox := ⟨933774259150987601719035278,933774259151081684726665763⟩
end hm12_0_0_10
namespace hm12_1_0_10
 def realAnswer : RBox := ⟨(-852394364736292960153574299),(-852394364736215691767969980)⟩
end hm12_1_0_10
namespace hm12_0_0_11
 def realAnswer : RBox := ⟨70364584020710081489047614,70364584020730576518342243⟩
end hm12_0_0_11
namespace hm12_1_0_11
 def realAnswer : RBox := ⟨(-74320441254135941466981361),(-74320441254119108663150024)⟩
end hm12_1_0_11
namespace hm12_0_0_12
 def realAnswer : RBox := ⟨(-73662392526648103525748449),(-73662392526644003437379842)⟩
end hm12_0_0_12
namespace hm12_1_0_12
 def realAnswer : RBox := ⟨66955118808386384656918514,66955118808389752255330101⟩
end hm12_1_0_12
namespace hm12_0_0_13
 def realAnswer : RBox := ⟨(-2819524641174286350874435),(-2819524641173527722501112)⟩
end hm12_0_0_13
namespace hm12_1_0_13
 def realAnswer : RBox := ⟨3272816906500759700915921,3272816906501382847494791⟩
end hm12_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock12_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm12_0_1_2
 def realAnswer : RBox := ⟨(-9483842800179091637158717561),(-9483842800179083110092972052)⟩
end hm12_0_1_2
namespace hm12_1_1_2
 def realAnswer : RBox := ⟨5117459929107664328614247628,5117459929107671226187496289⟩
end hm12_1_1_2
namespace hm12_0_1_3
 def realAnswer : RBox := ⟨35146806285335766645788341104,35146806285335778786917898951⟩
end hm12_0_1_3
namespace hm12_1_1_3
 def realAnswer : RBox := ⟨(-31342697090587374521890450812),(-31342697090587364689193706707)⟩
end hm12_1_1_3
namespace hm12_0_1_4
 def realAnswer : RBox := ⟨6421840530720008321979829232,6421840530720021300423468751⟩
end hm12_0_1_4
namespace hm12_1_1_4
 def realAnswer : RBox := ⟨(-2472603525860432340629876970),(-2472603525860421817355702868)⟩
end hm12_1_1_4
namespace hm12_0_1_5
 def realAnswer : RBox := ⟨(-23493381442871399036180564112),(-23493381442871387926665026350)⟩
end hm12_0_1_5
namespace hm12_1_1_5
 def realAnswer : RBox := ⟨20762427502464828279560371191,20762427502464837298966416710⟩
end hm12_1_1_5
namespace hm12_0_1_6
 def realAnswer : RBox := ⟨(-1059765791827550969722944129),(-1059765791827543043965304173)⟩
end hm12_0_1_6
namespace hm12_1_1_6
 def realAnswer : RBox := ⟨(-309575169266626230906643734),(-309575169266619788583779914)⟩
end hm12_1_1_6
namespace hm12_0_1_7
 def realAnswer : RBox := ⟨7347378785329836105756297302,7347378785329840954390016449⟩
end hm12_0_1_7
namespace hm12_1_1_7
 def realAnswer : RBox := ⟨(-6458220312351141426565021153),(-6458220312351137480702754182)⟩
end hm12_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock12_11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm12_0_1_8
 def realAnswer : RBox := ⟨(-156336174665575794199940833),(-156336174665573196896774661)⟩
end hm12_0_1_8
namespace hm12_1_1_8
 def realAnswer : RBox := ⟨397525681996648438296270922,397525681996650554347513240⟩
end hm12_1_1_8
namespace hm12_0_1_9
 def realAnswer : RBox := ⟨(-1317566584583492400750131945),(-1317566584583491162755751850)⟩
end hm12_0_1_9
namespace hm12_1_1_9
 def realAnswer : RBox := ⟨1154898650158645233320371274,1154898650158646243021362591⟩
end hm12_1_1_9
namespace hm12_0_1_10
 def realAnswer : RBox := ⟨79493469852177235389706802,79493469852177767060821094⟩
end hm12_0_1_10
namespace hm12_1_1_10
 def realAnswer : RBox := ⟨(-104058104309994973469865771),(-104058104309994539407620227)⟩
end hm12_1_1_10
namespace hm12_0_1_11
 def realAnswer : RBox := ⟨152070309765535454124265409,152070309765535661976062137⟩
end hm12_0_1_11
namespace hm12_1_1_11
 def realAnswer : RBox := ⟨(-133165475909019213461314350),(-133165475909019043597556944)⟩
end hm12_1_1_11
namespace hm12_0_1_12
 def realAnswer : RBox := ⟨(-13162612621184966543211990),(-13162612621184891883717855)⟩
end hm12_0_1_12
namespace hm12_1_1_12
 def realAnswer : RBox := ⟨14678818367730045040658725,14678818367730106124664022⟩
end hm12_1_1_12
namespace hm12_0_1_13
 def realAnswer : RBox := ⟨(-12175794789060434879055113),(-12175794789060410004823432)⟩
end hm12_0_1_13
namespace hm12_1_1_13
 def realAnswer : RBox := ⟨10663632557402472531964671,10663632557402492921286514⟩
end hm12_1_1_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein12
open IntegerIntervals CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 61451870782754334557887457376, hi := 61451870782926870143619619324}
lemma t0_checked : ((hm12_0_0_2.realAnswer).add hm12_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -68392677232393836247174386897, hi := -68392677232327173032422620753}
lemma t1_checked : ((hm12_0_0_3.realAnswer).add hm12_1_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := 15351330037314008013857284244, hi := 15351330037333596654915174042}
lemma t2_checked : ((hm12_0_0_4.realAnswer).add hm12_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 6019219521564652454054716063, hi := 6019219521569285273348680292}
lemma t3_checked : ((hm12_0_0_5.realAnswer).add hm12_1_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := -2207469923573222124698097481, hi := -2207469923572305961399924704}
lemma t4_checked : ((hm12_0_0_6.realAnswer).add hm12_1_1_6.realAnswer).scale (-1) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := -172201938830744301018145682, hi := -172201938830588617881209139}
lemma t5_checked : ((hm12_0_0_7.realAnswer).add hm12_1_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := 114346374233584744018950159, hi := 114346374233607945462155430}
lemma t6_checked : ((hm12_0_0_8.realAnswer).add hm12_1_1_8.realAnswer).scale (-1) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 32497956112314523873831, hi := 32497956115395410721941}
lemma t7_checked : ((hm12_0_0_9.realAnswer).add hm12_1_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := -3241078729847996661402522, hi := -3241078729847627454098318}
lemma t8_checked : ((hm12_0_0_10.realAnswer).add hm12_1_1_10.realAnswer).scale (-1) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 122657991969313412264091, hi := 122657991969353773383334}
lemma t9_checked : ((hm12_0_0_11.realAnswer).add hm12_1_1_11.realAnswer).scale (-1) 512=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := 57601146639564352844449, hi := 57601146639568416489346}
lemma t10_checked : ((hm12_0_0_12.realAnswer).add hm12_1_1_12.realAnswer).scale (-1) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -3830130818471174413470, hi := -3830130818470794033735}
lemma t11_checked : ((hm12_0_0_13.realAnswer).add hm12_1_1_13.realAnswer).scale (-1) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -171396147550665061348791, hi := 171396147550665061348791}
noncomputable def t13 : RBox := {lo := -20540279013060288964123, hi := 20540279013060288964123}
noncomputable def t14 : RBox := {lo := -2370812092565497112264, hi := 2370812092565497112264}
noncomputable def t15 : RBox := {lo := -263953881363605769697, hi := 263953881363605769697}
noncomputable def t16 : RBox := {lo := -28365989397522196385, hi := 28365989397522196385}
noncomputable def t17 : RBox := {lo := -2943072604808163227, hi := 2943072604808163227}
noncomputable def t18 : RBox := {lo := -294818953479539848, hi := 294818953479539848}
noncomputable def t19 : RBox := {lo := -28516436648066880, hi := 28516436648066880}
noncomputable def t20 : RBox := {lo := -2663938389153873, hi := 2663938389153873}
noncomputable def t21 : RBox := {lo := -240457452818595, hi := 240457452818595}
noncomputable def t22 : RBox := {lo := -20985905895579, hi := 20985905895579}
noncomputable def t23 : RBox := {lo := -1772419477128, hi := 1772419477128}
noncomputable def t24 : RBox := {lo := -145009275090, hi := 145009275090}
noncomputable def t25 : RBox := {lo := -11505508624, hi := 11505508624}
noncomputable def t26 : RBox := {lo := -886376938, hi := 886376938}
noncomputable def t27 : RBox := {lo := -66385150, hi := 66385150}
noncomputable def t28 : RBox := {lo := -4839517, hi := 4839517}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N0_right
namespace N1_right
noncomputable def t0 : RBox := {lo := 57107874017072128817429474713, hi := 57107874017213800199224982736}
lemma t0_checked : ((hm12_1_0_2.realAnswer).add hm12_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -64102648638575682381800867583, hi := -64102648638520946701470089508}
lemma t1_checked : ((hm12_1_0_3.realAnswer).add hm12_0_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := 14881897462067047697700182100, hi := 14881897462083132231575770777}
lemma t2_checked : ((hm12_1_0_4.realAnswer).add hm12_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 5451874784449207388662781310, hi := 5451874784453011827281267286}
lemma t3_checked : ((hm12_1_0_5.realAnswer).add hm12_0_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := -2107615803192218289586973149, hi := -2107615803191465834166763822}
lemma t4_checked : ((hm12_1_0_6.realAnswer).add hm12_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := -138560400336620494335049796, hi := -138560400336492601637852046}
lemma t5_checked : ((hm12_1_0_7.realAnswer).add hm12_0_1_7.realAnswer).scale (1) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := 108003698222192452161017401, hi := 108003698222211518818240316}
lemma t6_checked : ((hm12_1_0_8.realAnswer).add hm12_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := -1168490931924759867310974, hi := -1168490931922226511909750}
lemma t7_checked : ((hm12_1_0_9.realAnswer).add hm12_0_1_9.realAnswer).scale (1) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := -3019144120641077049858858, hi := -3019144120640773143387300}
lemma t8_checked : ((hm12_1_0_10.realAnswer).add hm12_0_1_10.realAnswer).scale (1) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 151855211936327173158757, hi := 151855211936360455689282}
lemma t9_checked : ((hm12_1_0_11.realAnswer).add hm12_0_1_11.realAnswer).scale (1) 512=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := 52531744323438884876666, hi := 52531744323442246456653}
lemma t10_checked : ((hm12_1_0_12.realAnswer).add hm12_0_1_12.realAnswer).scale (1) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -4347157169218591395576, hi := -4347157169218274979164}
lemma t11_checked : ((hm12_1_0_13.realAnswer).add hm12_0_1_13.realAnswer).scale (1) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -171396147550665061348791, hi := 171396147550665061348791}
noncomputable def t13 : RBox := {lo := -20540279013060288964123, hi := 20540279013060288964123}
noncomputable def t14 : RBox := {lo := -2370812092565497112264, hi := 2370812092565497112264}
noncomputable def t15 : RBox := {lo := -263953881363605769697, hi := 263953881363605769697}
noncomputable def t16 : RBox := {lo := -28365989397522196385, hi := 28365989397522196385}
noncomputable def t17 : RBox := {lo := -2943072604808163227, hi := 2943072604808163227}
noncomputable def t18 : RBox := {lo := -294818953479539848, hi := 294818953479539848}
noncomputable def t19 : RBox := {lo := -28516436648066880, hi := 28516436648066880}
noncomputable def t20 : RBox := {lo := -2663938389153873, hi := 2663938389153873}
noncomputable def t21 : RBox := {lo := -240457452818595, hi := 240457452818595}
noncomputable def t22 : RBox := {lo := -20985905895579, hi := 20985905895579}
noncomputable def t23 : RBox := {lo := -1772419477128, hi := 1772419477128}
noncomputable def t24 : RBox := {lo := -145009275090, hi := 145009275090}
noncomputable def t25 : RBox := {lo := -11505508624, hi := 11505508624}
noncomputable def t26 : RBox := {lo := -886376938, hi := 886376938}
noncomputable def t27 : RBox := {lo := -66385150, hi := 66385150}
noncomputable def t28 : RBox := {lo := -4839517, hi := 4839517}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_right
namespace N0_left
noncomputable def t0 : RBox := {lo := 61451870782754334557887457376, hi := 61451870782926870143619619324}
lemma t0_checked : ((hm12_0_0_2.realAnswer).add hm12_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := 205178031696981519097267862259, hi := 205178031697181508741523160691}
lemma t1_checked : ((hm12_0_0_3.realAnswer).add hm12_1_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := 138161970335826072124715558198, hi := 138161970336002369894236566372}
lemma t2_checked : ((hm12_0_0_4.realAnswer).add hm12_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := -162518927082370702380414367864, hi := -162518927082245616259477333704}
lemma t3_checked : ((hm12_0_0_5.realAnswer).add hm12_1_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := -178805063809430992100545895936, hi := -178805063809356782873393901049}
lemma t4_checked : ((hm12_0_0_6.realAnswer).add hm12_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := 41845071135833034145133820814, hi := 41845071135870865147409400635}
lemma t5_checked : ((hm12_0_0_7.realAnswer).add hm12_1_1_7.realAnswer).scale (243) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := 83358506816283278389814666047, hi := 83358506816300192241911307787}
lemma t6_checked : ((hm12_0_0_8.realAnswer).add hm12_1_1_8.realAnswer).scale (-729) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := -71073030024369763248884216, hi := -71073030017631863712068397}
lemma t7_checked : ((hm12_0_0_9.realAnswer).add hm12_1_1_9.realAnswer).scale (2187) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := -21264717546532706095461944382, hi := -21264717546530283726339066935}
lemma t8_checked : ((hm12_0_0_10.realAnswer).add hm12_1_1_10.realAnswer).scale (-6561) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := -2414277255932790321504152666, hi := -2414277255931995893594107343}
lemma t9_checked : ((hm12_0_0_11.realAnswer).add hm12_1_1_11.realAnswer).scale (19683) 512=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := 3401290107919635471111871538, hi := 3401290107919875425279358509}
lemma t10_checked : ((hm12_0_0_12.realAnswer).add hm12_1_1_12.realAnswer).scale (-59049) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := 678496184099645750694136736, hi := 678496184099713133822869926}
lemma t11_checked : ((hm12_0_0_13.realAnswer).add hm12_1_1_13.realAnswer).scale (177147) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -91086940050472990868262756351, hi := 91086940050472990868262756351}
noncomputable def t13 : RBox := {lo := -32747839256939319082147225590, hi := 32747839256939319082147225590}
noncomputable def t14 : RBox := {lo := -11339520743565903157545117223, hi := 11339520743565903157545117223}
noncomputable def t15 : RBox := {lo := -3787449695975412374043620960, hi := 3787449695975412374043620960}
noncomputable def t16 : RBox := {lo := -1221062831484096079059057587, hi := 1221062831484096079059057587}
noncomputable def t17 : RBox := {lo := -380068875905760782769548654, hi := 380068875905760782769548654}
noncomputable def t18 : RBox := {lo := -114218903123511579077843282, hi := 114218903123511579077843282}
noncomputable def t19 : RBox := {lo := -33143555492194773979714580, hi := 33143555492194773979714580}
noncomputable def t20 : RBox := {lo := -9288578820526788622989364, hi := 9288578820526788622989364}
noncomputable def t21 : RBox := {lo := -2515269886776208955260010, hi := 2515269886776208955260010}
noncomputable def t22 : RBox := {lo := -658559963858000548233917, hi := 658559963858000548233917}
noncomputable def t23 : RBox := {lo := -166861203791677917241811, hi := 166861203791677917241811}
noncomputable def t24 : RBox := {lo := -40954902349054626329048, hi := 40954902349054626329048}
noncomputable def t25 : RBox := {lo := -9748486402679208977336, hi := 9748486402679208977336}
noncomputable def t26 : RBox := {lo := -2253051248616112321678, hi := 2253051248616112321678}
noncomputable def t27 : RBox := {lo := -506226427008888682575, hi := 506226427008888682575}
noncomputable def t28 : RBox := {lo := -110712622742236369478, hi := 110712622742236369478}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N0_left
namespace N1_left
noncomputable def t0 : RBox := {lo := 57107874017072128817429474713, hi := 57107874017213800199224982736}
lemma t0_checked : ((hm12_1_0_2.realAnswer).add hm12_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := 192307945915562840104410268524, hi := 192307945915727047145402602749}
lemma t1_checked : ((hm12_1_0_3.realAnswer).add hm12_0_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := 133937077158603429279301638906, hi := 133937077158748190084181936993}
lemma t2_checked : ((hm12_1_0_4.realAnswer).add hm12_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := -147200619180231319336594216719, hi := -147200619180128599493895095383}
lemma t3_checked : ((hm12_1_0_5.realAnswer).add hm12_0_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := -170716880058569681456544825004, hi := -170716880058508732567507869597}
lemma t4_checked : ((hm12_1_0_6.realAnswer).add hm12_0_1_6.realAnswer).scale (81) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := 33670177281767702197998047337, hi := 33670177281798780123417100315}
lemma t5_checked : ((hm12_1_0_7.realAnswer).add hm12_0_1_7.realAnswer).scale (-243) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := 78734696003978297625381685420, hi := 78734696003992197218497190068}
lemma t6_checked : ((hm12_1_0_8.realAnswer).add hm12_0_1_8.realAnswer).scale (729) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 2555489668113909381546624582, hi := 2555489668119449829809098293}
lemma t7_checked : ((hm12_1_0_9.realAnswer).add hm12_0_1_9.realAnswer).scale (-2187) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := -19808604575526106524123963469, hi := -19808604575524112593764077504}
lemma t8_checked : ((hm12_1_0_10.realAnswer).add hm12_0_1_10.realAnswer).scale (6561) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := -2988966136543382849332127188, hi := -2988966136542727749283831868}
lemma t9_checked : ((hm12_1_0_11.realAnswer).add hm12_0_1_11.realAnswer).scale (-19683) 512=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := 3101946970554742713082281773, hi := 3101946970554941211018878432}
lemma t10_checked : ((hm12_1_0_12.realAnswer).add hm12_0_1_12.realAnswer).scale (59049) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := 770085851055509757734031624, hi := 770085851055565809952062230}
lemma t11_checked : ((hm12_1_0_13.realAnswer).add hm12_0_1_13.realAnswer).scale (-177147) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -91086940050472990868262756351, hi := 91086940050472990868262756351}
noncomputable def t13 : RBox := {lo := -32747839256939319082147225590, hi := 32747839256939319082147225590}
noncomputable def t14 : RBox := {lo := -11339520743565903157545117223, hi := 11339520743565903157545117223}
noncomputable def t15 : RBox := {lo := -3787449695975412374043620960, hi := 3787449695975412374043620960}
noncomputable def t16 : RBox := {lo := -1221062831484096079059057587, hi := 1221062831484096079059057587}
noncomputable def t17 : RBox := {lo := -380068875905760782769548654, hi := 380068875905760782769548654}
noncomputable def t18 : RBox := {lo := -114218903123511579077843282, hi := 114218903123511579077843282}
noncomputable def t19 : RBox := {lo := -33143555492194773979714580, hi := 33143555492194773979714580}
noncomputable def t20 : RBox := {lo := -9288578820526788622989364, hi := 9288578820526788622989364}
noncomputable def t21 : RBox := {lo := -2515269886776208955260010, hi := 2515269886776208955260010}
noncomputable def t22 : RBox := {lo := -658559963858000548233917, hi := 658559963858000548233917}
noncomputable def t23 : RBox := {lo := -166861203791677917241811, hi := 166861203791677917241811}
noncomputable def t24 : RBox := {lo := -40954902349054626329048, hi := 40954902349054626329048}
noncomputable def t25 : RBox := {lo := -9748486402679208977336, hi := 9748486402679208977336}
noncomputable def t26 : RBox := {lo := -2253051248616112321678, hi := 2253051248616112321678}
noncomputable def t27 : RBox := {lo := -506226427008888682575, hi := 506226427008888682575}
noncomputable def t28 : RBox := {lo := -110712622742236369478, hi := 110712622742236369478}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_left
end SharpPlanar.Bernstein12

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock13_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm13_0_0_2
 def realAnswer : RBox := ⟨(-35759419444116237919690812321),(-35759419443943854742525582255)⟩
end hm13_0_0_2
namespace hm13_1_0_2
 def realAnswer : RBox := ⟨30779915230009437498026080551,30779915230150979335745531150⟩
end hm13_1_0_2
namespace hm13_0_0_3
 def realAnswer : RBox := ⟨(-46628227448638666511195283582),(-46628227448505462489422818417)⟩
end hm13_0_0_3
namespace hm13_1_0_3
 def realAnswer : RBox := ⟨48315515580349798189411862106,48315515580459163946013068788⟩
end hm13_1_0_3
namespace hm13_0_0_4
 def realAnswer : RBox := ⟨48443281182903570882924530309,48443281182981849014487094764⟩
end hm13_0_0_4
namespace hm13_1_0_4
 def realAnswer : RBox := ⟨(-43307050787927565948149490037),(-43307050787863295488325420361)⟩
end hm13_1_0_4
namespace hm13_0_0_5
 def realAnswer : RBox := ⟨31681855348504598604097282568,31681855348541621169488600705⟩
end hm13_0_0_5
namespace hm13_1_0_5
 def realAnswer : RBox := ⟨(-32285903197318717458535786237),(-32285903197288318751586773575)⟩
end hm13_1_0_5
namespace hm13_0_0_6
 def realAnswer : RBox := ⟨(-26852248895882905265208649177),(-26852248895868265225071126546)⟩
end hm13_0_0_6
namespace hm13_1_0_6
 def realAnswer : RBox := ⟨24513638814118619451056885878,24513638814130640745206187082⟩
end hm13_1_0_6
namespace hm13_0_0_7
 def realAnswer : RBox := ⟨(-6606848801494838244397521535),(-6606848801489864404095228215)⟩
end hm13_0_0_7
namespace hm13_1_0_7
 def realAnswer : RBox := ⟨6855003349057609024142460536,6855003349061693360449406439⟩
end hm13_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock13_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm13_0_0_8
 def realAnswer : RBox := ⟨6215667836631988628230323151,6215667836633470208088760059⟩
end hm13_0_0_8
namespace hm13_1_0_8
 def realAnswer : RBox := ⟨(-5699171844162648416671329608),(-5699171844161431741621519283)⟩
end hm13_1_0_8
namespace hm13_0_0_9
 def realAnswer : RBox := ⟨692714456312292144991335379,692714456312685176446296840⟩
end hm13_0_0_9
namespace hm13_1_0_9
 def realAnswer : RBox := ⟨(-749374371708701465582257100),(-749374371708378693599488647)⟩
end hm13_1_0_9
namespace hm13_0_0_10
 def realAnswer : RBox := ⟨(-796777699532712677140078569),(-796777699532618667447362925)⟩
end hm13_0_0_10
namespace hm13_1_0_10
 def realAnswer : RBox := ⟨730515796928993686512837075,730515796929070893920293030⟩
end hm13_1_0_10
namespace hm13_0_0_11
 def realAnswer : RBox := ⟨(-43477061816050602804894121),(-43477061816030123420467800)⟩
end hm13_0_0_11
namespace hm13_1_0_11
 def realAnswer : RBox := ⟨50856540824985348709901075,50856540825002168493394150⟩
end hm13_1_0_11
namespace hm13_0_0_12
 def realAnswer : RBox := ⟨65492904298390834241322100,65492904298394931273779114⟩
end hm13_0_0_12
namespace hm13_1_0_12
 def realAnswer : RBox := ⟨(-59955791527451674101069094),(-59955791527448309049931691)⟩
end hm13_1_0_12
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock13_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm13_0_1_2
 def realAnswer : RBox := ⟨(-3556423611936107098842542891),(-3556423611936103282159578944)⟩
end hm13_0_1_2
namespace hm13_1_1_2
 def realAnswer : RBox := ⟨5938195380126575043382703656,5938195380126578071387958453⟩
end hm13_1_1_2
namespace hm13_0_1_3
 def realAnswer : RBox := ⟨(-28585618646489137145726201584),(-28585618646489131747647518117)⟩
end hm13_0_1_3
namespace hm13_1_1_3
 def realAnswer : RBox := ⟨24544598698633587242193477527,24544598698633591535600761956⟩
end hm13_1_1_3
namespace hm13_0_1_4
 def realAnswer : RBox := ⟨6964535267077789267838119987,6964535267077794997204288964⟩
end hm13_0_1_4
namespace hm13_1_1_4
 def realAnswer : RBox := ⟨(-8893689330508213887329504515),(-8893689330508209318921354603)⟩
end hm13_1_1_4
namespace hm13_0_1_5
 def realAnswer : RBox := ⟨18066453153226222863856441121,18066453153226227734002799944⟩
end hm13_0_1_5
namespace hm13_1_1_5
 def realAnswer : RBox := ⟨(-15393868290565750972482591606),(-15393868290565747078723978511)⟩
end hm13_1_1_5
namespace hm13_0_1_6
 def realAnswer : RBox := ⟨(-4325870706208662249896430392),(-4325870706208658797057649160)⟩
end hm13_0_1_6
namespace hm13_1_1_6
 def realAnswer : RBox := ⟨4893087489694441594911401416,4893087489694444362743415845⟩
end hm13_1_1_6
namespace hm13_0_1_7
 def realAnswer : RBox := ⟨(-5344804657206575754879075766),(-5344804657206573653758256023)⟩
end hm13_0_1_7
namespace hm13_1_1_7
 def realAnswer : RBox := ⟨4526619509699792582340059503,4526619509699794271094986377⟩
end hm13_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock13_11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm13_0_1_8
 def realAnswer : RBox := ⟨1292094030963943135630710706,1292094030963944255739196839⟩
end hm13_0_1_8
namespace hm13_1_1_8
 def realAnswer : RBox := ⟨(-1366340184551885592788331248),(-1366340184551884690233623407)⟩
end hm13_1_1_8
namespace hm13_0_1_9
 def realAnswer : RBox := ⟨905730055144685286236928570,905730055144685817719679919⟩
end hm13_0_1_9
namespace hm13_1_1_9
 def realAnswer : RBox := ⟨(-763132067492261161948482692),(-763132067492260732635431775)⟩
end hm13_1_1_9
namespace hm13_0_1_10
 def realAnswer : RBox := ⟨(-225114110804242884639023416),(-225114110804242657520098760)⟩
end hm13_0_1_10
namespace hm13_1_1_10
 def realAnswer : RBox := ⟨228450033696178622819366330,228450033696178806701358326⟩
end hm13_1_1_10
namespace hm13_0_1_11
 def realAnswer : RBox := ⟨(-98508324966930146483699464),(-98508324966930058093746275)⟩
end hm13_0_1_11
namespace hm13_1_1_11
 def realAnswer : RBox := ⟨82582782028404384430066527,82582782028404456158874846⟩
end hm13_1_1_11
namespace hm13_0_1_12
 def realAnswer : RBox := ⟨25587563097985382626095110,25587563097985414273319526⟩
end hm13_0_1_12
namespace hm13_1_1_12
 def realAnswer : RBox := ⟨(-25288516306850174054006785),(-25288516306850148303461890)⟩
end hm13_1_1_12
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein13
open IntegerIntervals CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 29821224063817276671137623802, hi := 29821224063989662876308108665}
lemma t0_checked : ((hm13_0_0_2.realAnswer).add hm13_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := 22083628749871870953822056461, hi := 22083628750005079269001806055}
lemma t1_checked : ((hm13_0_0_3.realAnswer).add hm13_1_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -39549591852473639695565740161, hi := -39549591852395356995595025794}
lemma t2_checked : ((hm13_0_0_4.realAnswer).add hm13_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := -16287987057975874090764622194, hi := -16287987057938847631614690962}
lemma t3_checked : ((hm13_0_0_5.realAnswer).add hm13_1_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 21959161406173820862327710701, hi := 21959161406188463670297247761}
lemma t4_checked : ((hm13_0_0_6.realAnswer).add hm13_1_1_6.realAnswer).scale (-1) 1=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := 2080229291790070133000241838, hi := 2080229291795045662057462032}
lemma t5_checked : ((hm13_0_0_7.realAnswer).add hm13_1_1_7.realAnswer).scale (-1) 1=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -4849327652081585517855136652, hi := -4849327652080103035441991903}
lemma t6_checked : ((hm13_0_0_8.realAnswer).add hm13_1_1_8.realAnswer).scale (-1) 1=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 70417611179575556189134935, hi := 70417611179969016957147313}
lemma t7_checked : ((hm13_0_0_9.realAnswer).add hm13_1_1_9.realAnswer).scale (-1) 1=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 568327665836439860746004599, hi := 568327665836534054320712239}
lemma t8_checked : ((hm13_0_0_10.realAnswer).add hm13_1_1_10.realAnswer).scale (-1) 1=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := -39105720212374332738407046, hi := -39105720212353781625172406}
lemma t9_checked : ((hm13_0_0_11.realAnswer).add hm13_1_1_11.realAnswer).scale (-1) 1=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := -40204387991544782970317224, hi := -40204387991540660187315315}
lemma t10_checked : ((hm13_0_0_12.realAnswer).add hm13_1_1_12.realAnswer).scale (-1) 1=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -2531115368513107029833780037, hi := 2531115368513107029833780037}
noncomputable def t12 : RBox := {lo := -617291382224693317143528265, hi := 617291382224693317143528265}
noncomputable def t13 : RBox := {lo := -144478140411823014312463399, hi := 144478140411823014312463399}
noncomputable def t14 : RBox := {lo := -32567611871130225775617023, hi := 32567611871130225775617023}
noncomputable def t15 : RBox := {lo := -7086462145518744700765859, hi := 7086462145518744700765859}
noncomputable def t16 : RBox := {lo := -1490272985556831369284206, hi := 1490272985556831369284206}
noncomputable def t17 : RBox := {lo := -303042818377332642491714, hi := 303042818377332642491714}
noncomputable def t18 : RBox := {lo := -59589010613871900078267, hi := 59589010613871900078267}
noncomputable def t19 : RBox := {lo := -11329372415748521439348, hi := 11329372415748521439348}
noncomputable def t20 : RBox := {lo := -2082539517045679030472, hi := 2082539517045679030472}
noncomputable def t21 : RBox := {lo := -370140407122910181103, hi := 370140407122910181103}
noncomputable def t22 : RBox := {lo := -63628917450002357168, hi := 63628917450002357168}
noncomputable def t23 : RBox := {lo := -10584744548565259465, hi := 10584744548565259465}
noncomputable def t24 : RBox := {lo := -1705111562507517738, hi := 1705111562507517738}
noncomputable def t25 : RBox := {lo := -266227122488009142, hi := 266227122488009142}
noncomputable def t26 : RBox := {lo := -40328799510286982, hi := 40328799510286982}
noncomputable def t27 : RBox := {lo := -5933603166316064, hi := 5933603166316064}
noncomputable def t28 : RBox := {lo := -848915492766886, hi := 848915492766886}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N0_right
namespace N1_right
noncomputable def t0 : RBox := {lo := 27223491618073330399183537660, hi := 27223491618214876053585952206}
lemma t0_checked : ((hm13_1_0_2.realAnswer).add hm13_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := 19729896933860661043685660522, hi := 19729896933970032198365550671}
lemma t1_checked : ((hm13_1_0_3.realAnswer).add hm13_0_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -36342515520849776680311370050, hi := -36342515520785500491121131397}
lemma t2_checked : ((hm13_1_0_4.realAnswer).add hm13_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := -14219450044092494594679345116, hi := -14219450044062091017583973631}
lemma t3_checked : ((hm13_1_0_5.realAnswer).add hm13_0_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 20187768107909957201160455486, hi := 20187768107921981948148537922}
lemma t4_checked : ((hm13_1_0_6.realAnswer).add hm13_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := 1510198691851033269263384770, hi := 1510198691855119706691150416}
lemma t5_checked : ((hm13_1_0_7.realAnswer).add hm13_0_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -4407077813198705281040618902, hi := -4407077813197487485882322444}
lemma t6_checked : ((hm13_1_0_8.realAnswer).add hm13_0_1_8.realAnswer).scale (1) 1=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 156355683435983820654671470, hi := 156355683436307124120191272}
lemma t7_checked : ((hm13_1_0_9.realAnswer).add hm13_0_1_9.realAnswer).scale (1) 1=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 505401686124750801873813659, hi := 505401686124828236400194270}
lemma t8_checked : ((hm13_1_0_10.realAnswer).add hm13_0_1_10.realAnswer).scale (1) 1=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := -47651784141944797773798389, hi := -47651784141927889600352125}
lemma t9_checked : ((hm13_1_0_11.realAnswer).add hm13_0_1_11.realAnswer).scale (1) 1=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := -34368228429466291474973984, hi := -34368228429462894776612165}
lemma t10_checked : ((hm13_1_0_12.realAnswer).add hm13_0_1_12.realAnswer).scale (1) 1=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -2531115368513107029833780037, hi := 2531115368513107029833780037}
noncomputable def t12 : RBox := {lo := -617291382224693317143528265, hi := 617291382224693317143528265}
noncomputable def t13 : RBox := {lo := -144478140411823014312463399, hi := 144478140411823014312463399}
noncomputable def t14 : RBox := {lo := -32567611871130225775617023, hi := 32567611871130225775617023}
noncomputable def t15 : RBox := {lo := -7086462145518744700765859, hi := 7086462145518744700765859}
noncomputable def t16 : RBox := {lo := -1490272985556831369284206, hi := 1490272985556831369284206}
noncomputable def t17 : RBox := {lo := -303042818377332642491714, hi := 303042818377332642491714}
noncomputable def t18 : RBox := {lo := -59589010613871900078267, hi := 59589010613871900078267}
noncomputable def t19 : RBox := {lo := -11329372415748521439348, hi := 11329372415748521439348}
noncomputable def t20 : RBox := {lo := -2082539517045679030472, hi := 2082539517045679030472}
noncomputable def t21 : RBox := {lo := -370140407122910181103, hi := 370140407122910181103}
noncomputable def t22 : RBox := {lo := -63628917450002357168, hi := 63628917450002357168}
noncomputable def t23 : RBox := {lo := -10584744548565259465, hi := 10584744548565259465}
noncomputable def t24 : RBox := {lo := -1705111562507517738, hi := 1705111562507517738}
noncomputable def t25 : RBox := {lo := -266227122488009142, hi := 266227122488009142}
noncomputable def t26 : RBox := {lo := -40328799510286982, hi := 40328799510286982}
noncomputable def t27 : RBox := {lo := -5933603166316064, hi := 5933603166316064}
noncomputable def t28 : RBox := {lo := -848915492766886, hi := 848915492766886}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_right
namespace N0_left
noncomputable def t0 : RBox := {lo := 29821224063817276671137623802, hi := 29821224063989662876308108665}
lemma t0_checked : ((hm13_0_0_2.realAnswer).add hm13_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -11041814375002539634500903028, hi := -11041814374935935476911028230}
lemma t1_checked : ((hm13_0_0_3.realAnswer).add hm13_1_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -9887397963118409923891435041, hi := -9887397963098839248898756448}
lemma t2_checked : ((hm13_0_0_4.realAnswer).add hm13_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 2035998382242355953951836370, hi := 2035998382246984261345577775}
lemma t3_checked : ((hm13_0_0_5.realAnswer).add hm13_1_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 1372447587885863803895481918, hi := 1372447587886778979393577986}
lemma t4_checked : ((hm13_0_0_6.realAnswer).add hm13_1_1_6.realAnswer).scale (-1) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := -65007165368595176939295689, hi := -65007165368439691656257557}
lemma t5_checked : ((hm13_0_0_7.realAnswer).add hm13_1_1_7.realAnswer).scale (1) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -75770744563774773716486511, hi := -75770744563751609928781123}
lemma t6_checked : ((hm13_0_0_8.realAnswer).add hm13_1_1_8.realAnswer).scale (-1) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := -550137587343507944977714, hi := -550137587340434032727616}
lemma t7_checked : ((hm13_0_0_9.realAnswer).add hm13_1_1_9.realAnswer).scale (1) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 2220029944673593206039080, hi := 2220029944673961149690283}
lemma t8_checked : ((hm13_0_0_10.realAnswer).add hm13_1_1_10.realAnswer).scale (-1) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 76378359789753479736664, hi := 76378359789793618629702}
lemma t9_checked : ((hm13_0_0_11.realAnswer).add hm13_1_1_11.realAnswer).scale (1) 512=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := -39262097647992952119451, hi := -39262097647988925964175}
lemma t10_checked : ((hm13_0_0_12.realAnswer).add hm13_1_1_12.realAnswer).scale (-1) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -1235896176031790541911026, hi := 1235896176031790541911026}
noncomputable def t12 : RBox := {lo := -150705903863450516880745, hi := 150705903863450516880745}
noncomputable def t13 : RBox := {lo := -17636491749490114051815, hi := 17636491749490114051815}
noncomputable def t14 : RBox := {lo := -1987769279243788194313, hi := 1987769279243788194313}
noncomputable def t15 : RBox := {lo := -216261662155723410058, hi := 216261662155723410058}
noncomputable def t16 : RBox := {lo := -22739761132153798970, hi := 22739761132153798970}
noncomputable def t17 : RBox := {lo := -2312033221262608662, hi := 2312033221262608662}
noncomputable def t18 : RBox := {lo := -227314035850036240, hi := 227314035850036240}
noncomputable def t19 : RBox := {lo := -21609062987801593, hi := 21609062987801593}
noncomputable def t20 : RBox := {lo := -1986064450307540, hi := 1986064450307540}
noncomputable def t21 : RBox := {lo := -176496699868637, hi := 176496699868637}
noncomputable def t22 : RBox := {lo := -15170316088201, hi := 15170316088201}
noncomputable def t23 : RBox := {lo := -1261799877711, hi := 1261799877711}
noncomputable def t24 : RBox := {lo := -101632568986, hi := 101632568986}
noncomputable def t25 : RBox := {lo := -7934186533, hi := 7934186533}
noncomputable def t26 : RBox := {lo := -600945943, hi := 600945943}
noncomputable def t27 : RBox := {lo := -44208789, hi := 44208789}
noncomputable def t28 : RBox := {lo := -3162457, hi := 3162457}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N0_left
namespace N1_left
noncomputable def t0 : RBox := {lo := 27223491618073330399183537660, hi := 27223491618214876053585952206}
lemma t0_checked : ((hm13_1_0_2.realAnswer).add hm13_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -9864948466985016099182775336, hi := -9864948466930330521842830261}
lemma t1_checked : ((hm13_1_0_3.realAnswer).add hm13_0_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -9085628880212444170077842513, hi := -9085628880196375122780282849}
lemma t2_checked : ((hm13_1_0_4.realAnswer).add hm13_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 1777431255507761377197996703, hi := 1777431255511561824334918140}
lemma t3_checked : ((hm13_1_0_5.realAnswer).add hm13_0_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 1261735506744372325072528467, hi := 1261735506745123871759283621}
lemma t4_checked : ((hm13_1_0_6.realAnswer).add hm13_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := -47193709120472490834098451, hi := -47193709120344789664480774}
lemma t5_checked : ((hm13_1_0_7.realAnswer).add hm13_0_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -68860590831229770016259671, hi := -68860590831210741966911288}
lemma t6_checked : ((hm13_1_0_8.realAnswer).add hm13_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := -1221528776846149407188995, hi := -1221528776843623598864620}
lemma t7_checked : ((hm13_1_0_9.realAnswer).add hm13_0_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 1974225336424807819819584, hi := 1974225336425110298438259}
lemma t8_checked : ((hm13_1_0_10.realAnswer).add hm13_0_1_10.realAnswer).scale (1) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 93069890902202909375687, hi := 93069890902235933151950}
lemma t9_checked : ((hm13_1_0_11.realAnswer).add hm13_0_1_11.realAnswer).scale (-1) 512=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := -33562723075650675268530, hi := -33562723075647358180285}
lemma t10_checked : ((hm13_1_0_12.realAnswer).add hm13_0_1_12.realAnswer).scale (1) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -1235896176031790541911026, hi := 1235896176031790541911026}
noncomputable def t12 : RBox := {lo := -150705903863450516880745, hi := 150705903863450516880745}
noncomputable def t13 : RBox := {lo := -17636491749490114051815, hi := 17636491749490114051815}
noncomputable def t14 : RBox := {lo := -1987769279243788194313, hi := 1987769279243788194313}
noncomputable def t15 : RBox := {lo := -216261662155723410058, hi := 216261662155723410058}
noncomputable def t16 : RBox := {lo := -22739761132153798970, hi := 22739761132153798970}
noncomputable def t17 : RBox := {lo := -2312033221262608662, hi := 2312033221262608662}
noncomputable def t18 : RBox := {lo := -227314035850036240, hi := 227314035850036240}
noncomputable def t19 : RBox := {lo := -21609062987801593, hi := 21609062987801593}
noncomputable def t20 : RBox := {lo := -1986064450307540, hi := 1986064450307540}
noncomputable def t21 : RBox := {lo := -176496699868637, hi := 176496699868637}
noncomputable def t22 : RBox := {lo := -15170316088201, hi := 15170316088201}
noncomputable def t23 : RBox := {lo := -1261799877711, hi := 1261799877711}
noncomputable def t24 : RBox := {lo := -101632568986, hi := 101632568986}
noncomputable def t25 : RBox := {lo := -7934186533, hi := 7934186533}
noncomputable def t26 : RBox := {lo := -600945943, hi := 600945943}
noncomputable def t27 : RBox := {lo := -44208789, hi := 44208789}
noncomputable def t28 : RBox := {lo := -3162457, hi := 3162457}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_left
end SharpPlanar.Bernstein13

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock15_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm15_0_0_2
 def realAnswer : RBox := ⟨(-40917779543972341666446182637),(-40917779543799953371423683666)⟩
end hm15_0_0_2
namespace hm15_1_0_2
 def realAnswer : RBox := ⟨38418017252846763750351432514,38418017252988304886629725204⟩
end hm15_1_0_2
namespace hm15_0_0_3
 def realAnswer : RBox := ⟨17608961882319443557501275264,17608961882452650992008285906⟩
end hm15_0_0_3
namespace hm15_1_0_3
 def realAnswer : RBox := ⟨(-12409947219169811654632318931),(-12409947219060446517242094132)⟩
end hm15_1_0_3
namespace hm15_0_0_4
 def realAnswer : RBox := ⟨49517535006138582169526879069,49517535006216862217875141566⟩
end hm15_0_0_4
namespace hm15_1_0_4
 def realAnswer : RBox := ⟨(-46588685987599600321221165563),(-46588685987535330200949753308)⟩
end hm15_1_0_4
namespace hm15_0_0_5
 def realAnswer : RBox := ⟨(-15990853615066629452216021562),(-15990853615029605964255470146)⟩
end hm15_0_0_5
namespace hm15_1_0_5
 def realAnswer : RBox := ⟨12299828388271689350649158982,12299828388302087914756578121⟩
end hm15_1_0_5
namespace hm15_0_0_6
 def realAnswer : RBox := ⟨(-25340424568025372713961775833),(-25340424568010732297617762656)⟩
end hm15_0_0_6
namespace hm15_1_0_6
 def realAnswer : RBox := ⟨23742000638959456114986860792,23742000638971477361470044025⟩
end hm15_1_0_6
namespace hm15_0_0_7
 def realAnswer : RBox := ⟨3418571098313921534771072900,3418571098318895508934774599⟩
end hm15_0_0_7
namespace hm15_1_0_7
 def realAnswer : RBox := ⟨(-2458083693898358088193726713),(-2458083693894273766440106432)⟩
end hm15_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock15_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm15_0_0_8
 def realAnswer : RBox := ⟨5768052270412901790290936294,5768052270414383411657683355⟩
end hm15_0_0_8
namespace hm15_1_0_8
 def realAnswer : RBox := ⟨(-5392857453675090443250740371),(-5392857453673873772059920068)⟩
end hm15_1_0_8
namespace hm15_0_0_9
 def realAnswer : RBox := ⟨(-364605533437995296498556600),(-364605533437602253494908194)⟩
end hm15_0_0_9
namespace hm15_1_0_9
 def realAnswer : RBox := ⟨225704659568100544483422971,225704659568423315417115456⟩
end hm15_1_0_9
namespace hm15_0_0_10
 def realAnswer : RBox := ⟨(-739683115309532773390967722),(-739683115309438760818063668)⟩
end hm15_0_0_10
namespace hm15_1_0_10
 def realAnswer : RBox := ⟨690689284851788024321360790,690689284851865231475626733⟩
end hm15_1_0_10
namespace hm15_0_0_11
 def realAnswer : RBox := ⟨24981630995007524551504110,24981630995028004595030568⟩
end hm15_0_0_11
namespace hm15_1_0_11
 def realAnswer : RBox := ⟨(-11776166116199366520173325),(-11776166116182546801143874)⟩
end hm15_1_0_11
namespace hm15_0_0_12
 def realAnswer : RBox := ⟨61097656590676598851068612,61097656590680696021763809⟩
end hm15_0_0_12
namespace hm15_1_0_12
 def realAnswer : RBox := ⟨(-56997369351655511210769957),(-56997369351652146173816507)⟩
end hm15_1_0_12
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock15_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm15_0_1_2
 def realAnswer : RBox := ⟨(-14011625264835364092335887370),(-14011625264835363172510406513)⟩
end hm15_0_1_2
namespace hm15_1_1_2
 def realAnswer : RBox := ⟨13758441533732691807173141121,13758441533732692447593089794⟩
end hm15_1_1_2
namespace hm15_0_1_3
 def realAnswer : RBox := ⟨(-7906781799710130363751617515),(-7906781799710129088017603182)⟩
end hm15_0_1_3
namespace hm15_1_1_3
 def realAnswer : RBox := ⟨5032007640385820011624422122,5032007640385820908734902893⟩
end hm15_1_1_3
namespace hm15_0_1_4
 def realAnswer : RBox := ⟨16111611093716564252414916217,16111611093716565579363454629⟩
end hm15_0_1_4
namespace hm15_1_1_4
 def realAnswer : RBox := ⟨(-15508614347840595308592457810),(-15508614347840594365230233062)⟩
end hm15_1_1_4
namespace hm15_0_1_5
 def realAnswer : RBox := ⟨3823476042735603178367492259,3823476042735604283779365176⟩
end hm15_0_1_5
namespace hm15_1_1_5
 def realAnswer : RBox := ⟨(-2102183242683958690305123447),(-2102183242683957895614010390)⟩
end hm15_1_1_5
namespace hm15_0_1_6
 def realAnswer : RBox := ⟨(-7290594602856026856255755453),(-7290594602856026088159931400)⟩
end hm15_0_1_6
namespace hm15_1_1_6
 def realAnswer : RBox := ⟨6907593903617864225667536331,6907593903617864784316646196⟩
end hm15_1_1_6
namespace hm15_0_1_7
 def realAnswer : RBox := ⟨(-755453699195408323719932970),(-755453699195407865556375602)⟩
end hm15_0_1_7
namespace hm15_1_1_7
 def realAnswer : RBox := ⟨275039689678132830262714127,275039689678133167328560555⟩
end hm15_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock15_11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm15_0_1_8
 def realAnswer : RBox := ⟨1740947868617444868052235658,1740947868617445107352659969⟩
end hm15_0_1_8
namespace hm15_1_1_8
 def realAnswer : RBox := ⟨(-1628824968229977411736256679),(-1628824968229977233664586584)⟩
end hm15_1_1_8
namespace hm15_0_1_9
 def realAnswer : RBox := ⟨56655552567523856509591551,56655552567523967786940042⟩
end hm15_0_1_9
namespace hm15_1_1_9
 def realAnswer : RBox := ⟨19829148803302068901552585,19829148803302152620937878⟩
end hm15_1_1_9
namespace hm15_0_1_10
 def realAnswer : RBox := ⟨(-255037926294055466406623981),(-255037926294055419697498819)⟩
end hm15_0_1_10
namespace hm15_1_1_10
 def realAnswer : RBox := ⟨236216599562096520250515710,236216599562096555782920351⟩
end hm15_1_1_10
namespace hm15_0_1_11
 def realAnswer : RBox := ⟨2870634082974198362974753,2870634082974216298701158⟩
end hm15_0_1_11
namespace hm15_1_1_11
 def realAnswer : RBox := ⟨(-10648986374384356563361717),(-10648986374384342761847257)⟩
end hm15_1_1_11
namespace hm15_0_1_12
 def realAnswer : RBox := ⟨25130278084220019911423634,25130278084220026326083509⟩
end hm15_0_1_12
namespace hm15_1_1_12
 def realAnswer : RBox := ⟨(-23086710416364026214103286),(-23086710416364021206026673)⟩
end hm15_1_1_12
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein15
open IntegerIntervals CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 27159338010067260923830593872, hi := 27159338010239649859273041516}
lemma t0_checked : ((hm15_0_0_2.realAnswer).add hm15_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -11320484761419235950371594400, hi := -11320484761352631784562848693}
lemma t1_checked : ((hm15_0_0_3.realAnswer).add hm15_1_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -8502230164594066963161227126, hi := -8502230164574496715233605314}
lemma t2_checked : ((hm15_0_0_4.realAnswer).add hm15_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 2261629607214195482483685067, hi := 2261629607218823517815143127}
lemma t3_checked : ((hm15_0_0_5.realAnswer).add hm15_1_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 1152051916524554219581319778, hi := 1152051916525469280518389969}
lemma t4_checked : ((hm15_0_0_6.realAnswer).add hm15_1_1_6.realAnswer).scale (-1) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := -115425337124907146133229224, hi := -115425337124751698907305844}
lemma t5_checked : ((hm15_0_0_7.realAnswer).add hm15_1_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -64675426596631346531142138, hi := -64675426596608193414916868}
lemma t6_checked : ((hm15_0_0_8.realAnswer).add hm15_1_1_8.realAnswer).scale (-1) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 2693565504955469538077893, hi := 2693565504958540840601594}
lemma t7_checked : ((hm15_0_0_9.realAnswer).add hm15_1_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 1966666077138055488418528, hi := 1966666077138422863829891}
lemma t8_checked : ((hm15_0_0_10.realAnswer).add hm15_1_1_10.realAnswer).scale (-1) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := -27993446524694652017937, hi := -27993446524654624976840}
lemma t9_checked : ((hm15_0_0_11.realAnswer).add hm15_1_1_11.realAnswer).scale (-1) 512=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := -37120064623356127749744, hi := -37120064623352121715786}
lemma t10_checked : ((hm15_0_0_12.realAnswer).add hm15_1_1_12.realAnswer).scale (-1) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -1061230630839543253842157, hi := 1061230630839543253842157}
noncomputable def t12 : RBox := {lo := -124676864188939402959787, hi := 124676864188939402959787}
noncomputable def t13 : RBox := {lo := -14011371607662972651343, hi := 14011371607662972651343}
noncomputable def t14 : RBox := {lo := -1513738773311503444352, hi := 1513738773311503444352}
noncomputable def t15 : RBox := {lo := -157824026550899286770, hi := 157824026550899286770}
noncomputable def t16 : RBox := {lo := -15922942750219540366, hi := 15922942750219540366}
noncomputable def t17 : RBox := {lo := -1557074307019053506, hi := 1557074307019053506}
noncomputable def t18 : RBox := {lo := -147690407521422312, hi := 147690407521422312}
noncomputable def t19 : RBox := {lo := -13589382730293059, hi := 13589382730293059}
noncomputable def t20 : RBox := {lo := -1212674233406933, hi := 1212674233406933}
noncomputable def t21 : RBox := {lo := -104912039047631, hi := 104912039047631}
noncomputable def t22 : RBox := {lo := -8796397165936, hi := 8796397165936}
noncomputable def t23 : RBox := {lo := -714679113149, hi := 714679113149}
noncomputable def t24 : RBox := {lo := -56267812699, hi := 56267812699}
noncomputable def t25 : RBox := {lo := -4293965936, hi := 4293965936}
noncomputable def t26 : RBox := {lo := -317759162, hi := 317759162}
noncomputable def t27 : RBox := {lo := -22816166, hi := 22816166}
noncomputable def t28 : RBox := {lo := -1590803, hi := 1590803}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N0_right
namespace N1_right
noncomputable def t0 : RBox := {lo := 24406391988011399658015545144, hi := 24406391988152941714119318691}
lemma t0_checked : ((hm15_1_0_2.realAnswer).add hm15_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -10158364509439971009191968223, hi := -10158364509385287802629848657}
lemma t1_checked : ((hm15_1_0_3.realAnswer).add hm15_0_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -7619268723470759017201562337, hi := -7619268723454691155396574669}
lemma t2_checked : ((hm15_1_0_4.realAnswer).add hm15_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 2015413053875911566127081405, hi := 2015413053879711524816992913}
lemma t3_checked : ((hm15_1_0_5.realAnswer).add hm15_0_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 1028212877256464328670694083, hi := 1028212877257215704581882040}
lemma t4_checked : ((hm15_1_0_6.realAnswer).add hm15_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := -100423043534180200372301866, hi := -100423043534052550999890063}
lemma t5_checked : ((hm15_1_0_7.realAnswer).add hm15_0_1_7.realAnswer).scale (1) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -57061087266525712112476637, hi := -57061087266506697886050939}
lemma t6_checked : ((hm15_1_0_8.realAnswer).add hm15_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 2205939157309565632757925, hi := 2205939157312088150031684}
lemma t7_checked : ((hm15_1_0_9.realAnswer).add hm15_0_1_9.realAnswer).scale (1) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 1701763119366142804354440, hi := 1701763119366444577258313}
lemma t8_checked : ((hm15_1_0_10.realAnswer).add hm15_0_1_10.realAnswer).scale (1) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := -17393617252392906557029, hi := -17393617252360020512583}
lemma t9_checked : ((hm15_1_0_11.realAnswer).add hm15_0_1_11.realAnswer).scale (1) 512=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := -31120206315854971972018, hi := -31120206315851679538801}
lemma t10_checked : ((hm15_1_0_12.realAnswer).add hm15_0_1_12.realAnswer).scale (1) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -1061230630839543253842157, hi := 1061230630839543253842157}
noncomputable def t12 : RBox := {lo := -124676864188939402959787, hi := 124676864188939402959787}
noncomputable def t13 : RBox := {lo := -14011371607662972651343, hi := 14011371607662972651343}
noncomputable def t14 : RBox := {lo := -1513738773311503444352, hi := 1513738773311503444352}
noncomputable def t15 : RBox := {lo := -157824026550899286770, hi := 157824026550899286770}
noncomputable def t16 : RBox := {lo := -15922942750219540366, hi := 15922942750219540366}
noncomputable def t17 : RBox := {lo := -1557074307019053506, hi := 1557074307019053506}
noncomputable def t18 : RBox := {lo := -147690407521422312, hi := 147690407521422312}
noncomputable def t19 : RBox := {lo := -13589382730293059, hi := 13589382730293059}
noncomputable def t20 : RBox := {lo := -1212674233406933, hi := 1212674233406933}
noncomputable def t21 : RBox := {lo := -104912039047631, hi := 104912039047631}
noncomputable def t22 : RBox := {lo := -8796397165936, hi := 8796397165936}
noncomputable def t23 : RBox := {lo := -714679113149, hi := 714679113149}
noncomputable def t24 : RBox := {lo := -56267812699, hi := 56267812699}
noncomputable def t25 : RBox := {lo := -4293965936, hi := 4293965936}
noncomputable def t26 : RBox := {lo := -317759162, hi := 317759162}
noncomputable def t27 : RBox := {lo := -22816166, hi := 22816166}
noncomputable def t28 : RBox := {lo := -1590803, hi := 1590803}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_right
namespace N0_left
noncomputable def t0 : RBox := {lo := 27159338010067260923830593872, hi := 27159338010239649859273041516}
lemma t0_checked : ((hm15_0_0_2.realAnswer).add hm15_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := 22640969522705263569125697386, hi := 22640969522838471900743188799}
lemma t1_checked : ((hm15_0_0_3.realAnswer).add hm15_1_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -34008920658376267852644908504, hi := -34008920658297986860934421259}
lemma t2_checked : ((hm15_0_0_4.realAnswer).add hm15_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := -18093036857750588142521145009, hi := -18093036857713563859869480536}
lemma t3_checked : ((hm15_0_0_5.realAnswer).add hm15_1_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 18432830664392867513301116460, hi := 18432830664407508488294239502}
lemma t4_checked : ((hm15_0_0_6.realAnswer).add hm15_1_1_6.realAnswer).scale (-1) 1=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := 3693610787992054365033787027, hi := 3693610787997028676263335154}
lemma t5_checked : ((hm15_0_0_7.realAnswer).add hm15_1_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -4139227302184406177993096771, hi := -4139227302182924378554679615}
lemma t6_checked : ((hm15_0_0_8.realAnswer).add hm15_1_1_8.realAnswer).scale (-1) 1=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := -344776384634693227597004015, hi := -344776384634300100873970316}
lemma t7_checked : ((hm15_0_0_9.realAnswer).add hm15_1_1_9.realAnswer).scale (1) 1=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 503466515747342205035143317, hi := 503466515747436253140452012}
lemma t8_checked : ((hm15_0_0_10.realAnswer).add hm15_1_1_10.realAnswer).scale (-1) 1=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 14332644620623167988142393, hi := 14332644620643661833183311}
lemma t9_checked : ((hm15_0_0_11.realAnswer).add hm15_1_1_11.realAnswer).scale (1) 1=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := -38010946174316674815737136, hi := -38010946174312572636965326}
lemma t10_checked : ((hm15_0_0_12.realAnswer).add hm15_1_1_12.realAnswer).scale (-1) 1=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -2173400331959384583868736519, hi := 2173400331959384583868736519}
noncomputable def t12 : RBox := {lo := -510676435717895794523285937, hi := 510676435717895794523285937}
noncomputable def t13 : RBox := {lo := -114781156209975071959800993, hi := 114781156209975071959800993}
noncomputable def t14 : RBox := {lo := -24801096061935672432257826, hi := 24801096061935672432257826}
noncomputable def t15 : RBox := {lo := -5171577702019867828849372, hi := 5171577702019867828849372}
noncomputable def t16 : RBox := {lo := -1043525976078387797403047, hi := 1043525976078387797403047}
noncomputable def t17 : RBox := {lo := -204088843569601381051700, hi := 204088843569601381051700}
noncomputable def t18 : RBox := {lo := -38716154189295730443609, hi := 38716154189295730443609}
noncomputable def t19 : RBox := {lo := -7124750292899887013175, hi := 7124750292899887013175}
noncomputable def t20 : RBox := {lo := -1271581096968907241704, hi := 1271581096968907241704}
noncomputable def t21 : RBox := {lo := -220016492512816141698, hi := 220016492512816141698}
noncomputable def t22 : RBox := {lo := -36894763818673297662, hi := 36894763818673297662}
noncomputable def t23 : RBox := {lo := -5995162925987219398, hi := 5995162925987219398}
noncomputable def t24 : RBox := {lo := -944017247492413777, hi := 944017247492413777}
noncomputable def t25 : RBox := {lo := -144081587984564201, hi := 144081587984564201}
noncomputable def t26 : RBox := {lo := -21324456348662756, hi := 21324456348662756}
noncomputable def t27 : RBox := {lo := -3062333875518606, hi := 3062333875518606}
noncomputable def t28 : RBox := {lo := -427027912874177, hi := 427027912874177}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N0_left
namespace N1_left
noncomputable def t0 : RBox := {lo := 24406391988011399658015545144, hi := 24406391988152941714119318691}
lemma t0_checked : ((hm15_1_0_2.realAnswer).add hm15_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := 20316729018770575605259697314, hi := 20316729018879942018383936446}
lemma t1_checked : ((hm15_1_0_3.realAnswer).add hm15_0_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -30477074893883036068806249346, hi := -30477074893818764621586298679}
lemma t2_checked : ((hm15_1_0_4.realAnswer).add hm15_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := -16123304431037692198535943297, hi := -16123304431007292529016651241}
lemma t3_checked : ((hm15_1_0_5.realAnswer).add hm15_0_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 16451406036103429258731105339, hi := 16451406036115451273310112625}
lemma t4_checked : ((hm15_1_0_6.realAnswer).add hm15_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := 3213537393089681631996482034, hi := 3213537393093766411913659683}
lemma t5_checked : ((hm15_1_0_7.realAnswer).add hm15_0_1_7.realAnswer).scale (-1) 1=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -3651909585057645575198504713, hi := -3651909585056428664707260099}
lemma t6_checked : ((hm15_1_0_8.realAnswer).add hm15_0_1_8.realAnswer).scale (1) 1=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := -282360212135947283204055498, hi := -282360212135624400993014522}
lemma t7_checked : ((hm15_1_0_9.realAnswer).add hm15_0_1_9.realAnswer).scale (-1) 1=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 435651358557732557914736809, hi := 435651358557809811778127914}
lemma t8_checked : ((hm15_1_0_10.realAnswer).add hm15_0_1_10.realAnswer).scale (1) 1=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 8905532033208330502442716, hi := 8905532033225168157198572}
lemma t9_checked : ((hm15_1_0_11.realAnswer).add hm15_0_1_11.realAnswer).scale (-1) 1=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := -31867091267435491299346323, hi := -31867091267432119847732998}
lemma t10_checked : ((hm15_1_0_12.realAnswer).add hm15_0_1_12.realAnswer).scale (1) 1=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -2173400331959384583868736519, hi := 2173400331959384583868736519}
noncomputable def t12 : RBox := {lo := -510676435717895794523285937, hi := 510676435717895794523285937}
noncomputable def t13 : RBox := {lo := -114781156209975071959800993, hi := 114781156209975071959800993}
noncomputable def t14 : RBox := {lo := -24801096061935672432257826, hi := 24801096061935672432257826}
noncomputable def t15 : RBox := {lo := -5171577702019867828849372, hi := 5171577702019867828849372}
noncomputable def t16 : RBox := {lo := -1043525976078387797403047, hi := 1043525976078387797403047}
noncomputable def t17 : RBox := {lo := -204088843569601381051700, hi := 204088843569601381051700}
noncomputable def t18 : RBox := {lo := -38716154189295730443609, hi := 38716154189295730443609}
noncomputable def t19 : RBox := {lo := -7124750292899887013175, hi := 7124750292899887013175}
noncomputable def t20 : RBox := {lo := -1271581096968907241704, hi := 1271581096968907241704}
noncomputable def t21 : RBox := {lo := -220016492512816141698, hi := 220016492512816141698}
noncomputable def t22 : RBox := {lo := -36894763818673297662, hi := 36894763818673297662}
noncomputable def t23 : RBox := {lo := -5995162925987219398, hi := 5995162925987219398}
noncomputable def t24 : RBox := {lo := -944017247492413777, hi := 944017247492413777}
noncomputable def t25 : RBox := {lo := -144081587984564201, hi := 144081587984564201}
noncomputable def t26 : RBox := {lo := -21324456348662756, hi := 21324456348662756}
noncomputable def t27 : RBox := {lo := -3062333875518606, hi := 3062333875518606}
noncomputable def t28 : RBox := {lo := -427027912874177, hi := 427027912874177}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_left
end SharpPlanar.Bernstein15

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock16_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm16_0_0_2
 def realAnswer : RBox := ⟨(-39108151862714672275080458040),(-39108151862542164239881162207)⟩
end hm16_0_0_2
namespace hm16_1_0_2
 def realAnswer : RBox := ⟨33273308506349113539460209656,33273308506490749108361652014⟩
end hm16_1_0_2
namespace hm16_0_0_3
 def realAnswer : RBox := ⟨(-111748310409133348704206418333),(-111748310409000049367577967430)⟩
end hm16_0_0_3
namespace hm16_1_0_3
 def realAnswer : RBox := ⟨99627215917892600421008553246,99627215918002038316326938716⟩
end hm16_1_0_3
namespace hm16_0_0_4
 def realAnswer : RBox := ⟨(-54032802668215622206380679708),(-54032802668137288507702649341)⟩
end hm16_0_0_4
namespace hm16_1_0_4
 def realAnswer : RBox := ⟨52202651704230293379975461591,52202651704294606047039474688⟩
end hm16_1_0_4
namespace hm16_0_0_5
 def realAnswer : RBox := ⟨46416345137438690671355222010,46416345137475739355696256905⟩
end hm16_0_0_5
namespace hm16_1_0_5
 def realAnswer : RBox := ⟨(-40481978938012348734618637510),(-40481978937981930183908654263)⟩
end hm16_1_0_5
namespace hm16_0_0_6
 def realAnswer : RBox := ⟨30705319851311005931015249506,30705319851325656229791653593⟩
end hm16_0_0_6
namespace hm16_1_0_6
 def realAnswer : RBox := ⟨(-29116391832868403440372294126),(-29116391832856374355509226674)⟩
end hm16_1_0_6
namespace hm16_0_0_7
 def realAnswer : RBox := ⟨(-8111277402674312070852339373),(-8111277402669334768560725297)⟩
end hm16_0_0_7
namespace hm16_1_0_7
 def realAnswer : RBox := ⟨6806629957145485978837984204,6806629957149572937900113482⟩
end hm16_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock16_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm16_0_0_8
 def realAnswer : RBox := ⟨(-6637718308027063158526800229),(-6637718308025580555646284824)⟩
end hm16_0_0_8
namespace hm16_1_0_8
 def realAnswer : RBox := ⟨6265912783814996326094910172,6265912783816213774365305615⟩
end hm16_1_0_8
namespace hm16_0_0_9
 def realAnswer : RBox := ⟨803813293551143076155661224,803813293551536376846069747⟩
end hm16_0_0_9
namespace hm16_1_0_9
 def realAnswer : RBox := ⟨(-632529025491936378667205715),(-632529025491613404072844083)⟩
end hm16_1_0_9
namespace hm16_0_0_10
 def realAnswer : RBox := ⟨809722739925447713262965027,809722739925541786766001650⟩
end hm16_0_0_10
namespace hm16_1_0_10
 def realAnswer : RBox := ⟨(-762891194565512719707881737),(-762891194565435464475701424)⟩
end hm16_1_0_10
namespace hm16_0_0_11
 def realAnswer : RBox := ⟨(-52221183719928337616444847),(-52221183719907844452680722)⟩
end hm16_0_0_11
namespace hm16_1_0_11
 def realAnswer : RBox := ⟨36982409158687032856203160,36982409158703862901171005⟩
end hm16_1_0_11
namespace hm16_0_0_12
 def realAnswer : RBox := ⟨(-64527162614230081959182760),(-64527162614225982196608455)⟩
end hm16_0_0_12
namespace hm16_1_0_12
 def realAnswer : RBox := ⟨60732269077394044931221207,60732269077397412003074194⟩
end hm16_1_0_12
namespace hm16_0_0_13
 def realAnswer : RBox := ⟨2453142311554788485915832,2453142311555547063998420⟩
end hm16_0_0_13
namespace hm16_1_0_13
 def realAnswer : RBox := ⟨(-1467008438300085247735866),(-1467008438299462193594619)⟩
end hm16_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock16_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm16_0_1_2
 def realAnswer : RBox := ⟨12854342221963685854369877755,12854342221963686386008797791⟩
end hm16_0_1_2
namespace hm16_1_1_2
 def realAnswer : RBox := ⟨(-11955177109782510104801803928),(-11955177109782509791149404345)⟩
end hm16_1_1_2
namespace hm16_0_1_3
 def realAnswer : RBox := ⟨(-674071430096950287613214112),(-674071430096949561141730787)⟩
end hm16_0_1_3
namespace hm16_1_1_3
 def realAnswer : RBox := ⟨2652482297270403800265773685,2652482297270404236341242495⟩
end hm16_1_1_3
namespace hm16_0_1_4
 def realAnswer : RBox := ⟨(-13955793312118830506827002922),(-13955793312118829762894178949)⟩
end hm16_0_1_4
namespace hm16_1_1_4
 def realAnswer : RBox := ⟨12796252347844152376355700389,12796252347844152831644920272⟩
end hm16_1_1_4
namespace hm16_0_1_5
 def realAnswer : RBox := ⟨1598211240521945396201323238,1598211240521946005100272371⟩
end hm16_0_1_5
namespace hm16_1_1_5
 def realAnswer : RBox := ⟨(-2718729722651728821214967711),(-2718729722651728441212052421)⟩
end hm16_1_1_5
namespace hm16_0_1_6
 def realAnswer : RBox := ⟨5976991707323418764101549597,5976991707323419179688932961⟩
end hm16_0_1_6
namespace hm16_1_1_6
 def realAnswer : RBox := ⟨(-5412474525274265236445723648),(-5412474525274264971614421737)⟩
end hm16_1_1_6
namespace hm16_0_1_7
 def realAnswer : RBox := ⟨(-851189483481400211837711816),(-851189483481399968614455541)⟩
end hm16_0_1_7
namespace hm16_1_1_7
 def realAnswer : RBox := ⟨1144802043188815002741600616,1144802043188815160975491677⟩
end hm16_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock16_11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm16_0_1_8
 def realAnswer : RBox := ⟨(-1351895772180970832842812101),(-1351895772180970708021257977)⟩
end hm16_0_1_8
namespace hm16_1_1_8
 def realAnswer : RBox := ⟨1210601825318114626821040542,1210601825318114709789287177⟩
end hm16_1_1_8
namespace hm16_0_1_9
 def realAnswer : RBox := ⟨216615779091078650561108364,216615779091078707634794953⟩
end hm16_0_1_9
namespace hm16_1_1_9
 def realAnswer : RBox := ⟨(-259947793109865055953429131),(-259947793109865017200556517)⟩
end hm16_1_1_9
namespace hm16_0_1_10
 def realAnswer : RBox := ⟨187423562076477235746383925,187423562076477259372523174⟩
end hm16_0_1_10
namespace hm16_1_1_10
 def realAnswer : RBox := ⟨(-166103073784242345787344682),(-166103073784242329381563005)⟩
end hm16_1_1_10
namespace hm16_0_1_11
 def realAnswer : RBox := ⟨(-32757910389516643343997313),(-32757910389516634354875218)⟩
end hm16_0_1_11
namespace hm16_1_1_11
 def realAnswer : RBox := ⟨36755909995355661353283149,36755909995355667750363204⟩
end hm16_1_1_11
namespace hm16_0_1_12
 def realAnswer : RBox := ⟨(-17430700609273909017285885),(-17430700609273905786109098)⟩
end hm16_0_1_12
namespace hm16_1_1_12
 def realAnswer : RBox := ⟨15292564068279723312906110,15292564068279725688905680⟩
end hm16_1_1_12
namespace hm16_0_1_13
 def realAnswer : RBox := ⟨3294767548405512822156179,3294767548405513989578885⟩
end hm16_0_1_13
namespace hm16_1_1_13
 def realAnswer : RBox := ⟨(-3538149074314556383693999),(-3538149074314555477816150)⟩
end hm16_1_1_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein16
open IntegerIntervals CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 51063328972324674031030566552, hi := 51063328972497182379882261968}
lemma t0_checked : ((hm16_0_0_2.realAnswer).add hm16_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := 163643742167594467696855087402, hi := 163643742167794417355910966972}
lemma t1_checked : ((hm16_0_0_3.realAnswer).add hm16_1_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := 92782238220659555271129890405, hi := 92782238220835807117556203468}
lemma t2_checked : ((hm16_0_0_4.realAnswer).add hm16_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := -147479452025031036836384190134, hi := -147479452024905996244223358259}
lemma t3_checked : ((hm16_0_0_5.realAnswer).add hm16_1_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := -128045029463135168244522236271, hi := -128045029463060999766258224656}
lemma t4_checked : ((hm16_0_0_6.realAnswer).add hm16_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := 52901672261055195770100367801, hi := 52901672261092993360965922436}
lemma t5_checked : ((hm16_0_0_7.realAnswer).add hm16_1_1_7.realAnswer).scale (-243) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := 61818248685839728150464863822, hi := 61818248685856616868960918935}
lemma t6_checked : ((hm16_0_0_8.realAnswer).add hm16_1_1_8.realAnswer).scale (-729) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := -9292451948952619246443261204, hi := -9292451948945898673299074901}
lemma t7_checked : ((hm16_0_0_9.realAnswer).add hm16_1_1_9.realAnswer).scale (-2187) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := -16495268084191663046481648242, hi := -16495268084189251625029472982}
lemma t8_checked : ((hm16_0_0_10.realAnswer).add hm16_1_1_10.realAnswer).scale (-6561) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 594537075625704089905694739, hi := 594537075626492161890257230}
lemma t9_checked : ((hm16_0_0_11.realAnswer).add hm16_1_1_11.realAnswer).scale (-19683) 512=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := 2839115048378496582542325352, hi := 2839115048378733132523427643}
lemma t10_checked : ((hm16_0_0_12.realAnswer).add hm16_1_1_12.realAnswer).scale (-59049) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := 93850436036362335684848347, hi := 93850436036428029193217261}
lemma t11_checked : ((hm16_0_0_13.realAnswer).add hm16_1_1_13.realAnswer).scale (-177147) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -61839186594498546985068715579, hi := 61839186594498546985068715579}
noncomputable def t13 : RBox := {lo := -20500998507632111319484518539, hi := 20500998507632111319484518539}
noncomputable def t14 : RBox := {lo := -6523208948461922490851005092, hi := 6523208948461922490851005092}
noncomputable def t15 : RBox := {lo := -2001108592322595368095247195, hi := 2001108592322595368095247195}
noncomputable def t16 : RBox := {lo := -593882974596011604139733432, hi := 593882974596011604139733432}
noncomputable def t17 : RBox := {lo := -170914791314823074313359263, hi := 170914791314823074313359263}
noncomputable def t18 : RBox := {lo := -47763463222836881166984422, hi := 47763463222836881166984422}
noncomputable def t19 : RBox := {lo := -12968152058503371238596043, hi := 12968152058503371238596043}
noncomputable def t20 : RBox := {lo := -3420604834478252576726273, hi := 3420604834478252576726273}
noncomputable def t21 : RBox := {lo := -876206515302459865725797, hi := 876206515302459865725797}
noncomputable def t22 : RBox := {lo := -217861827796249410693090, hi := 217861827796249410693090}
noncomputable def t23 : RBox := {lo := -52558745128403565729773, hi := 52558745128403565729773}
noncomputable def t24 : RBox := {lo := -12299393946913104075874, hi := 12299393946913104075874}
noncomputable def t25 : RBox := {lo := -2791704545697118689729, hi := 2791704545697118689729}
noncomputable def t26 : RBox := {lo := -614700496900798892964, hi := 614700496900798892964}
noncomputable def t27 : RBox := {lo := -131343900200550587389, hi := 131343900200550587389}
noncomputable def t28 : RBox := {lo := -27247313584658673303, hi := 27247313584658673303}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N0_right
namespace N1_right
noncomputable def t0 : RBox := {lo := 46127650728312799393830087411, hi := 46127650728454435494370449805}
lemma t0_checked : ((hm16_1_0_2.realAnswer).add hm16_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := 148429716731693475200093008701, hi := 148429716731857633132777811894}
lemma t1_checked : ((hm16_1_0_3.realAnswer).add hm16_0_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := 86055431382250791464584032005, hi := 86055431382395496639326915413}
lemma t2_checked : ((hm16_1_0_4.realAnswer).add hm16_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := -131232715979030111267158435668, hi := -131232715978927446603478288885}
lemma t3_checked : ((hm16_1_0_5.realAnswer).add hm16_0_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := -117143213135571484923620644179, hi := -117143213135510585577590236922}
lemma t4_checked : ((hm16_1_0_6.realAnswer).add hm16_0_1_6.realAnswer).scale (81) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := 45224126096886651293158318446, hi := 45224126096917688485512964990}
lemma t5_checked : ((hm16_1_0_7.realAnswer).add hm16_0_1_7.realAnswer).scale (243) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := 55973725023143821634074679589, hi := 55973725023157690552575167627}
lemma t6_checked : ((hm16_1_0_8.realAnswer).add hm16_0_1_8.realAnswer).scale (729) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := -7106267733427155088812772709, hi := -7106267733421635789921980057}
lemma t7_checked : ((hm16_1_0_9.realAnswer).add hm16_0_1_9.realAnswer).scale (2187) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := -14748606002970944571372606034, hi := -14748606002968963998757626946}
lemma t8_checked : ((hm16_1_0_10.realAnswer).add hm16_0_1_10.realAnswer).scale (6561) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 162403924362462454626460325, hi := 162403924363109803665507765}
lemma t9_checked : ((hm16_1_0_11.realAnswer).add hm16_0_1_11.realAnswer).scale (19683) 512=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := 2496986637181665923419889481, hi := 2496986637181860272075753862}
lemma t10_checked : ((hm16_1_0_12.realAnswer).add hm16_0_1_12.realAnswer).scale (59049) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := 158096700721604579358317962, hi := 158096700721658572999621470}
lemma t11_checked : ((hm16_1_0_13.realAnswer).add hm16_0_1_13.realAnswer).scale (177147) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -61839186594498546985068715579, hi := 61839186594498546985068715579}
noncomputable def t13 : RBox := {lo := -20500998507632111319484518539, hi := 20500998507632111319484518539}
noncomputable def t14 : RBox := {lo := -6523208948461922490851005092, hi := 6523208948461922490851005092}
noncomputable def t15 : RBox := {lo := -2001108592322595368095247195, hi := 2001108592322595368095247195}
noncomputable def t16 : RBox := {lo := -593882974596011604139733432, hi := 593882974596011604139733432}
noncomputable def t17 : RBox := {lo := -170914791314823074313359263, hi := 170914791314823074313359263}
noncomputable def t18 : RBox := {lo := -47763463222836881166984422, hi := 47763463222836881166984422}
noncomputable def t19 : RBox := {lo := -12968152058503371238596043, hi := 12968152058503371238596043}
noncomputable def t20 : RBox := {lo := -3420604834478252576726273, hi := 3420604834478252576726273}
noncomputable def t21 : RBox := {lo := -876206515302459865725797, hi := 876206515302459865725797}
noncomputable def t22 : RBox := {lo := -217861827796249410693090, hi := 217861827796249410693090}
noncomputable def t23 : RBox := {lo := -52558745128403565729773, hi := 52558745128403565729773}
noncomputable def t24 : RBox := {lo := -12299393946913104075874, hi := 12299393946913104075874}
noncomputable def t25 : RBox := {lo := -2791704545697118689729, hi := 2791704545697118689729}
noncomputable def t26 : RBox := {lo := -614700496900798892964, hi := 614700496900798892964}
noncomputable def t27 : RBox := {lo := -131343900200550587389, hi := 131343900200550587389}
noncomputable def t28 : RBox := {lo := -27247313584658673303, hi := 27247313584658673303}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_right
namespace N0_left
noncomputable def t0 : RBox := {lo := 51063328972324674031030566552, hi := 51063328972497182379882261968}
lemma t0_checked : ((hm16_0_0_2.realAnswer).add hm16_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -54547914055931472451970322324, hi := -54547914055864822565618362467}
lemma t1_checked : ((hm16_0_0_3.realAnswer).add hm16_1_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := 10309137580073283919014432267, hi := 10309137580092867457506244830}
lemma t2_checked : ((hm16_0_0_4.realAnswer).add hm16_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 5462201926848370231267531787, hi := 5462201926853001364310525561}
lemma t3_checked : ((hm16_0_0_5.realAnswer).add hm16_1_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := -1580802832878211953636076991, hi := -1580802832877296293410595366}
lemma t4_checked : ((hm16_0_0_6.realAnswer).add hm16_1_1_6.realAnswer).scale (-1) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := -217702354983921783378460587, hi := -217702354983766237737038550}
lemma t5_checked : ((hm16_0_0_7.realAnswer).add hm16_1_1_7.realAnswer).scale (1) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := 84798695042304153841515588, hi := 84798695042327320807902496}
lemma t6_checked : ((hm16_0_0_8.realAnswer).add hm16_1_1_8.realAnswer).scale (-1) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 4248949222197484532829938, hi := 4248949222200557497230573}
lemma t7_checked : ((hm16_0_0_9.realAnswer).add hm16_1_1_9.realAnswer).scale (1) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := -2514139320864451005407964, hi := -2514139320864083466701641}
lemma t8_checked : ((hm16_0_0_10.realAnswer).add hm16_1_1_10.realAnswer).scale (-1) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := -30205612743306008326488, hi := -30205612743265970121713}
lemma t9_checked : ((hm16_0_0_11.realAnswer).add hm16_1_1_11.realAnswer).scale (1) 512=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := 48080662642525641120803, hi := 48080662642529647115505}
lemma t10_checked : ((hm16_0_0_12.realAnswer).add hm16_1_1_12.realAnswer).scale (-1) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -529788458378792918837, hi := -529788458378422077059}
lemma t11_checked : ((hm16_0_0_13.realAnswer).add hm16_1_1_13.realAnswer).scale (1) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -116361339442193107014831, hi := 116361339442193107014831}
noncomputable def t13 : RBox := {lo := -12858748514342521132471, hi := 12858748514342521132471}
noncomputable def t14 : RBox := {lo := -1363840942406677210505, hi := 1363840942406677210505}
noncomputable def t15 : RBox := {lo := -139460698457561636444, hi := 139460698457561636444}
noncomputable def t16 : RBox := {lo := -13796241869293868031, hi := 13796241869293868031}
noncomputable def t17 : RBox := {lo := -1323482852618229035, hi := 1323482852618229035}
noncomputable def t18 : RBox := {lo := -123285847235706941, hi := 123285847235706941}
noncomputable def t19 : RBox := {lo := -11157689062837503, hi := 11157689062837503}
noncomputable def t20 : RBox := {lo := -981019885685285, hi := 981019885685285}
noncomputable def t21 : RBox := {lo := -83764524801244, hi := 83764524801244}
noncomputable def t22 : RBox := {lo := -6942462444250, hi := 6942462444250}
noncomputable def t23 : RBox := {lo := -558285218147, hi := 558285218147}
noncomputable def t24 : RBox := {lo := -43548539931, hi := 43548539931}
noncomputable def t25 : RBox := {lo := -3294868496, hi := 3294868496}
noncomputable def t26 : RBox := {lo := -241830427, hi := 241830427}
noncomputable def t27 : RBox := {lo := -17224080, hi := 17224080}
noncomputable def t28 : RBox := {lo := -1191047, hi := 1191047}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N0_left
namespace N1_left
noncomputable def t0 : RBox := {lo := 46127650728312799393830087411, hi := 46127650728454435494370449805}
lemma t0_checked : ((hm16_1_0_2.realAnswer).add hm16_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -49476572243952544377592603965, hi := -49476572243897825066697669567}
lemma t1_checked : ((hm16_1_0_3.realAnswer).add hm16_0_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := 9561714598027865718287114667, hi := 9561714598043944071036323935}
lemma t2_checked : ((hm16_1_0_4.realAnswer).add hm16_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 4860470962182498022351047736, hi := 4860470962186300417302164284}
lemma t3_checked : ((hm16_1_0_5.realAnswer).add hm16_0_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := -1446212507846561542266921534, hi := -1446212507845809698488768357}
lemma t4_checked : ((hm16_1_0_6.realAnswer).add hm16_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := -186107514802130405290176811, hi := -186107514802002680218758512}
lemma t5_checked : ((hm16_1_0_7.realAnswer).add hm16_0_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := 76781515806781648332064032, hi := 76781515806800672911625745}
lemma t6_checked : ((hm16_1_0_8.realAnswer).add hm16_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 3249322237504177315922258, hi := 3249322237506701000828886}
lemma t7_checked : ((hm16_1_0_9.realAnswer).add hm16_0_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := -2247920439410294859224601, hi := -2247920439409992988684290}
lemma t8_checked : ((hm16_1_0_10.realAnswer).add hm16_0_1_10.realAnswer).scale (1) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := -8250974158568805754484, hi := -8250974158535917016027}
lemma t9_checked : ((hm16_1_0_11.realAnswer).add hm16_0_1_11.realAnswer).scale (-1) 512=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := 42286687957148570228452, hi := 42286687957151861540005}
lemma t10_checked : ((hm16_1_0_12.realAnswer).add hm16_0_1_12.realAnswer).scale (1) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -892460502981470603508, hi := -892460502981165807822}
lemma t11_checked : ((hm16_1_0_13.realAnswer).add hm16_0_1_13.realAnswer).scale (-1) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -116361339442193107014831, hi := 116361339442193107014831}
noncomputable def t13 : RBox := {lo := -12858748514342521132471, hi := 12858748514342521132471}
noncomputable def t14 : RBox := {lo := -1363840942406677210505, hi := 1363840942406677210505}
noncomputable def t15 : RBox := {lo := -139460698457561636444, hi := 139460698457561636444}
noncomputable def t16 : RBox := {lo := -13796241869293868031, hi := 13796241869293868031}
noncomputable def t17 : RBox := {lo := -1323482852618229035, hi := 1323482852618229035}
noncomputable def t18 : RBox := {lo := -123285847235706941, hi := 123285847235706941}
noncomputable def t19 : RBox := {lo := -11157689062837503, hi := 11157689062837503}
noncomputable def t20 : RBox := {lo := -981019885685285, hi := 981019885685285}
noncomputable def t21 : RBox := {lo := -83764524801244, hi := 83764524801244}
noncomputable def t22 : RBox := {lo := -6942462444250, hi := 6942462444250}
noncomputable def t23 : RBox := {lo := -558285218147, hi := 558285218147}
noncomputable def t24 : RBox := {lo := -43548539931, hi := 43548539931}
noncomputable def t25 : RBox := {lo := -3294868496, hi := 3294868496}
noncomputable def t26 : RBox := {lo := -241830427, hi := 241830427}
noncomputable def t27 : RBox := {lo := -17224080, hi := 17224080}
noncomputable def t28 : RBox := {lo := -1191047, hi := 1191047}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_left
end SharpPlanar.Bernstein16

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock19_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm19_0_0_2
 def realAnswer : RBox := ⟨(-418211711642572335327317318122),(-418211711642399848167095728165)⟩
end hm19_0_0_2
namespace hm19_1_0_2
 def realAnswer : RBox := ⟨393673690332384813448622257830,393673690332526408693830320114⟩
end hm19_1_0_2
namespace hm19_0_0_3
 def realAnswer : RBox := ⟨90012907393916898153019372625,90012907394050178901825543866⟩
end hm19_0_0_3
namespace hm19_1_0_3
 def realAnswer : RBox := ⟨(-79786998738870458109857318319),(-79786998738761051570783894194)⟩
end hm19_1_0_3
namespace hm19_0_0_4
 def realAnswer : RBox := ⟨272574203064866024595321439111,272574203064944346941362886260⟩
end hm19_0_0_4
namespace hm19_1_0_4
 def realAnswer : RBox := ⟨(-258093029408487832422881496981),(-258093029408423538124027278008)⟩
end hm19_1_0_4
namespace hm19_0_0_5
 def realAnswer : RBox := ⟨(-37363894037392341543012641718),(-37363894037355298200131460322)⟩
end hm19_0_0_5
namespace hm19_1_0_5
 def realAnswer : RBox := ⟨32056864681612366123335117871,32056864681642776082442365838⟩
end hm19_1_0_5
namespace hm19_0_0_6
 def realAnswer : RBox := ⟨(-75710610038094048389185220012),(-75710610038079400127840290099)⟩
end hm19_0_0_6
namespace hm19_1_0_6
 def realAnswer : RBox := ⟨71979685264267069730136912378,71979685264279095474110744791⟩
end hm19_1_0_6
namespace hm19_0_0_7
 def realAnswer : RBox := ⟨6148503759342565387373261423,6148503759347542036190951792⟩
end hm19_0_0_7
namespace hm19_1_0_7
 def realAnswer : RBox := ⟨(-4955097436552370480860943810),(-4955097436548284630559912068)⟩
end hm19_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock19_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm19_0_0_8
 def realAnswer : RBox := ⟨11770849022536977137807765572,11770849022538459561992304330⟩
end hm19_0_0_8
namespace hm19_1_0_8
 def realAnswer : RBox := ⟨(-11218878401243232946473923956),(-11218878401242015819124060805)⟩
end hm19_1_0_8
namespace hm19_0_0_9
 def realAnswer : RBox := ⟨(-576560791570139248133867695),(-576560791569745989806665711)⟩
end hm19_0_0_9
namespace hm19_1_0_9
 def realAnswer : RBox := ⟨417702961260475864870470573,417702961260798757342161155⟩
end hm19_1_0_9
namespace hm19_0_0_10
 def realAnswer : RBox := ⟨(-1176449074813062079376559066),(-1176449074812968014529195419)⟩
end hm19_0_0_10
namespace hm19_1_0_10
 def realAnswer : RBox := ⟨1123282313632132547135345744,1123282313632209783534510800⟩
end hm19_1_0_10
namespace hm19_0_0_11
 def realAnswer : RBox := ⟨36168962907389394570550064,36168962907409886211893494⟩
end hm19_0_0_11
namespace hm19_1_0_11
 def realAnswer : RBox := ⟨(-21943143587009057464322489),(-21943143586992231317283470)⟩
end hm19_1_0_11
namespace hm19_0_0_12
 def realAnswer : RBox := ⟨82195789257902807832219899,82195789257906907375694654⟩
end hm19_0_0_12
namespace hm19_1_0_12
 def realAnswer : RBox := ⟨(-78599927499845018612612724),(-78599927499841652275722864)⟩
end hm19_1_0_12
namespace hm19_0_0_13
 def realAnswer : RBox := ⟨(-1675312502259518576454510),(-1675312502258760021440502)⟩
end hm19_0_0_13
namespace hm19_1_0_13
 def realAnswer : RBox := ⟨755814041261783832876607,755814041262406760452945⟩
end hm19_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock19_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm19_0_1_2
 def realAnswer : RBox := ⟨(-1174254333827126792921574653),(-1174254333827126532080895937)⟩
end hm19_0_1_2
namespace hm19_1_1_2
 def realAnswer : RBox := ⟨170088134389376308467642415,170088134389376380087849506⟩
end hm19_1_1_2
namespace hm19_0_1_3
 def realAnswer : RBox := ⟨8333978897035344994416667350,8333978897035345336387312663⟩
end hm19_0_1_3
namespace hm19_1_1_3
 def realAnswer : RBox := ⟨(-8201208471614204411661847408),(-8201208471614204315703705925)⟩
end hm19_1_1_3
namespace hm19_0_1_4
 def realAnswer : RBox := ⟨437517012954251723301512232,437517012954252057800766799⟩
end hm19_0_1_4
namespace hm19_1_1_4
 def realAnswer : RBox := ⟨594297448450700578129161256,594297448450700674217533773⟩
end hm19_1_1_4
namespace hm19_0_1_5
 def realAnswer : RBox := ⟨(-5491719520114719165322492600),(-5491719520114718904762824753)⟩
end hm19_0_1_5
namespace hm19_1_1_5
 def realAnswer : RBox := ⟨5320764408082609339376897222,5320764408082609416370989338⟩
end hm19_1_1_5
namespace hm19_0_1_6
 def realAnswer : RBox := ⟨179866039632845191393684575,179866039632845359784615979⟩
end hm19_0_1_6
namespace hm19_1_1_6
 def realAnswer : RBox := ⟨(-596921136904036183254803045),(-596921136904036132012032241)⟩
end hm19_1_1_6
namespace hm19_0_1_7
 def realAnswer : RBox := ⟨1701002529493489556631933493,1701002529493489649640504881⟩
end hm19_0_1_7
namespace hm19_1_1_7
 def realAnswer : RBox := ⟨(-1625090846885190552911203820),(-1625090846885190523593895615)⟩
end hm19_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock19_11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm19_0_1_8
 def realAnswer : RBox := ⟨(-128147057805038848356743782),(-128147057805038803521072830)⟩
end hm19_0_1_8
namespace hm19_1_1_8
 def realAnswer : RBox := ⟨216913903669059044128403629,216913903669059058813929729⟩
end hm19_1_1_8
namespace hm19_0_1_9
 def realAnswer : RBox := ⟨(-303329145331693410846886809),(-303329145331693391608443886)⟩
end hm19_0_1_9
namespace hm19_1_1_9
 def realAnswer : RBox := ⟨286086549544392342147001774,286086549544392348769212329⟩
end hm19_1_1_9
namespace hm19_0_1_10
 def realAnswer : RBox := ⟨30905466266380620907058845,30905466266380628394418285⟩
end hm19_0_1_10
namespace hm19_1_1_10
 def realAnswer : RBox := ⟨(-42449614028963712428750147),(-42449614028963709671361506)⟩
end hm19_1_1_10
namespace hm19_0_1_11
 def realAnswer : RBox := ⟨34926274368096169405132574,34926274368096172139671129⟩
end hm19_0_1_11
namespace hm19_1_1_11
 def realAnswer : RBox := ⟨(-32545469287847945893339293),(-32545469287847944763562980)⟩
end hm19_1_1_11
namespace hm19_0_1_12
 def realAnswer : RBox := ⟨(-4239123975083248229512410),(-4239123975083247221787996)⟩
end hm19_0_1_12
namespace hm19_1_1_12
 def realAnswer : RBox := ⟨5242673494950962753490819,5242673494950963263609288⟩
end hm19_1_1_12
namespace hm19_0_1_13
 def realAnswer : RBox := ⟨(-2794948343610622646097585),(-2794948343610622207930838)⟩
end hm19_0_1_13
namespace hm19_1_1_13
 def realAnswer : RBox := ⟨2574202367680013301534660,2574202367680013597600573⟩
end hm19_1_1_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein19
open IntegerIntervals CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 418041623508010471787007878659, hi := 418041623508182959018849675707}
lemma t0_checked : ((hm19_0_0_2.realAnswer).add hm19_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -81811698922435974586121837941, hi := -81811698922302693741357525217}
lemma t1_checked : ((hm19_0_0_3.realAnswer).add hm19_1_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -273168500513395047615580420033, hi := -273168500513316725173450600367}
lemma t2_checked : ((hm19_0_0_4.realAnswer).add hm19_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 32043129629272688783760470984, hi := 32043129629309732203635744496}
lemma t3_checked : ((hm19_0_0_5.realAnswer).add hm19_1_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 76307531174983436259852322340, hi := 76307531174998084572440023057}
lemma t4_checked : ((hm19_0_0_6.realAnswer).add hm19_1_1_6.realAnswer).scale (-1) 1=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := -4523412912462351512597056177, hi := -4523412912457374834462057603}
lemma t5_checked : ((hm19_0_0_7.realAnswer).add hm19_1_1_7.realAnswer).scale (-1) 1=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -11987762926207518620806234059, hi := -11987762926206036181936169201}
lemma t6_checked : ((hm19_0_0_8.realAnswer).add hm19_1_1_8.realAnswer).scale (-1) 1=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 290474242025353641037453382, hi := 290474242025746905986865921}
lemma t7_checked : ((hm19_0_0_9.realAnswer).add hm19_1_1_9.realAnswer).scale (-1) 1=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 1218898688841931724200556925, hi := 1218898688842025791805309213}
lemma t8_checked : ((hm19_0_0_10.realAnswer).add hm19_1_1_10.realAnswer).scale (-1) 1=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := -3623493619561941448330514, hi := -3623493619541448677210771}
lemma t9_checked : ((hm19_0_0_11.realAnswer).add hm19_1_1_11.realAnswer).scale (-1) 1=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := -87438462752857870639303942, hi := -87438462752853770585710718}
lemma t10_checked : ((hm19_0_0_12.realAnswer).add hm19_1_1_12.realAnswer).scale (-1) 1=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -898889865421253576160071, hi := -898889865420494725080150}
lemma t11_checked : ((hm19_0_0_13.realAnswer).add hm19_1_1_13.realAnswer).scale (-1) 1=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -415519823301646288216618079, hi := 415519823301646288216618079}
noncomputable def t13 : RBox := {lo := -88441022552632104701542875, hi := 88441022552632104701542875}
noncomputable def t14 : RBox := {lo := -17961769109023805605644033, hi := 17961769109023805605644033}
noncomputable def t15 : RBox := {lo := -3499152986883578905581056, hi := 3499152986883578905581056}
noncomputable def t16 : RBox := {lo := -657025204371517831247787, hi := 657025204371517831247787}
noncomputable def t17 : RBox := {lo := -119404930671123464551117, hi := 119404930671123464551117}
noncomputable def t18 : RBox := {lo := -21074327843674396260647, hi := 21074327843674396260647}
noncomputable def t19 : RBox := {lo := -3621158106959460131472, hi := 3621158106959460131472}
noncomputable def t20 : RBox := {lo := -606685585115109330584, hi := 606685585115109330584}
noncomputable def t21 : RBox := {lo := -99171959366183814819, hi := 99171959366183814819}
noncomputable def t22 : RBox := {lo := -15816651699858251513, hi := 15816651699858251513}
noncomputable def t23 : RBox := {lo := -2460008358849052878, hi := 2460008358849052878}
noncomputable def t24 : RBox := {lo := -372867321116342342, hi := 372867321116342342}
noncomputable def t25 : RBox := {lo := -55036650600723914, hi := 55036650600723914}
noncomputable def t26 : RBox := {lo := -7905972890555824, hi := 7905972890555824}
noncomputable def t27 : RBox := {lo := -1104748937734647, hi := 1104748937734647}
noncomputable def t28 : RBox := {lo := -150128174659659, hi := 150128174659659}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N0_right
namespace N1_right
noncomputable def t0 : RBox := {lo := 392499435998557686655700683177, hi := 392499435998699282161749424177}
lemma t0_checked : ((hm19_1_0_2.realAnswer).add hm19_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -71453019841835113115440650969, hi := -71453019841725706234396581531}
lemma t1_checked : ((hm19_1_0_3.realAnswer).add hm19_0_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -257655512395533580699579984749, hi := -257655512395469286066226511209}
lemma t2_checked : ((hm19_1_0_4.realAnswer).add hm19_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 26565145161497646958012625271, hi := 26565145161528057177679541085}
lemma t3_checked : ((hm19_1_0_5.realAnswer).add hm19_0_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 72159551303899914921530596953, hi := 72159551303911940833895360770}
lemma t4_checked : ((hm19_1_0_6.realAnswer).add hm19_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := -3254094907058880924229010317, hi := -3254094907054794980919407187}
lemma t5_checked : ((hm19_1_0_7.realAnswer).add hm19_0_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -11347025459048271794830667738, hi := -11347025459047054622645133635}
lemma t6_checked : ((hm19_1_0_8.realAnswer).add hm19_0_1_8.realAnswer).scale (1) 1=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 114373815928782454023583764, hi := 114373815929105365733717269}
lemma t7_checked : ((hm19_1_0_9.realAnswer).add hm19_0_1_9.realAnswer).scale (1) 1=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 1154187779898513168042404589, hi := 1154187779898590411928929085}
lemma t8_checked : ((hm19_1_0_10.realAnswer).add hm19_0_1_10.realAnswer).scale (1) 1=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 12983130781087111940810085, hi := 12983130781103940822387659}
lemma t9_checked : ((hm19_1_0_11.realAnswer).add hm19_0_1_11.realAnswer).scale (1) 1=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := -82839051474928266842125134, hi := -82839051474924899497510860}
lemma t10_checked : ((hm19_1_0_12.realAnswer).add hm19_0_1_12.realAnswer).scale (1) 1=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -2039134302348838813220978, hi := -2039134302348215447477893}
lemma t11_checked : ((hm19_1_0_13.realAnswer).add hm19_0_1_13.realAnswer).scale (1) 1=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -415519823301646288216618079, hi := 415519823301646288216618079}
noncomputable def t13 : RBox := {lo := -88441022552632104701542875, hi := 88441022552632104701542875}
noncomputable def t14 : RBox := {lo := -17961769109023805605644033, hi := 17961769109023805605644033}
noncomputable def t15 : RBox := {lo := -3499152986883578905581056, hi := 3499152986883578905581056}
noncomputable def t16 : RBox := {lo := -657025204371517831247787, hi := 657025204371517831247787}
noncomputable def t17 : RBox := {lo := -119404930671123464551117, hi := 119404930671123464551117}
noncomputable def t18 : RBox := {lo := -21074327843674396260647, hi := 21074327843674396260647}
noncomputable def t19 : RBox := {lo := -3621158106959460131472, hi := 3621158106959460131472}
noncomputable def t20 : RBox := {lo := -606685585115109330584, hi := 606685585115109330584}
noncomputable def t21 : RBox := {lo := -99171959366183814819, hi := 99171959366183814819}
noncomputable def t22 : RBox := {lo := -15816651699858251513, hi := 15816651699858251513}
noncomputable def t23 : RBox := {lo := -2460008358849052878, hi := 2460008358849052878}
noncomputable def t24 : RBox := {lo := -372867321116342342, hi := 372867321116342342}
noncomputable def t25 : RBox := {lo := -55036650600723914, hi := 55036650600723914}
noncomputable def t26 : RBox := {lo := -7905972890555824, hi := 7905972890555824}
noncomputable def t27 : RBox := {lo := -1104748937734647, hi := 1104748937734647}
noncomputable def t28 : RBox := {lo := -150128174659659, hi := 150128174659659}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_right
namespace N0_left
noncomputable def t0 : RBox := {lo := 418041623508010471787007878659, hi := 418041623508182959018849675707}
lemma t0_checked : ((hm19_0_0_2.realAnswer).add hm19_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := 122717548383454040612036287825, hi := 122717548383653961879182756912}
lemma t1_checked : ((hm19_0_0_3.realAnswer).add hm19_1_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -614629126155138857135055945075, hi := -614629126154962631640263850825}
lemma t2_checked : ((hm19_0_0_4.realAnswer).add hm19_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := -108145562498920346187270637674, hi := -108145562498795324645191589571}
lemma t3_checked : ((hm19_0_0_5.realAnswer).add hm19_1_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 386306876573353646065502381846, hi := 386306876573427803147977616727}
lemma t4_checked : ((hm19_0_0_6.realAnswer).add hm19_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := 34349666803973190149196249922, hi := 34349666804010981798783895345}
lemma t5_checked : ((hm19_0_0_7.realAnswer).add hm19_1_1_7.realAnswer).scale (243) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -136548112081332516790121009829, hi := -136548112081315630884866677305}
lemma t6_checked : ((hm19_0_0_8.realAnswer).add hm19_1_1_8.realAnswer).scale (-729) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := -4963024744611785026509966948, hi := -4963024744605065726163363644}
lemma t7_checked : ((hm19_0_0_9.realAnswer).add hm19_1_1_9.realAnswer).scale (2187) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 31239040224577789228436929628, hi := 31239040224580200078260288073}
lemma t8_checked : ((hm19_0_0_10.realAnswer).add hm19_1_1_10.realAnswer).scale (-6561) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 139299267409051434206132042, hi := 139299267409839245170877944}
lemma t9_checked : ((hm19_0_0_11.realAnswer).add hm19_1_1_11.realAnswer).scale (19683) 512=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := -5042142370208500393926033664, hi := -5042142370208263964175422057}
lemma t10_checked : ((hm19_0_0_12.realAnswer).add hm19_1_1_12.realAnswer).scale (-59049) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := 77751778803537294464733072, hi := 77751778803602933230482470}
lemma t11_checked : ((hm19_0_0_13.realAnswer).add hm19_1_1_13.realAnswer).scale (177147) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -53912175394348194593781183722, hi := 53912175394348194593781183722}
noncomputable def t13 : RBox := {lo := -17212348193259286506845451795, hi := 17212348193259286506845451795}
noncomputable def t14 : RBox := {lo := -5243565968848784330677590020, hi := 5243565968848784330677590020}
noncomputable def t15 : RBox := {lo := -1532257714464254563700694382, hi := 1532257714464254563700694382}
noncomputable def t16 : RBox := {lo := -431560984230784735538460829, hi := 431560984230784735538460829}
noncomputable def t17 : RBox := {lo := -117645051650028866617248316, hi := 117645051650028866617248316}
noncomputable def t18 : RBox := {lo := -31145577997370339035337953, hi := 31145577997370339035337953}
noncomputable def t19 : RBox := {lo := -8027520243899622043481178, hi := 8027520243899622043481178}
noncomputable def t20 : RBox := {lo := -2017385324946328166284412, hi := 2017385324946328166284412}
noncomputable def t21 : RBox := {lo := -494658337976382597555488, hi := 494658337976382597555488}
noncomputable def t22 : RBox := {lo := -118337461902628652472489, hi := 118337461902628652472489}
noncomputable def t23 : RBox := {lo := -27608037810688158630507, hi := 27608037810688158630507}
noncomputable def t24 : RBox := {lo := -6276890317904993958782, hi := 6276890317904993958782}
noncomputable def t25 : RBox := {lo := -1389739726659286490149, hi := 1389739726659286490149}
noncomputable def t26 : RBox := {lo := -299452577981342345968, hi := 299452577981342345968}
noncomputable def t27 : RBox := {lo := -62766453036154687587, hi := 62766453036154687587}
noncomputable def t28 : RBox := {lo := -12794327338528462519, hi := 12794327338528462519}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N0_left
namespace N1_left
noncomputable def t0 : RBox := {lo := 392499435998557686655700683177, hi := 392499435998699282161749424177}
lemma t0_checked : ((hm19_1_0_2.realAnswer).add hm19_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := 107179529762588559351594872296, hi := 107179529762752669673160976454}
lemma t1_checked : ((hm19_1_0_3.realAnswer).add hm19_0_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -579724902889950556574054965686, hi := -579724902889805893649009650220}
lemma t2_checked : ((hm19_1_0_4.realAnswer).add hm19_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := -89657364920157192974668451162, hi := -89657364920054558483292610289}
lemma t3_checked : ((hm19_1_0_5.realAnswer).add hm19_0_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 365307728475993319290248647074, hi := 365307728476054200471595263899}
lemma t4_checked : ((hm19_1_0_6.realAnswer).add hm19_0_1_6.realAnswer).scale (81) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := 24710783200447349386356748326, hi := 24710783200478377018364047095}
lemma t5_checked : ((hm19_1_0_7.realAnswer).add hm19_0_1_7.realAnswer).scale (-243) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -129249711869471720912993074704, hi := -129249711869457856561067225311}
lemma t6_checked : ((hm19_1_0_8.realAnswer).add hm19_0_1_8.realAnswer).scale (729) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := -1954183870601198709840934901, hi := -1954183870595681460543575717}
lemma t7_checked : ((hm19_1_0_9.realAnswer).add hm19_0_1_9.realAnswer).scale (-2187) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 29580570405914628498149283236, hi := 29580570405916608174475405183}
lemma t8_checked : ((hm19_1_0_10.realAnswer).add hm19_0_1_10.realAnswer).scale (6561) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := -499115162430603256263781821, hi := -499115162429956297521415826}
lemma t9_checked : ((hm19_1_0_11.realAnswer).add hm19_0_1_11.realAnswer).scale (-19683) 512=t9 := by decide +kernel
noncomputable def t10 : RBox := {lo := -4776917139202186746836569373, hi := -4776917139201992568777850363}
lemma t10_checked : ((hm19_1_0_12.realAnswer).add hm19_0_1_12.realAnswer).scale (59049) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := 176380138797890293883967925, hi := 176380138797944213498855757}
lemma t11_checked : ((hm19_1_0_13.realAnswer).add hm19_0_1_13.realAnswer).scale (-177147) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -53912175394348194593781183722, hi := 53912175394348194593781183722}
noncomputable def t13 : RBox := {lo := -17212348193259286506845451795, hi := 17212348193259286506845451795}
noncomputable def t14 : RBox := {lo := -5243565968848784330677590020, hi := 5243565968848784330677590020}
noncomputable def t15 : RBox := {lo := -1532257714464254563700694382, hi := 1532257714464254563700694382}
noncomputable def t16 : RBox := {lo := -431560984230784735538460829, hi := 431560984230784735538460829}
noncomputable def t17 : RBox := {lo := -117645051650028866617248316, hi := 117645051650028866617248316}
noncomputable def t18 : RBox := {lo := -31145577997370339035337953, hi := 31145577997370339035337953}
noncomputable def t19 : RBox := {lo := -8027520243899622043481178, hi := 8027520243899622043481178}
noncomputable def t20 : RBox := {lo := -2017385324946328166284412, hi := 2017385324946328166284412}
noncomputable def t21 : RBox := {lo := -494658337976382597555488, hi := 494658337976382597555488}
noncomputable def t22 : RBox := {lo := -118337461902628652472489, hi := 118337461902628652472489}
noncomputable def t23 : RBox := {lo := -27608037810688158630507, hi := 27608037810688158630507}
noncomputable def t24 : RBox := {lo := -6276890317904993958782, hi := 6276890317904993958782}
noncomputable def t25 : RBox := {lo := -1389739726659286490149, hi := 1389739726659286490149}
noncomputable def t26 : RBox := {lo := -299452577981342345968, hi := 299452577981342345968}
noncomputable def t27 : RBox := {lo := -62766453036154687587, hi := 62766453036154687587}
noncomputable def t28 : RBox := {lo := -12794327338528462519, hi := 12794327338528462519}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_left
end SharpPlanar.Bernstein19

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock21_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm21_0_0_2
 def realAnswer : RBox := ⟨(-426478654790351126762300784245),(-426478654790178581078752078580)⟩
end hm21_0_0_2
namespace hm21_1_0_2
 def realAnswer : RBox := ⟨410930184236636141796414804483,410930184236777751357546041939⟩
end hm21_1_0_2
namespace hm21_0_0_3
 def realAnswer : RBox := ⟨(-93296556965229690192941785254),(-93296556965096367985472639724)⟩
end hm21_0_0_3
namespace hm21_1_0_3
 def realAnswer : RBox := ⟨93825581738560846728652615600,93825581738670263796526214358⟩
end hm21_1_0_3
namespace hm21_0_0_4
 def realAnswer : RBox := ⟨274245577325808908608395234693,274245577325887254563883759547⟩
end hm21_0_0_4
namespace hm21_1_0_4
 def realAnswer : RBox := ⟨(-263449943878736943308039740830),(-263449943878672642833167291244)⟩
end hm21_1_0_4
namespace hm21_0_0_5
 def realAnswer : RBox := ⟨39310110847345917079691402801,39310110847382971548746211268⟩
end hm21_0_0_5
namespace hm21_1_0_5
 def realAnswer : RBox := ⟨(-40475047408812078261318245119),(-40475047408781665322990062921)⟩
end hm21_1_0_5
namespace hm21_0_0_6
 def realAnswer : RBox := ⟨(-75442457420873834165733220076),(-75442457420859181459999277059)⟩
end hm21_0_0_6
namespace hm21_1_0_6
 def realAnswer : RBox := ⟨72396260760555599643166706302,72396260760567626603396918054⟩
end hm21_1_0_6
namespace hm21_0_0_7
 def realAnswer : RBox := ⟨(-6485209451313610183746280863),(-6485209451308631996105097987)⟩
end hm21_0_0_7
namespace hm21_1_0_7
 def realAnswer : RBox := ⟨6965882401323370571968405430,6965882401327456850627315537⟩
end hm21_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock21_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm21_0_0_8
 def realAnswer : RBox := ⟨11658686209734497199454628948,11658686209735980093373114226⟩
end hm21_0_0_8
namespace hm21_1_0_8
 def realAnswer : RBox := ⟨(-11196567368926514303934070966),(-11196567368925297043627593928)⟩
end hm21_1_0_8
namespace hm21_0_0_9
 def realAnswer : RBox := ⟨595656276450481873241449267,595656276450875259939063121⟩
end hm21_0_0_9
namespace hm21_1_0_9
 def realAnswer : RBox := ⟨(-683685902456284459346048989),(-683685902455961530094297543)⟩
end hm21_1_0_9
namespace hm21_0_0_10
 def realAnswer : RBox := ⟨(-1160569250035384086357903813),(-1160569250035289989749253816)⟩
end hm21_0_0_10
namespace hm21_1_0_10
 def realAnswer : RBox := ⟨1116536460672786192755598060,1116536460672863438370963737⟩
end hm21_1_0_10
namespace hm21_0_0_11
 def realAnswer : RBox := ⟨(-34934428810622888351589130),(-34934428810602389520715754)⟩
end hm21_0_0_11
namespace hm21_1_0_11
 def realAnswer : RBox := ⟨44411910604979854022634125,44411910604996682273362887⟩
end hm21_1_0_11
namespace hm21_0_0_12
 def realAnswer : RBox := ⟨80854059716196317129034169,80854059716200418172908324⟩
end hm21_0_0_12
namespace hm21_1_0_12
 def realAnswer : RBox := ⟨(-77961526294620834611678153),(-77961526294617467831506744)⟩
end hm21_1_0_12
namespace hm21_0_0_13
 def realAnswer : RBox := ⟨1389542231349094228133322,1389542231349853073962377⟩
end hm21_0_0_13
namespace hm21_1_0_13
 def realAnswer : RBox := ⟨(-2074181774603690205138973),(-2074181774603067191177060)⟩
end hm21_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock21_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm21_0_1_2
 def realAnswer : RBox := ⟨3249763911890922725497153054,3249763911890922976776092601⟩
end hm21_0_1_2
namespace hm21_1_1_2
 def realAnswer : RBox := ⟨(-3692999854034548411100435270),(-3692999854034548365464267137)⟩
end hm21_1_1_2
namespace hm21_0_1_3
 def realAnswer : RBox := ⟨3787171616631372097193697343,3787171616631372423633304962⟩
end hm21_0_1_3
namespace hm21_1_1_3
 def realAnswer : RBox := ⟨(-3178877697994674888232830040),(-3178877697994674827984826024)⟩
end hm21_1_1_3
namespace hm21_0_1_4
 def realAnswer : RBox := ⟨(-3925586419655757893836446001),(-3925586419655757578022292525)⟩
end hm21_0_1_4
namespace hm21_1_1_4
 def realAnswer : RBox := ⟨4326979385990955170988969988,4326979385990955230181648510⟩
end hm21_1_1_4
namespace hm21_0_1_5
 def realAnswer : RBox := ⟨(-2165221390214724920283034225),(-2165221390214724677101792139)⟩
end hm21_0_1_5
namespace hm21_1_1_5
 def realAnswer : RBox := ⟨1751090174657154400471520424,1751090174657154446950835920⟩
end hm21_1_1_5
namespace hm21_0_1_6
 def realAnswer : RBox := ⟨1857559545192807323583790948,1857559545192807478686166000⟩
end hm21_0_1_6
namespace hm21_1_1_6
 def realAnswer : RBox := ⟨(-1997287908999806377733251724),(-1997287908999806347492637811)⟩
end hm21_1_1_6
namespace hm21_0_1_7
 def realAnswer : RBox := ⟨568599043946234637192645148,568599043946234721632623995⟩
end hm21_0_1_7
namespace hm21_1_1_7
 def realAnswer : RBox := ⟨(-437090941786695321044671034),(-437090941786695304163313455)⟩
end hm21_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock21_11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm21_0_1_8
 def realAnswer : RBox := ⟨(-462569290689468344345816668),(-462569290689468304287750597)⟩
end hm21_0_1_8
namespace hm21_1_1_8
 def realAnswer : RBox := ⟨487207479307795579089853063,487207479307795587350359714⟩
end hm21_1_1_8
namespace hm21_0_1_9
 def realAnswer : RBox := ⟨(-82770379508304231148350185),(-82770379508304214260766050)⟩
end hm21_0_1_9
namespace hm21_1_1_9
 def realAnswer : RBox := ⟨58846070560286762240808733,58846070560286765895870749⟩
end hm21_1_1_9
namespace hm21_0_1_10
 def realAnswer : RBox := ⟨70554797140294881628800379,70554797140294888084767247⟩
end hm21_0_1_10
namespace hm21_1_1_10
 def realAnswer : RBox := ⟨(-73028300524829966222168338),(-73028300524829964694253817)⟩
end hm21_1_1_10
namespace hm21_0_1_11
 def realAnswer : RBox := ⟨7277187351915915475855970,7277187351915917799434539⟩
end hm21_0_1_11
namespace hm21_1_1_11
 def realAnswer : RBox := ⟨(-4474183199552851829297974),(-4474183199552851165892913)⟩
end hm21_1_1_11
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein21
open IntegerIntervals CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 430171654644213129444216345717, hi := 430171654644385675173401219515}
lemma t0_checked : ((hm21_0_0_2.realAnswer).add hm21_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := 144713151994636564220186198622, hi := 144713151994836547621761922941}
lemma t1_checked : ((hm21_0_0_3.realAnswer).add hm21_1_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -626788252601725972036647168129, hi := -626788252601549693503614460532}
lemma t2_checked : ((hm21_0_0_4.realAnswer).add hm21_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := -138581553449385425235477534260, hi := -138581553449260366245549865884}
lemma t3_checked : ((hm21_0_0_5.realAnswer).add hm21_1_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 392038710732411125775427819029, hi := 392038710732485305251299013488}
lemma t4_checked : ((hm21_0_0_6.realAnswer).add hm21_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := 52566218610067641686413249387, hi := 52566218610105444927006290968}
lemma t5_checked : ((hm21_0_0_7.realAnswer).add hm21_1_1_7.realAnswer).scale (-243) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -138349320301764257363240820348, hi := -138349320301747366180608240406}
lemma t6_checked : ((hm21_0_0_8.realAnswer).add hm21_1_1_8.realAnswer).scale (-729) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := -11182786194636026175789065420, hi := -11182786194629304732810142546}
lemma t7_checked : ((hm21_0_0_9.realAnswer).add hm21_1_1_9.realAnswer).scale (-2187) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 31615755973534949301186928047, hi := 31615755973537360933507239777}
lemma t8_checked : ((hm21_0_0_10.realAnswer).add hm21_1_1_10.realAnswer).scale (-6561) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 1514999433976339067254918735, hi := 1514999433977127136680470446}
lemma t9_checked : ((hm21_0_0_11.realAnswer).add hm21_1_1_11.realAnswer).scale (-19683) 512=t9 := by decide +kernel
noncomputable def tr10 : RBox := {lo := -371133651526043528725074012, hi := 371133651526043528725074012}
noncomputable def t10 : RBox := {lo := -26063889024553967598026327108, hi := 16738984000761394528842340517}
lemma t10_checked : ((hm21_0_0_12.realAnswer).add tr10).scale (-59049) 1024=t10 := by decide +kernel
noncomputable def tr11 : RBox := {lo := -118092620930630225462300918, hi := 118092620930630225462300918}
noncomputable def t11 : RBox := {lo := -10334915409011369615460661094, hi := 10094531387862087184931194888}
lemma t11_checked : ((hm21_0_0_13.realAnswer).add tr11).scale (-177147) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -51162317996940730898206516312, hi := 51162317996940730898206516312}
noncomputable def t13 : RBox := {lo := -16073196934339071663200440071, hi := 16073196934339071663200440071}
noncomputable def t14 : RBox := {lo := -4801042232493527104590166183, hi := 4801042232493527104590166183}
noncomputable def t15 : RBox := {lo := -1370423344206941770097461362, hi := 1370423344206941770097461362}
noncomputable def t16 : RBox := {lo := -375651332374229463579451301, hi := 375651332374229463579451301}
noncomputable def t17 : RBox := {lo := -99341861518469404294500801, hi := 99341861518469404294500801}
noncomputable def t18 : RBox := {lo := -25451841483023795969396598, hi := 25451841483023795969396598}
noncomputable def t19 : RBox := {lo := -6340229876241134019004759, hi := 6340229876241134019004759}
noncomputable def t20 : RBox := {lo := -1539969542447927337362309, hi := 1539969542447927337362309}
noncomputable def t21 : RBox := {lo := -365409763453884912068065, hi := 365409763453884912068065}
noncomputable def t22 : RBox := {lo := -84793777425826568097104, hi := 84793777425826568097104}
noncomputable def t23 : RBox := {lo := -19247738723856548849879, hi := 19247738723856548849879}
noncomputable def t24 : RBox := {lo := -4272541658258472116877, hi := 4272541658258472116877}
noncomputable def t25 : RBox := {lo := -926793089502574754670, hi := 926793089502574754670}
noncomputable def t26 : RBox := {lo := -196290930856939223080, hi := 196290930856939223080}
noncomputable def t27 : RBox := {lo := -40557817829263615547, hi := 40557817829263615547}
noncomputable def t28 : RBox := {lo := -8169491131565603124, hi := 8169491131565603124}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N0_right
namespace N1_right
noncomputable def t0 : RBox := {lo := 414179948148527064521911957537, hi := 414179948148668674334322134540}
lemma t0_checked : ((hm21_1_0_2.realAnswer).add hm21_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := 146419130032788328238769469414, hi := 146419130032952454330239278980}
lemma t1_checked : ((hm21_1_0_3.realAnswer).add hm21_0_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -601594943171383577704221420370, hi := -601594943171238900925176563480}
lemma t2_checked : ((hm21_1_0_4.realAnswer).add hm21_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := -143910907196715460737904317786, hi := -143910907196612816250310010827}
lemma t3_checked : ((hm21_1_0_5.realAnswer).add hm21_0_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 375909965297851310269174392328, hi := 375909965297912197540545613024}
lemma t4_checked : ((hm21_1_0_6.realAnswer).add hm21_0_1_6.realAnswer).scale (81) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := 57214968475016064557066727826, hi := 57214968475047095376848915822}
lemma t5_checked : ((hm21_1_0_7.realAnswer).add hm21_0_1_7.realAnswer).scale (243) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -132804853513438302353063095082, hi := -132804853513424436541098221230}
lemma t6_checked : ((hm21_1_0_8.realAnswer).add hm21_0_1_8.realAnswer).scale (729) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := -13095624130129339578994148388, hi := -13095624130123821741441594358}
lemma t7_checked : ((hm21_1_0_9.realAnswer).add hm21_0_1_9.realAnswer).scale (2187) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 30423850556686034879047024055, hi := 30423850556688014765140824165}
lemma t8_checked : ((hm21_1_0_10.realAnswer).add hm21_0_1_10.realAnswer).scale (6561) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 1987102568526522326247618241, hi := 1987102568527169350064202610}
lemma t9_checked : ((hm21_1_0_11.realAnswer).add hm21_0_1_11.realAnswer).scale (19683) 512=t9 := by decide +kernel
noncomputable def tr10 : RBox := {lo := -371133651526043528725074012, hi := 371133651526043528725074012}
noncomputable def t10 : RBox := {lo := -25897090971808994131515506437, hi := 16905782053506325654008060165}
lemma t10_checked : ((hm21_1_0_12.realAnswer).add tr10).scale (59049) 1024=t10 := by decide +kernel
noncomputable def tr11 : RBox := {lo := -118092620930630225462300918, hi := 118092620930630225462300918}
noncomputable def t11 : RBox := {lo := -10394135058019566630244128111, hi := 10035311738853878421022840857}
lemma t11_checked : ((hm21_1_0_13.realAnswer).add tr11).scale (177147) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -51162317996940730898206516312, hi := 51162317996940730898206516312}
noncomputable def t13 : RBox := {lo := -16073196934339071663200440071, hi := 16073196934339071663200440071}
noncomputable def t14 : RBox := {lo := -4801042232493527104590166183, hi := 4801042232493527104590166183}
noncomputable def t15 : RBox := {lo := -1370423344206941770097461362, hi := 1370423344206941770097461362}
noncomputable def t16 : RBox := {lo := -375651332374229463579451301, hi := 375651332374229463579451301}
noncomputable def t17 : RBox := {lo := -99341861518469404294500801, hi := 99341861518469404294500801}
noncomputable def t18 : RBox := {lo := -25451841483023795969396598, hi := 25451841483023795969396598}
noncomputable def t19 : RBox := {lo := -6340229876241134019004759, hi := 6340229876241134019004759}
noncomputable def t20 : RBox := {lo := -1539969542447927337362309, hi := 1539969542447927337362309}
noncomputable def t21 : RBox := {lo := -365409763453884912068065, hi := 365409763453884912068065}
noncomputable def t22 : RBox := {lo := -84793777425826568097104, hi := 84793777425826568097104}
noncomputable def t23 : RBox := {lo := -19247738723856548849879, hi := 19247738723856548849879}
noncomputable def t24 : RBox := {lo := -4272541658258472116877, hi := 4272541658258472116877}
noncomputable def t25 : RBox := {lo := -926793089502574754670, hi := 926793089502574754670}
noncomputable def t26 : RBox := {lo := -196290930856939223080, hi := 196290930856939223080}
noncomputable def t27 : RBox := {lo := -40557817829263615547, hi := 40557817829263615547}
noncomputable def t28 : RBox := {lo := -8169491131565603124, hi := 8169491131565603124}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_right
namespace N0_left
noncomputable def t0 : RBox := {lo := 430171654644213129444216345717, hi := 430171654644385675173401219515}
lemma t0_checked : ((hm21_0_0_2.realAnswer).add hm21_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -96475434663224365081174615294, hi := -96475434663091042813457465748}
lemma t1_checked : ((hm21_0_0_3.realAnswer).add hm21_1_1_3.realAnswer).scale (1) 1=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -278572556711878209794065408057, hi := -278572556711799863779384204681}
lemma t2_checked : ((hm21_0_0_4.realAnswer).add hm21_1_1_4.realAnswer).scale (-1) 1=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 41061201022003071480162923225, hi := 41061201022040125995697047188}
lemma t3_checked : ((hm21_0_0_5.realAnswer).add hm21_1_1_5.realAnswer).scale (1) 1=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 77439745329858987807491914870, hi := 77439745329873640543466471800}
lemma t4_checked : ((hm21_0_0_6.realAnswer).add hm21_1_1_6.realAnswer).scale (-1) 1=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := -6922300393100305504790951897, hi := -6922300393095327300268411442}
lemma t5_checked : ((hm21_0_0_7.realAnswer).add hm21_1_1_7.realAnswer).scale (1) 1=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -12145893689043775680723473940, hi := -12145893689042292778544482011}
lemma t6_checked : ((hm21_0_0_8.realAnswer).add hm21_1_1_8.realAnswer).scale (-1) 1=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 654502347010768635482258000, hi := 654502347011162025834933870}
lemma t7_checked : ((hm21_0_0_9.realAnswer).add hm21_1_1_9.realAnswer).scale (1) 1=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 1233597550560119954443507633, hi := 1233597550560214052580072151}
lemma t8_checked : ((hm21_0_0_10.realAnswer).add hm21_1_1_10.realAnswer).scale (-1) 1=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := -39408612010175740180887104, hi := -39408612010155240686608667}
lemma t9_checked : ((hm21_0_0_11.realAnswer).add hm21_1_1_11.realAnswer).scale (1) 1=t9 := by decide +kernel
noncomputable def tr10 : RBox := {lo := -371133651526043528725074012, hi := 371133651526043528725074012}
noncomputable def t10 : RBox := {lo := -451987711242243946897982336, hi := 290279591809847211596039843}
lemma t10_checked : ((hm21_0_0_12.realAnswer).add tr10).scale (-1) 1=t10 := by decide +kernel
noncomputable def tr11 : RBox := {lo := -118092620930630225462300918, hi := 118092620930630225462300918}
noncomputable def t11 : RBox := {lo := -116703078699281131234167596, hi := 119482163161980078536263295}
lemma t11_checked : ((hm21_0_0_13.realAnswer).add tr11).scale (1) 1=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -394325719158795113209281728, hi := 394325719158795113209281728}
noncomputable def t13 : RBox := {lo := -82587800142195574588673691, hi := 82587800142195574588673691}
noncomputable def t14 : RBox := {lo := -16445909630017244117953782, hi := 16445909630017244117953782}
noncomputable def t15 : RBox := {lo := -3129578590409225449893404, hi := 3129578590409225449893404}
noncomputable def t16 : RBox := {lo := -571906178834794457983058, hi := 571906178834794457983058}
noncomputable def t17 : RBox := {lo := -100827938965423342075918, hi := 100827938965423342075918}
noncomputable def t18 : RBox := {lo := -17221720903165216877834, hi := 17221720903165216877834}
noncomputable def t19 : RBox := {lo := -2860033250465415001628, hi := 2860033250465415001628}
noncomputable def t20 : RBox := {lo := -463112976666628679145, hi := 463112976666628679145}
noncomputable def t21 : RBox := {lo := -73259458966171742099, hi := 73259458966171742099}
noncomputable def t22 : RBox := {lo := -11333297353995478269, hi := 11333297353995478269}
noncomputable def t23 : RBox := {lo := -1715065680303394038, hi := 1715065680303394038}
noncomputable def t24 : RBox := {lo := -253802612725042730, hi := 253802612725042730}
noncomputable def t25 : RBox := {lo := -36702978599261021, hi := 36702978599261021}
noncomputable def t26 : RBox := {lo := -5182359051567824, hi := 5182359051567824}
noncomputable def t27 : RBox := {lo := -713855953241536, hi := 713855953241536}
noncomputable def t28 : RBox := {lo := -95860513728366, hi := 95860513728366}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N0_left
namespace N1_left
noncomputable def t0 : RBox := {lo := 414179948148527064521911957537, hi := 414179948148668674334322134540}
lemma t0_checked : ((hm21_1_0_2.realAnswer).add hm21_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -97612753355301636220159519320, hi := -97612753355192218825846312943}
lemma t1_checked : ((hm21_1_0_3.realAnswer).add hm21_0_1_3.realAnswer).scale (-1) 1=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -267375530298392701201876186831, hi := -267375530298328400411189583769}
lemma t2_checked : ((hm21_1_0_4.realAnswer).add hm21_0_1_4.realAnswer).scale (1) 1=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 42640268798996390000091855060, hi := 42640268799026803181601279344}
lemma t3_checked : ((hm21_1_0_5.realAnswer).add hm21_0_1_5.realAnswer).scale (-1) 1=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := 74253820305748406966750497250, hi := 74253820305760434082083084054}
lemma t4_checked : ((hm21_1_0_6.realAnswer).add hm21_0_1_6.realAnswer).scale (1) 1=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := -7534481445273691572259939532, hi := -7534481445269605209161050578}
lemma t5_checked : ((hm21_1_0_7.realAnswer).add hm21_0_1_7.realAnswer).scale (-1) 1=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := -11659136659615982648279887634, hi := -11659136659614765347915344525}
lemma t6_checked : ((hm21_1_0_8.realAnswer).add hm21_0_1_8.realAnswer).scale (1) 1=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 766456281964265744355063593, hi := 766456281964588690494399174}
lemma t7_checked : ((hm21_1_0_9.realAnswer).add hm21_0_1_9.realAnswer).scale (-1) 1=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := 1187091257813081074384398439, hi := 1187091257813158326455730984}
lemma t8_checked : ((hm21_1_0_10.realAnswer).add hm21_0_1_10.realAnswer).scale (1) 1=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := -51689097956912600072797426, hi := -51689097956895769498490095}
lemma t9_checked : ((hm21_1_0_11.realAnswer).add hm21_0_1_11.realAnswer).scale (-1) 1=t9 := by decide +kernel
noncomputable def tr10 : RBox := {lo := -371133651526043528725074012, hi := 371133651526043528725074012}
noncomputable def t10 : RBox := {lo := -449095177820664363336752165, hi := 293172125231426060893567268}
lemma t10_checked : ((hm21_1_0_12.realAnswer).add tr10).scale (1) 1=t10 := by decide +kernel
noncomputable def tr11 : RBox := {lo := -118092620930630225462300918, hi := 118092620930630225462300918}
noncomputable def t11 : RBox := {lo := -116018439156027158271123858, hi := 120166802705233915667439891}
lemma t11_checked : ((hm21_1_0_13.realAnswer).add tr11).scale (-1) 1=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -394325719158795113209281728, hi := 394325719158795113209281728}
noncomputable def t13 : RBox := {lo := -82587800142195574588673691, hi := 82587800142195574588673691}
noncomputable def t14 : RBox := {lo := -16445909630017244117953782, hi := 16445909630017244117953782}
noncomputable def t15 : RBox := {lo := -3129578590409225449893404, hi := 3129578590409225449893404}
noncomputable def t16 : RBox := {lo := -571906178834794457983058, hi := 571906178834794457983058}
noncomputable def t17 : RBox := {lo := -100827938965423342075918, hi := 100827938965423342075918}
noncomputable def t18 : RBox := {lo := -17221720903165216877834, hi := 17221720903165216877834}
noncomputable def t19 : RBox := {lo := -2860033250465415001628, hi := 2860033250465415001628}
noncomputable def t20 : RBox := {lo := -463112976666628679145, hi := 463112976666628679145}
noncomputable def t21 : RBox := {lo := -73259458966171742099, hi := 73259458966171742099}
noncomputable def t22 : RBox := {lo := -11333297353995478269, hi := 11333297353995478269}
noncomputable def t23 : RBox := {lo := -1715065680303394038, hi := 1715065680303394038}
noncomputable def t24 : RBox := {lo := -253802612725042730, hi := 253802612725042730}
noncomputable def t25 : RBox := {lo := -36702978599261021, hi := 36702978599261021}
noncomputable def t26 : RBox := {lo := -5182359051567824, hi := 5182359051567824}
noncomputable def t27 : RBox := {lo := -713855953241536, hi := 713855953241536}
noncomputable def t28 : RBox := {lo := -95860513728366, hi := 95860513728366}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_left
end SharpPlanar.Bernstein21

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock24_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm24_0_0_2
 def realAnswer : RBox := ⟨(-58105882735373984564764829131),(-58105882735201165419420249566)⟩
end hm24_0_0_2
namespace hm24_1_0_2
 def realAnswer : RBox := ⟨57793955036254893051606266065,57793955036396609988655123129⟩
end hm24_1_0_2
namespace hm24_0_0_3
 def realAnswer : RBox := ⟨122037610667935720482374712002,122037610668069241517346725008⟩
end hm24_0_0_3
namespace hm24_1_0_3
 def realAnswer : RBox := ⟨(-120184454184484915291874767715),(-120184454184375416749240741563)⟩
end hm24_1_0_3
namespace hm24_0_0_4
 def realAnswer : RBox := ⟨(-42246824923135612289826508074),(-42246824923057152499719636077)⟩
end hm24_0_0_4
namespace hm24_1_0_4
 def realAnswer : RBox := ⟨40651107797369817058899462369,40651107797434164997719442166⟩
end hm24_1_0_4
namespace hm24_0_0_5
 def realAnswer : RBox := ⟨(-51145832445786572745783738498),(-51145832445749464941342827274)⟩
end hm24_0_0_5
namespace hm24_1_0_5
 def realAnswer : RBox := ⟨50919206272100943490459245486,50919206272131378808650977119⟩
end hm24_1_0_5
namespace hm24_0_0_6
 def realAnswer : RBox := ⟨27087858226706663438380139108,27087858226721337223744812225⟩
end hm24_0_0_6
namespace hm24_1_0_6
 def realAnswer : RBox := ⟨(-26359536285964298707202177451),(-26359536285952262892102108266)⟩
end hm24_1_0_6
namespace hm24_0_0_7
 def realAnswer : RBox := ⟨8982120260878161345734723274,8982120260883146733494279443⟩
end hm24_0_0_7
namespace hm24_1_0_7
 def realAnswer : RBox := ⟨(-9099085245214852106191211164),(-9099085245210762807275231980)⟩
end hm24_1_0_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock24_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm24_0_0_8
 def realAnswer : RBox := ⟨(-5978602485532603764871144821),(-5978602485531118705114766643)⟩
end hm24_0_0_8
namespace hm24_1_0_8
 def realAnswer : RBox := ⟨5842683160006169561859294214,5842683160007387727793100305⟩
end hm24_1_0_8
namespace hm24_0_0_9
 def realAnswer : RBox := ⟨(-883095238816991821324885041),(-883095238816597852027134623)⟩
end hm24_0_0_9
namespace hm24_1_0_9
 def realAnswer : RBox := ⟨920608312122712838693156982,920608312123036010554933758⟩
end hm24_1_0_9
namespace hm24_0_0_10
 def realAnswer : RBox := ⟨732778967976492278482235207,732778967976586516919271378⟩
end hm24_0_0_10
namespace hm24_1_0_10
 def realAnswer : RBox := ⟨(-718530535821119443635389541),(-718530535821042139264947338)⟩
end hm24_1_0_10
namespace hm24_0_0_11
 def realAnswer : RBox := ⟨55285109236471165331762045,55285109236491695731032363⟩
end hm24_0_0_11
namespace hm24_1_0_11
 def realAnswer : RBox := ⟨(-60407611742982269825685748),(-60407611742965428570869270)⟩
end hm24_1_0_11
namespace hm24_0_0_12
 def realAnswer : RBox := ⟨(-58421428539381585556851676),(-58421428539377478036895253)⟩
end hm24_0_0_12
namespace hm24_1_0_12
 def realAnswer : RBox := ⟨57461870726013518491055512,57461870726016887921620286⟩
end hm24_1_0_12
namespace hm24_0_0_13
 def realAnswer : RBox := ⟨(-2368857873352360561726935),(-2368857873351600482429454)⟩
end hm24_0_0_13
namespace hm24_1_0_13
 def realAnswer : RBox := ⟨2794811401446885903322496,2794811401447509418734963⟩
end hm24_1_0_13
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock24_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm24_0_1_2
 def realAnswer : RBox := ⟨(-2086396849178749865966711395),(-2086396849178749584713512836)⟩
end hm24_0_1_2
namespace hm24_1_1_2
 def realAnswer : RBox := ⟨1921659021173350090989737698,1921659021173350128696494162⟩
end hm24_1_1_2
namespace hm24_0_1_3
 def realAnswer : RBox := ⟨1927249121700872065115288478,1927249121700872428321807218⟩
end hm24_0_1_3
namespace hm24_1_1_3
 def realAnswer : RBox := ⟨(-2300118899998373128621642661),(-2300118899998373079412976299)⟩
end hm24_1_1_3
namespace hm24_0_1_4
 def realAnswer : RBox := ⟨2086620181986076600723587740,2086620181986076950418172483⟩
end hm24_0_1_4
namespace hm24_1_1_4
 def realAnswer : RBox := ⟨(-1877175810155890590585061627),(-1877175810155890542545062065)⟩
end hm24_1_1_4
namespace hm24_0_1_5
 def realAnswer : RBox := ⟨(-1426489390613511580322220249),(-1426489390613511312681836809)⟩
end hm24_0_1_5
namespace hm24_1_1_5
 def realAnswer : RBox := ⟨1645737780898032346361721287,1645737780898032383584529508⟩
end hm24_1_1_5
namespace hm24_0_1_6
 def realAnswer : RBox := ⟨(-816751904855333796957989519),(-816751904855333627142134805)⟩
end hm24_0_1_6
namespace hm24_1_1_6
 def realAnswer : RBox := ⟨714690366421735658414378639,714690366421735682399864201⟩
end hm24_1_1_6
namespace hm24_0_1_7
 def realAnswer : RBox := ⟨490675378479356004243961078,490675378479356096104546410⟩
end hm24_0_1_7
namespace hm24_1_1_7
 def realAnswer : RBox := ⟨(-550961878014508415179333354),(-550961878014508401986928179)⟩
end hm24_1_1_7
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock24_11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm24_0_1_8
 def realAnswer : RBox := ⟨166689614323798618257638428,166689614323798661577782656⟩
end hm24_0_1_8
namespace hm24_1_1_8
 def realAnswer : RBox := ⟨(-140871666766662817002394138),(-140871666766662810617285055)⟩
end hm24_1_1_8
namespace hm24_0_1_9
 def realAnswer : RBox := ⟨(-96502571120004610755637449),(-96502571120004592625897576)⟩
end hm24_0_1_9
namespace hm24_1_1_9
 def realAnswer : RBox := ⟨105973214014816948378868397,105973214014816951176797126⟩
end hm24_1_1_9
namespace hm24_0_1_10
 def realAnswer : RBox := ⟨(-20427818183929109013711317),(-20427818183929102137647523)⟩
end hm24_0_1_10
namespace hm24_1_1_10
 def realAnswer : RBox := ⟨16462935124334889045760496,16462935124334890223655496⟩
end hm24_1_1_10
namespace hm24_0_1_11
 def realAnswer : RBox := ⟨12211986758761664342134819,12211986758761666789795216⟩
end hm24_0_1_11
namespace hm24_1_1_11
 def realAnswer : RBox := ⟨(-13161908452678197363117282),(-13161908452678196830627078)⟩
end hm24_1_1_11
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein24
open IntegerIntervals CachedData
namespace N0_right
noncomputable def t0 : RBox := {lo := 56184223714027815290723755404, hi := 56184223714200634473775091433}
lemma t0_checked : ((hm24_0_0_2.realAnswer).add hm24_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -59868745884035434218966874355, hi := -59868745883968673676876534670}
lemma t1_checked : ((hm24_0_0_3.realAnswer).add hm24_1_1_3.realAnswer).scale (-1) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := 11031000183303260760566174535, hi := 11031000183322875720102892426}
lemma t2_checked : ((hm24_0_0_4.realAnswer).add hm24_1_1_4.realAnswer).scale (-1) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 6187511833106429069719787220, hi := 6187511833111067549927752152}
lemma t3_checked : ((hm24_0_0_5.realAnswer).add hm24_1_1_5.realAnswer).scale (-1) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := -1737659287071442056634042277, hi := -1737659287070524943549657359}
lemma t4_checked : ((hm24_0_0_6.realAnswer).add hm24_1_1_6.realAnswer).scale (-1) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := -263473699464644947859604727, hi := -263473699464489154079855935}
lemma t5_checked : ((hm24_0_0_7.realAnswer).add hm24_1_1_7.realAnswer).scale (-1) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := 95616783629652836183313307, hi := 95616783629676040341774047}
lemma t6_checked : ((hm24_0_0_8.realAnswer).add hm24_1_1_8.realAnswer).scale (-1) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 6071265818763913287893261, hi := 6071265818766991194890756}
lemma t7_checked : ((hm24_0_0_9.realAnswer).add hm24_1_1_9.realAnswer).scale (-1) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := -2926726183987974246652059, hi := -2926726183987606123156233}
lemma t8_checked : ((hm24_0_0_10.realAnswer).add hm24_1_1_10.realAnswer).scale (-1) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := -82271876530885740039855, hi := -82271876530845640563759}
lemma t9_checked : ((hm24_0_0_11.realAnswer).add hm24_1_1_11.realAnswer).scale (-1) 512=t9 := by decide +kernel
noncomputable def tr10 : RBox := {lo := -185486386187469648751994235, hi := 185486386187469648751994235}
noncomputable def t10 : RBox := {lo := -124086872703215010463964, hi := 238191225319190658504733}
lemma t10_checked : ((hm24_0_0_12.realAnswer).add tr10).scale (-1) 1024=t10 := by decide +kernel
noncomputable def tr11 : RBox := {lo := -58997102609725292366925614, hi := 58997102609725292366925614}
noncomputable def t11 : RBox := {lo := -27650510125182466740477, hi := 29963847892127760219069}
lemma t11_checked : ((hm24_0_0_13.realAnswer).add tr11).scale (-1) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -92005094558355516319346, hi := 92005094558355516319346}
noncomputable def t13 : RBox := {lo := -9492764401100362812387, hi := 9492764401100362812387}
noncomputable def t14 : RBox := {lo := -927581682407947607361, hi := 927581682407947607361}
noncomputable def t15 : RBox := {lo := -86223802489917842930, hi := 86223802489917842930}
noncomputable def t16 : RBox := {lo := -7658197989607200361, hi := 7658197989607200361}
noncomputable def t17 : RBox := {lo := -652747664927167744, hi := 652747664927167744}
noncomputable def t18 : RBox := {lo := -53623681422163501, hi := 53623681422163501}
noncomputable def t19 : RBox := {lo := -4263623176223224, hi := 4263623176223224}
noncomputable def t20 : RBox := {lo := -329394523921959, hi := 329394523921959}
noncomputable def t21 : RBox := {lo := -24813157369210, hi := 24813157369210}
noncomputable def t22 : RBox := {lo := -1827741453474, hi := 1827741453474}
noncomputable def t23 : RBox := {lo := -131921188015, hi := 131921188015}
noncomputable def t24 : RBox := {lo := -9341435340, hi := 9341435340}
noncomputable def t25 : RBox := {lo := -649223786, hi := 649223786}
noncomputable def t26 : RBox := {lo := -44274198, hi := 44274198}
noncomputable def t27 : RBox := {lo := -2960569, hi := 2960569}
noncomputable def t28 : RBox := {lo := -193934, hi := 193934}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N0_right
namespace N1_right
noncomputable def t0 : RBox := {lo := 55707558187076143185639554670, hi := 55707558187217860403941610293}
lemma t0_checked : ((hm24_1_0_2.realAnswer).add hm24_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -59128602531392021613379739619, hi := -59128602531337272160459467172}
lemma t1_checked : ((hm24_1_0_3.realAnswer).add hm24_0_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := 10684431994838973414905762527, hi := 10684431994855060487034403663}
lemma t2_checked : ((hm24_1_0_4.realAnswer).add hm24_0_1_4.realAnswer).scale (1) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := 6186589610185928988767128154, hi := 6186589610189733436996142539}
lemma t3_checked : ((hm24_1_0_5.realAnswer).add hm24_0_1_5.realAnswer).scale (1) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := -1698518011926227031510010436, hi := -1698518011925474782452765191}
lemma t4_checked : ((hm24_1_0_6.realAnswer).add hm24_0_1_6.realAnswer).scale (1) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := -269012808335484253185851566, hi := -269012808335356459724083924}
lemma t5_checked : ((hm24_1_0_7.realAnswer).add hm24_0_1_7.realAnswer).scale (1) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := 93896449598905752814327072, hi := 93896449598924787333920047}
lemma t6_checked : ((hm24_1_0_8.realAnswer).add hm24_0_1_8.realAnswer).scale (1) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := 6438326101583658030761871, hi := 6438326101586182952570596}
lemma t7_checked : ((hm24_1_0_9.realAnswer).add hm24_0_1_9.realAnswer).scale (1) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := -2886556070332220908785551, hi := -2886556070331918911728886}
lemma t8_checked : ((hm24_1_0_10.realAnswer).add hm24_0_1_10.realAnswer).scale (1) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := -94132080047305870085061, hi := -94132080047272972228660}
lemma t9_checked : ((hm24_1_0_11.realAnswer).add hm24_0_1_11.realAnswer).scale (1) 512=t9 := by decide +kernel
noncomputable def tr10 : RBox := {lo := -185486386187469648751994235, hi := 185486386187469648751994235}
noncomputable def t10 : RBox := {lo := -125023940880328252207948, hi := 237254157142076695970327}
lemma t10_checked : ((hm24_1_0_12.realAnswer).add tr10).scale (1) 1024=t10 := by decide +kernel
noncomputable def tr11 : RBox := {lo := -58997102609725292366925614, hi := 58997102609725292366925614}
noncomputable def t11 : RBox := {lo := -27442525004042190656057, hi := 30171833013267969621905}
lemma t11_checked : ((hm24_1_0_13.realAnswer).add tr11).scale (1) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -92005094558355516319346, hi := 92005094558355516319346}
noncomputable def t13 : RBox := {lo := -9492764401100362812387, hi := 9492764401100362812387}
noncomputable def t14 : RBox := {lo := -927581682407947607361, hi := 927581682407947607361}
noncomputable def t15 : RBox := {lo := -86223802489917842930, hi := 86223802489917842930}
noncomputable def t16 : RBox := {lo := -7658197989607200361, hi := 7658197989607200361}
noncomputable def t17 : RBox := {lo := -652747664927167744, hi := 652747664927167744}
noncomputable def t18 : RBox := {lo := -53623681422163501, hi := 53623681422163501}
noncomputable def t19 : RBox := {lo := -4263623176223224, hi := 4263623176223224}
noncomputable def t20 : RBox := {lo := -329394523921959, hi := 329394523921959}
noncomputable def t21 : RBox := {lo := -24813157369210, hi := 24813157369210}
noncomputable def t22 : RBox := {lo := -1827741453474, hi := 1827741453474}
noncomputable def t23 : RBox := {lo := -131921188015, hi := 131921188015}
noncomputable def t24 : RBox := {lo := -9341435340, hi := 9341435340}
noncomputable def t25 : RBox := {lo := -649223786, hi := 649223786}
noncomputable def t26 : RBox := {lo := -44274198, hi := 44274198}
noncomputable def t27 : RBox := {lo := -2960569, hi := 2960569}
noncomputable def t28 : RBox := {lo := -193934, hi := 193934}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_right
namespace N0_left
noncomputable def t0 : RBox := {lo := 56184223714027815290723755404, hi := 56184223714200634473775091433}
lemma t0_checked : ((hm24_0_0_2.realAnswer).add hm24_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := 179606237651906021030629604011, hi := 179606237652106302656900623064}
lemma t1_checked : ((hm24_0_0_3.realAnswer).add hm24_1_1_3.realAnswer).scale (3) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := 99279001649729346845095570819, hi := 99279001649905881480926031828}
lemma t2_checked : ((hm24_0_0_4.realAnswer).add hm24_1_1_4.realAnswer).scale (-9) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := -167062819493998823848049308088, hi := -167062819493873584882434254960}
lemma t3_checked : ((hm24_0_0_5.realAnswer).add hm24_1_1_5.realAnswer).scale (27) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := -140750402252786806587357424407, hi := -140750402252712520427522246094}
lemma t4_checked : ((hm24_0_0_6.realAnswer).add hm24_1_1_6.realAnswer).scale (-81) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := 64024108969870864441404992205, hi := 64024108969908722329883948661}
lemma t5_checked : ((hm24_0_0_7.realAnswer).add hm24_1_1_7.realAnswer).scale (243) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := 69704635266016917577635401372, hi := 69704635266033833409153279705}
lemma t6_checked : ((hm24_0_0_8.realAnswer).add hm24_1_1_8.realAnswer).scale (-729) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := -13277858345643409743226081254, hi := -13277858345636678360622563327}
lemma t7_checked : ((hm24_0_0_9.realAnswer).add hm24_1_1_9.realAnswer).scale (2187) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := -19202250493145099032284153205, hi := -19202250493142683774028046122}
lemma t8_checked : ((hm24_0_0_10.realAnswer).add hm24_1_1_10.realAnswer).scale (-6561) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 1619357345756634743216474355, hi := 1619357345757424021204447705}
lemma t9_checked : ((hm24_0_0_11.realAnswer).add hm24_1_1_11.realAnswer).scale (19683) 512=t9 := by decide +kernel
noncomputable def tr10 : RBox := {lo := -185486386187469648751994235, hi := 185486386187469648751994235}
noncomputable def t10 : RBox := {lo := -7327205746252143152886601356, hi := 14064953663872889194045939648}
lemma t10_checked : ((hm24_0_0_12.realAnswer).add tr10).scale (-59049) 1024=t10 := by decide +kernel
noncomputable def tr11 : RBox := {lo := -58997102609725292366925614, hi := 58997102609725292366925614}
noncomputable def t11 : RBox := {lo := -5308005762546756339527350146, hi := 4898204917145698435675215457}
lemma t11_checked : ((hm24_0_0_13.realAnswer).add tr11).scale (177147) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -48895279457187013948269047943, hi := 48895279457187013948269047943}
noncomputable def t13 : RBox := {lo := -15134532618255533740132000351, hi := 15134532618255533740132000351}
noncomputable def t14 : RBox := {lo := -4436594431925058759630009084, hi := 4436594431925058759630009084}
noncomputable def t15 : RBox := {lo := -1237217323114199565829174978, hi := 1237217323114199565829174978}
noncomputable def t16 : RBox := {lo := -329660312221382053495992951, hi := 329660312221382053495992951}
noncomputable def t17 : RBox := {lo := -84295939846563825576348090, hi := 84295939846563825576348090}
noncomputable def t18 : RBox := {lo := -20774912878554798685150661, hi := 20774912878554798685150661}
noncomputable def t19 : RBox := {lo := -4955444927532403499927245, hi := 4955444927532403499927245}
noncomputable def t20 : RBox := {lo := -1148527687785906431688423, hi := 1148527687785906431688423}
noncomputable def t21 : RBox := {lo := -259554390163556698989919, hi := 259554390163556698989919}
noncomputable def t22 : RBox := {lo := -57356463501299681808300, hi := 57356463501299681808300}
noncomputable def t23 : RBox := {lo := -12419479994321041648233, hi := 12419479994321041648233}
noncomputable def t24 : RBox := {lo := -2638297253070937662254, hi := 2638297253070937662254}
noncomputable def t25 : RBox := {lo := -550079918257030980703, hi := 550079918257030980703}
noncomputable def t26 : RBox := {lo := -112539070762571183662, hi := 112539070762571183662}
noncomputable def t27 : RBox := {lo := -22576099940430149943, hi := 22576099940430149943}
noncomputable def t28 : RBox := {lo := -4436570569074936528, hi := 4436570569074936528}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N0_left
namespace N1_left
noncomputable def t0 : RBox := {lo := 55707558187076143185639554670, hi := 55707558187217860403941610293}
lemma t0_checked : ((hm24_1_0_2.realAnswer).add hm24_0_1_2.realAnswer).scale (1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := 177385807594011816481378401517, hi := 177385807594176064840139218856}
lemma t1_checked : ((hm24_1_0_3.realAnswer).add hm24_0_1_3.realAnswer).scale (-3) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := 96159887953550760734151862745, hi := 96159887953695544383309632961}
lemma t2_checked : ((hm24_1_0_4.realAnswer).add hm24_0_1_4.realAnswer).scale (9) 4=t2 := by decide +kernel
noncomputable def t3 : RBox := {lo := -167037919475122802798895848547, hi := -167037919475020082696712460174}
lemma t3_checked : ((hm24_1_0_5.realAnswer).add hm24_0_1_5.realAnswer).scale (-27) 8=t3 := by decide +kernel
noncomputable def t4 : RBox := {lo := -137579958966024389552310845286, hi := -137579958965963457378673980546}
lemma t4_checked : ((hm24_1_0_6.realAnswer).add hm24_0_1_6.realAnswer).scale (81) 16=t4 := by decide +kernel
noncomputable def t5 : RBox := {lo := 65370112425491619712952393547, hi := 65370112425522673524161930341}
lemma t5_checked : ((hm24_1_0_7.realAnswer).add hm24_0_1_7.realAnswer).scale (-243) 32=t5 := by decide +kernel
noncomputable def t6 : RBox := {lo := 68450511757602293801644435875, hi := 68450511757616169966427713728}
lemma t6_checked : ((hm24_1_0_8.realAnswer).add hm24_0_1_8.realAnswer).scale (729) 64=t6 := by decide +kernel
noncomputable def t7 : RBox := {lo := -14080619184168982117271891641, hi := -14080619184163460113276212645}
lemma t7_checked : ((hm24_1_0_9.realAnswer).add hm24_0_1_9.realAnswer).scale (-2187) 128=t7 := by decide +kernel
noncomputable def t8 : RBox := {lo := -18938694377449701382541995037, hi := -18938694377447719979853222199}
lemma t8_checked : ((hm24_1_0_10.realAnswer).add hm24_0_1_10.realAnswer).scale (6561) 256=t8 := by decide +kernel
noncomputable def t9 : RBox := {lo := 1852801731570473912376719931, hi := 1852801731571121440884244015}
lemma t9_checked : ((hm24_1_0_11.realAnswer).add hm24_0_1_11.realAnswer).scale (-19683) 512=t9 := by decide +kernel
noncomputable def tr10 : RBox := {lo := -185486386187469648751994235, hi := 185486386187469648751994235}
noncomputable def t10 : RBox := {lo := -7382538685042502964627119780, hi := 14009620725082486820351820167}
lemma t10_checked : ((hm24_1_0_12.realAnswer).add tr10).scale (59049) 1024=t10 := by decide +kernel
noncomputable def tr11 : RBox := {lo := -58997102609725292366925614, hi := 58997102609725292366925614}
noncomputable def t11 : RBox := {lo := -5344849702801381014611530388, hi := 4861360976891061948148389426}
lemma t11_checked : ((hm24_1_0_13.realAnswer).add tr11).scale (-177147) 2048=t11 := by decide +kernel
noncomputable def t12 : RBox := {lo := -48895279457187013948269047943, hi := 48895279457187013948269047943}
noncomputable def t13 : RBox := {lo := -15134532618255533740132000351, hi := 15134532618255533740132000351}
noncomputable def t14 : RBox := {lo := -4436594431925058759630009084, hi := 4436594431925058759630009084}
noncomputable def t15 : RBox := {lo := -1237217323114199565829174978, hi := 1237217323114199565829174978}
noncomputable def t16 : RBox := {lo := -329660312221382053495992951, hi := 329660312221382053495992951}
noncomputable def t17 : RBox := {lo := -84295939846563825576348090, hi := 84295939846563825576348090}
noncomputable def t18 : RBox := {lo := -20774912878554798685150661, hi := 20774912878554798685150661}
noncomputable def t19 : RBox := {lo := -4955444927532403499927245, hi := 4955444927532403499927245}
noncomputable def t20 : RBox := {lo := -1148527687785906431688423, hi := 1148527687785906431688423}
noncomputable def t21 : RBox := {lo := -259554390163556698989919, hi := 259554390163556698989919}
noncomputable def t22 : RBox := {lo := -57356463501299681808300, hi := 57356463501299681808300}
noncomputable def t23 : RBox := {lo := -12419479994321041648233, hi := 12419479994321041648233}
noncomputable def t24 : RBox := {lo := -2638297253070937662254, hi := 2638297253070937662254}
noncomputable def t25 : RBox := {lo := -550079918257030980703, hi := 550079918257030980703}
noncomputable def t26 : RBox := {lo := -112539070762571183662, hi := 112539070762571183662}
noncomputable def t27 : RBox := {lo := -22576099940430149943, hi := 22576099940430149943}
noncomputable def t28 : RBox := {lo := -4436570569074936528, hi := 4436570569074936528}
noncomputable def ts : Fin 29 → RBox := ![t0,t1,t2,t3,t4,t5,t6,t7,t8,t9,t10,t11,t12,t13,t14,t15,t16,t17,t18,t19,t20,t21,t22,t23,t24,t25,t26,t27,t28]
end N1_left
end SharpPlanar.Bernstein24

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock25_0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm25_0_0_2
 def realAnswer : RBox := ⟨(-28915690192598627060465666079),(-28915690192425659502817430710)⟩
end hm25_0_0_2
namespace hm25_0_0_3
 def realAnswer : RBox := ⟨(-26575453292563120014417037359),(-26575453292429491636752605172)⟩
end hm25_0_0_3
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock25_1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm25_0_0_12
 def realAnswer : RBox := ⟨53015999058273793950962265,53015999058277905066273949⟩
end hm25_0_0_12
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock25_10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals
namespace hm25_1_1_2
 def realAnswer : RBox := ⟨(-740286920018464820059952673),(-740286920018464780883396979)⟩
end hm25_1_1_2
namespace hm25_1_1_3
 def realAnswer : RBox := ⟨2522687815571104186980045420,2522687815571104238024619969⟩
end hm25_1_1_3
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Bernstein25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.Bernstein25
open IntegerIntervals CachedData
namespace N0_left
noncomputable def t0 : RBox := {lo := 29655977112444124283700827689, hi := 29655977112617091880525618752}
lemma t0_checked : ((hm25_0_0_2.realAnswer).add hm25_1_1_2.realAnswer).scale (-1) 1=t0 := by decide +kernel
noncomputable def t1 : RBox := {lo := -12026382738496007913718495970, hi := -12026382738429193699363992601}
lemma t1_checked : ((hm25_0_0_3.realAnswer).add hm25_1_1_3.realAnswer).scale (1) 2=t1 := by decide +kernel
noncomputable def t2 : RBox := {lo := -9545887615597315804338344950, hi := -9545887615577685525402012263}
noncomputable def tr10 : RBox := {lo := -147751113260532258274768477, hi := 147751113260532258274768477}
noncomputable def t10 : RBox := {lo := -196061633123838050137737, hi := 92514759963143031566218}
lemma t10_checked : ((hm25_0_0_12.realAnswer).add tr10).scale (-1) 1024=t10 := by decide +kernel
noncomputable def t11 : RBox := {lo := -834783007497098432118138, hi := 834783007497098432118138}
noncomputable def t12 : RBox := {lo := -91138538715420847058098, hi := 91138538715420847058098}
noncomputable def t13 : RBox := {lo := -9373199443828439527322, hi := 9373199443828439527322}
noncomputable def t14 : RBox := {lo := -912111747117539833158, hi := 912111747117539833158}
noncomputable def t15 : RBox := {lo := -84339555928767524402, hi := 84339555928767524402}
noncomputable def t16 : RBox := {lo := -7441404478306131261, hi := 7441404478306131261}
noncomputable def t17 : RBox := {lo := -629113109510099325, hi := 629113109510099325}
noncomputable def t18 : RBox := {lo := -51175531188269501, hi := 51175531188269501}
noncomputable def t19 : RBox := {lo := -4022077847157108, hi := 4022077847157108}
noncomputable def t20 : RBox := {lo := -306643047286786, hi := 306643047286786}
noncomputable def t21 : RBox := {lo := -22763106357385, hi := 22763106357385}
noncomputable def t22 : RBox := {lo := -1650697079642, hi := 1650697079642}
end N0_left
end SharpPlanar.Bernstein25

end OAI
end


