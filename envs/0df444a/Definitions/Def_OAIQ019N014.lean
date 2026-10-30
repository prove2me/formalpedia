-- Prove2me | Definitions.Def_OAIQ019N014
-- name    : OAIQ019N014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T06:00:00.077362+00:00
-- url     : https://prove2.me/theorems/3a028023-3c67-4c01-bb7c-ebc20e5ee411
-- title:
--   Definitions bundle OAIQ019N014 of the split of OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 8 definitions and 2 theorems. The definitions and types are `OAI.NuclearUltrapower.SL3Certificate.g0`, `OAI.NuclearUltrapower.SL3Certificate.q93`, `OAI.NuclearUltrapower.SL3Certificate.q95`, `OAI.NuclearUltrapower.SL3Certificate.q96`, `OAI.NuclearUltrapower.SL3Certificate.q97`, `OAI.NuclearUltrapower.SL3Certificate.q98`, `OAI.NuclearUltrapower.SL3Certificate.q99`, `OAI.NuclearUltrapower.hilbertDiagonal`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`NuclearUltrapower_FaithfulGNS`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/FaithfulGNS.lean), [`NuclearUltrapower_SOSCertificate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSCertificate.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ019N041`.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ019_Nuc.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FaithfulGNS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u
open scoped ComplexOrder ENNReal
namespace NuclearUltrapower
variable {A : Type u} [CStarAlgebra A] [Nontrivial A]

section DirectSum
variable {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)]

local instance gnsSpectralOrder_rb44978_1 : PartialOrder A := CStarAlgebra.spectralOrder A
/-- A uniformly bounded diagonal family acts on the Hilbert direct sum. -/
def hilbertDiagonal (T : ∀ i, E i →L[ℂ] E i) (M : ℝ) (hM : 0 ≤ M)
    (hT : ∀ i, ‖T i‖ ≤ M) : lp E 2 →L[ℂ] lp E 2 := by
  have hb (x : lp E 2) (i : ι) : ‖T i (x i)‖ ≤ ‖((M:ℂ) • x) i‖ := by
    change ‖T i (x i)‖ ≤ ‖(M:ℂ) • x i‖
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM]
    exact ((T i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))
  let L : lp E 2 →ₗ[ℂ] lp E 2 := {
    toFun x := ⟨fun i => T i (x i), (lp.memℓp ((M:ℂ) • x)).norm.mono (hb x)⟩
    map_add' x y := by ext i; exact map_add (T i) _ _
    map_smul' c x := by ext i; exact map_smul (T i) _ _ }
  refine L.mkContinuous M fun x => ?_
  have h := lp.norm_mono (x := L x) (y := (M:ℂ) • x) (by norm_num : (2 : ℝ≥0∞) ≠ 0) (hb x)
  simpa only [L, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM] using h

@[simp] theorem hilbertDiagonal_apply (T : ∀ i, E i →L[ℂ] E i) (M : ℝ) (hM : 0 ≤ M)
    (hT : ∀ i, ‖T i‖ ≤ M) (x : lp E 2) (i : ι) :
    hilbertDiagonal T M hM hT x i = T i (x i) := rfl
end DirectSum

end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/- Exact rational SOS data. All asserted computed identities reduce in the
   stock Lean kernel; the numerical program and these literals are untrusted. -/
namespace NuclearUltrapower.SL3Certificate
def q93 : List ℤ := [1160, -66, 358, 1118, 194, 379075, -274610, 407, -1013, -450, -1185, 706, 79542, -220454, 788, -172990, 5577, 79745, 477, -56303, -854, 285, -29812, 2835, 201972, -65789, 441, -66840, -176519, 54133, -10, 16022, -49146, -136, 15410, -647, 75521, -135690, 50004, 83647, -67560, 270513, -19891, -684, 50126, -10406, -47466, 27258, -404, 84363, 29, -16957, -3328, -5872, 897, -139, 61704, -134860, -2263, 107326, 241389, 14106, 41654, 173051, 217121, 66045, 34620, 284873, -9945, 69544, -755, 94525, 2832, -1104, -2236, -1171, -56556, -182201, -594, -48578, 19122, 15823, -36627, -36114, -431, -13443, -1376, -17894, 1928, 189926, -593, -167117, 228082, 101538, -182, 177, -1419, -20748, -604, 94127, -69940, -38, -1131, -172290, -69024, 44888, -24772, -10987, -152305, 4662, -6236, -16050, -447, 9967, 99143, 25215, 2222, 236, -2011, 147]
def q95 : List ℤ := [-1242, -542, -50, -155, -453, 240645, -194573, 147, 167, -171, -931, 988, 57149, -194508, -862, -28427, 8125, 228132, -240, -1232, -1176, 140, 5181, -56922, -34116, 125052, -772, 131330, 157712, -225086, 388, 9758, -66553, 1848, 9425, 1054, 63138, -42918, -306832, 111403, -38281, 124401, 0, 858, -22276, -274622, -60004, -95155, -278, -117521, -888, -163446, -1586, 208806, 33, -9288, -222336, -12198, 2038, -62411, -82157, -144386, -22453, -136513, 64963, -63365, -37383, -35638, -6032, 0, 0, 31861, -7, 1000, 379, -520, 71651, 0, -670, 3379, 341937, 11639, 61044, 60171, 0, 37944, 2, -148151, -4303, 92664, -418, -107333, -325347, 0, 223, -1030, -3870, 2115, 3148, -2929, 87768, 747, 97, -108346, 104833, 36183, -49646, 154258, -51227, -17158, 121498, -8060, 714, 8374, 80313, -38952, -1767, -35, 19, -287]
def q96 : List ℤ := [-272, -193, -689, -354, -97, 181074, -274610, 192, -341, 908, -1185, 626, 43294, -91025, -5, -169493, 93082, -88852, -496, -56303, 1232, -657, 96423, 47978, -92306, 341227, -249, -81595, 247714, 54133, -10, 72575, -100232, -1192, -38981, -742, 34920, 110184, -158474, 134208, -14185, 21146, -19891, -684, -42623, -272219, 46325, 25405, 443, 91235, 688, -16957, -5241, 119728, -2385, -218, -139622, 62345, 2360, 13963, 128631, -101539, -6721, -216214, -125120, -147582, 35617, 197936, -5368, 69544, -755, -243005, -1206, -844, 342, -487, -40784, -182201, -1445, -31623, 178472, -34867, -146168, 4712, -431, -13443, -1948, -157721, -9270, -126683, 50, 10553, -123556, 101538, 168, 2167, -1250, -1514, -413, -21246, -65831, -38, 1176, 34996, 128478, -110154, 137673, -192031, 37008, 15044, -100618, 48741, -2070, 848, -15193, 11183, -1022, -1086, 1520, -956]
def q97 : List ℤ := [701, -104, -1056, 323, -236, -210968, 274610, 139, 132, 124, -1109, 1315, 75165, 115097, -899, 78128, 46221, -63126, -537, -56303, 924, -624, -28095, 47583, 112437, -356847, -884, 63237, -256981, 54133, -10, -48922, -84184, 1010, -12840, -72, 62577, 112413, 237955, -99687, 113652, -76942, -19891, -684, -99073, 289961, 15450, 12422, -1097, 20945, 132, -16957, 284, -121525, -1142, 32302, -13130, -58765, 2146, 82471, -49496, -25913, 20691, 202483, 13127, 252529, 12443, -133215, -9959, 69544, -755, 148561, 210, 402, 2122, -509, 74653, 182201, -2008, -58851, -217566, -75705, -130261, 37106, -431, 13443, -3051, 65710, -9346, 142989, 210, -118044, 223337, 101538, 93, 770, -1590, -41363, 627, -94654, 58585, -38, 214, 8449, 150495, 165268, -70196, 47567, -21850, -51232, -69814, -16856, 1972, 5166, 47362, 3387, 1104, 1096, 605, -985]
def q98 : List ℤ := [678, 0, 0, -36, 0, 0, 0, 1012, 0, -2013, -2349, 1949, -128739, 4268, -685, 0, -158781, -107572, 0, 14841, 0, -1393, -85090, 116017, -34287, 0, 161, -39779, 42172, 74133, 180, -149362, 0, 508, -57341, 681, 1333, 0, 55448, 12721, -26192, 23558, -128151, 2156, 0, 50629, 0, 0, -212, 0, -4225, 67291, -8352, -80314, -2270, -7051, -78503, -122065, -401, 45396, 62833, -49005, 41275, -41016, -113662, 0, -10328, 0, 21532, 90551, -167, -41382, -1547, 191, -1062, 0, -117133, 0, 2963, 0, 97962, -9011, 48193, -22124, -27, 0, 1634, 0, -4322, -96138, -1576, 72125, -27567, -106959, 0, -2224, -10309, -41881, 5020, -774, -79857, -3261, -883, 21497, 0, -9824, 59502, -2234, 0, 0, 0, -2327, -3856, 3864, -108703, 0, -2820, -34, 1600, 0]
def q99 : List ℤ := [713, 119, 1455, 764, 151, 141519, 274610, 20, -157, -458, 534, 1332, -99121, -86285, -784, -111694, 12102, -9106, 502, -56303, 41, 371, 66611, 72898, 89740, -381377, 1310, 12045, -136891, 54133, -10, -20082, -18517, 1010, 23571, -124, 68701, 30560, -257750, 91736, -138848, -92494, 19891, -684, -96559, -249396, 38136, -33065, -628, -9752, 923, -16957, 4608, -113856, 1488, 33941, -11787, 72515, 97, 21747, -170051, -231892, -15718, 219138, -92001, -291898, 9556, -22353, -7360, -69544, 755, 98094, 3026, -367, 1895, 331, -97340, -182201, -2039, -148021, -197593, -37739, 182795, 31402, 431, 13443, -390, -11449, -7540, -63243, 544, 91840, 104526, -101538, 195, -798, -2669, -42591, -1280, 72882, -35315, -38, 46, 35377, 158764, -173423, -31391, -203018, -21202, -21682, -48421, -19028, 1822, -6004, -92412, 29101, -736, -850, -491, 999]
def g0 : List ℤ := [276726576341, -7158468946, -7158700808, 67943, 143683124409, 48398339509, -2112432855, -22603795307, -10173711233, -49221359593, -22603577948, -49221110918, 48397911061, -584106529928, 48397862720, -49220953326, -22603365175, -49221038044, -33595105247, -22603525174, -2112613445, 48397998398, -31146853137, -178089, -10370617592, 44817326883, -15710113406, -2112231710, 3525718952, -14631458507, -17927153224, 31388205025, -4715328105, 32770695042, -23154518737, 10370155384, 9509214253, 10370342674, -352634, -10370827745, 512550, -10370193209, 709723, 10370168783, 9509008655, 10370007391, -17926436965, -17926364819, -26688393082, 9509214227, -21997317929, 4934586101, -7158611935, 27131515001, -26688594389, 31388107505, 4935046968, 44817061578, -31146179104, 3524588985, 150554815730, 3525935281, -31146228448, 44816894413, 4934976534, 31387642853, -26688483839, 27131622053, -7158804393, 4933924037, -21996906631, 9509409248, -26688321670, -15709902083, -15709632313, 27131623222, -25072393716, 32771182256, -25072470360, -4715360261, -949092746, -4714913936, -25072279549, 32770570539, -25072429447, 27131475938, 6071507041, -10370551994, 46684, 31387946196, -17926531666, -14630766981, 3525950778, -2112708456, -15710126276, 44817029971, 32770776612, -4715113722, -31146478055, -618157, -14631282756, 46809448375, 46309104079, -31610400766, -31610781402, -74272, 46809143273, -43294372576, 46808982670, -73582, -31610613879, -31610993013, 2087038159, 46808742562, -14631002075, 174217, -2161, 155082088249, -21997008296, -21997216354, -168935]
end NuclearUltrapower.SL3Certificate
end

end OAI
end


