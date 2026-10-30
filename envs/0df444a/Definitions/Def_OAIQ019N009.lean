-- Prove2me | Definitions.Def_OAIQ019N009
-- name    : OAIQ019N009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:58:49.312824+00:00
-- url     : https://prove2.me/theorems/00460365-da08-447c-ae66-ee4a7c9b9312
-- title:
--   Definitions bundle OAIQ019N009 of the split of OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.NuclearUltrapower.main_no_embedding`, carved from OpenAI's openai/math development (OpenAI, *An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292)*, OpenAI Math Release, September 23, 2026, result family 292, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 13 definitions and 1 theorem. The definitions and types are `OAI.NuclearUltrapower.SL3Certificate.q49`, `OAI.NuclearUltrapower.SL3Certificate.q5`, `OAI.NuclearUltrapower.SL3Certificate.q50`, `OAI.NuclearUltrapower.SL3Certificate.q51`, `OAI.NuclearUltrapower.SL3Certificate.q52`, `OAI.NuclearUltrapower.SL3Certificate.q53`, `OAI.NuclearUltrapower.SL3Certificate.q54`, `OAI.NuclearUltrapower.SL3Certificate.q55`, `OAI.NuclearUltrapower.SL3Certificate.q56`, `OAI.NuclearUltrapower.SL3Certificate.q57`, `OAI.NuclearUltrapower.complementPoly`, `OAI.NuclearUltrapower.instPartialOrder_solutions`, `OAI.NuclearUltrapower.mixedTensorOperator`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: [`NuclearUltrapower_InitialMatching`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/InitialMatching.lean), [`NuclearUltrapower_NuclearFiniteness`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/NuclearFiniteness.lean), [`NuclearUltrapower_SOSCertificate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/SOSCertificate.lean), [`NuclearUltrapower_Schur`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/NuclearUltrapower/Schur.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ019N041`.
-- source:
--   OpenAI, An explicit obstruction to nuclear norm-ultrapower embeddings (result family 292), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 292; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/NuclearUltrapower.lean; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Schur
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
universe u v w
noncomputable section
open scoped TensorProduct InnerProductSpace
open Module.End
noncomputable section
open scoped CStarAlgebra
noncomputable section
open Filter
open scoped Topology ENNReal
noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower

open scoped TensorProduct
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {Γ : Type u} [Group Γ]

section MixedTensor
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The finite-rank operator represented by a rectangular Hilbert tensor. -/
def mixedTensorOperator : E ⊗[ℂ] StrongDual ℂ F →ₗ[ℂ] (F →L[ℂ] E) :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun f => f.smulRight x
          map_add' := by intro f g; ext v; simp [add_smul]
          map_smul' := by intro c f; ext v; simp [mul_smul] }
      map_add' := by intro x y; ext f v; simp [smul_add]
      map_smul' := by intro c x; ext f v; simp [smul_smul, mul_comm] }

omit [CompleteSpace F] in
@[simp] theorem mixedTensorOperator_tmul (x : E) (f : StrongDual ℂ F) (v : F) :
    mixedTensorOperator (x ⊗ₜ[ℂ] f) v = f v • x := rfl

end MixedTensor

end NuclearUltrapower

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_NuclearFiniteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
universe u v
open Filter
open scoped InnerProductSpace TensorProduct Topology ENNReal ComplexOrder
namespace NuclearUltrapower
section ComplementEvaluation
variable {Γ B C D A : Type*} [CStarAlgebra B] [CStarAlgebra C] [CStarAlgebra D]
  [CStarAlgebra A]

def complementPoly (S : Finset Γ) (z w : Γ → A) : A :=
  (2 * (S.card : ℂ)) • 1 + ∑ g ∈ S, (z g * w g + star (z g) * star (w g))

end ComplementEvaluation
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_InitialMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v

section Bounds
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → unitary B)
local instance instPartialOrder_solutions : PartialOrder B := CStarAlgebra.spectralOrder B
end Bounds
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
def q5 : List ℤ := [-1661, 648, -314, -47, -357, 247102, 194573, 1265, -14, -661, 804, 578, 12947, -116412, 579, -31220, -74071, 52014, 111, -1232, 715, -432, 5127, 119211, -229194, 111004, -826, 55301, 13047, -225086, 388, -83879, 3562, -788, 47397, -1116, 84879, -79063, 270538, 161018, 204766, -163851, 0, 858, 39492, 174451, 53009, -100571, -625, -116468, 944, -163446, 1123, -93839, 312, -18877, 101931, 186930, -2333, -49746, 19189, 264258, 17698, 119156, -328608, 91772, 33757, 19260, -4930, 0, 0, -102950, 887, -764, -218, -1023, 233394, 0, -351, -4372, -114709, 31797, -110771, -38248, 0, -37944, 123, -135797, 7514, 6534, 88, 49414, -296265, 0, -12, 510, -3700, -5511, -611, 3023, -62137, 747, -807, 3562, 102994, -97537, 77373, -204630, -86131, -4994, 101734, -15166, 1447, -5782, 12412, 26464, 3328, -152, -571, -394]
def q49 : List ℤ := [1219, -154, -74, 1111, 41, -357401, -274610, -161, 751, 717, -896, 472, -41727, -136548, 557, 223617, -35864, 33089, -844, -56303, -702, 130, -96020, -57876, -258061, -14537, 1100, 55932, -226555, 54133, -10, 92906, 61125, -133, -25714, -62, 60835, 119014, -84696, 160154, 20358, 266287, 19891, -684, 55795, -848, 4592, -10741, -849, 15133, -722, -16957, 3875, 9871, -1266, 23093, -108383, 134626, 2450, 87916, -180481, 99928, -38650, 179707, -194981, 65355, -6318, 234363, 26912, -69544, 755, 80812, 1198, -373, -2050, -1315, 91995, 182201, -480, 72708, 97414, 61936, 188962, -29673, 431, -13443, -2909, -163211, 4938, 41314, -645, -83232, 152863, -101538, -223, -212, 1063, -29961, 646, -22996, 33207, -38, 1246, 133830, -43801, -37731, 113923, -169632, -150328, 53678, 59016, -5625, 202, -8644, -70629, 83207, -2245, 268, 2041, 6]
def q50 : List ℤ := [625, 0, 0, 866, 0, 0, 0, -606, 0, 164, -167, 2674, -23157, 14801, -144, 0, -75166, 38921, 0, 101741, 0, -1362, 86776, -16823, 61150, 0, 907, -48820, 1614, 32833, 1682, 80998, 0, 373, -68727, -792, 7296, 0, -56473, 16661, 866, 24260, 28406, -1812, 0, 84124, 0, 0, -2035, 0, 260, 68543, -3851, -53927, 6152, -72314, -9586, 107424, -5659, -16077, -34416, 2678, -32964, 11903, 35722, 0, 48078, 0, -620, 70576, -3607, -61857, -2251, 3489, -4296, 0, -8674, 0, 2162, 0, 12470, -61276, -37647, 55460, 336, 0, 2408, 0, -2604, 2221, 276, 3830, -31629, -87280, 0, 3335, 3567, -30976, 4247, -147192, -114164, -332, 1915, -97965, 0, 28192, 40048, 45793, 0, 0, 0, -27211, 7270, -11234, 114873, 0, -2380, -269, -1331, 0]
def q51 : List ℤ := [-108, 0, 0, -1517, 0, 0, 0, 105, 0, 162, -185, 462, -2580, -1279492, -142, 0, 9605, 186054, 0, 28443, 0, 1220, 18745, -4021, 86998, 0, 1002, -11670, -139537, 112964, -297, 9024, 0, -64, -19344, -875, 1744, 0, 122451, -160341, 57985, -52603, 20481, 1381, 0, 119684, 0, 0, -22, 0, 3, 522129, -2402, 123269, 1765, 8182, -641892, -245554, 1246, -1076571, -48964, -231518, 4380, -114549, -750705, 0, -5440, 0, 70, 625789, 740, 134126, 302, 37, -1233, 0, -41464, 0, 880, 0, -262054, 7830, -34333, 15609, 408, 0, -323, 0, -1624, 2025, -248, -36862, 423788, -6248, 0, -447, -786, 4116, -767, -31796, -12719, 2371, 331, -12078, 0, 3476, 4937, -613565, 0, 0, 0, 3616, -1314, -7008, -14680, 0, 430, 471, -542, 0]
def q52 : List ℤ := [769, 0, 0, 1280, 0, 0, 0, -746, 0, -995, -425, -2598, 26048, -86781, 872, 0, 110562, 43313, 0, 72852, 0, 2388, 89446, 40249, -46710, 0, 2304, 116806, -9464, -52990, -2326, -91110, 0, 459, -83399, -2012, -17457, 0, 23859, -41803, -4416, -10250, 28704, -988, 0, -64259, 0, 0, 187, 0, -24, -87386, 2350, -80250, -1064, -93767, 48884, 159859, 6032, 81987, 26289, -15703, 48654, -29865, 75838, 0, 62341, 0, -804, 80682, 203, 26134, 333, -320, 743, 0, -9653, 0, 1028, 0, 26473, 90131, -81471, 67300, -1939, 0, -356, 0, 1589, 4806, -485, -9610, 68524, -105235, 0, -493, -3803, 45718, 3715, -151721, 128417, -500, -1861, 34213, 0, -9846, -13986, -99209, 0, 0, 0, 40162, 6359, 6857, -168967, 0, -2082, -398, -633, 0]
def q53 : List ℤ := [-90, -229, -453, 1111, -148, -109808, -274610, -934, -898, 717, 625, 472, 30912, -137564, 557, -329556, 97145, 33089, -559, -56303, 1419, 130, -96020, 74121, 159817, 239346, 370, -8789, 196661, 54133, -10, -55080, 95362, 806, -25714, -1220, -67881, -117071, -8053, 184521, -22118, -226444, 19891, -684, 25560, -134307, -43914, -11107, 790, -84112, 730, -16957, -7488, 9871, -1266, 15080, 127869, 134626, 2450, -55234, 235774, -149527, -17073, 66533, -194981, 65243, -19061, 5979, -26585, -69544, 755, -182403, 933, 474, -2050, 94, 91995, 182201, -480, 19684, 97414, -11979, 188962, -29673, 431, -13443, 629, 285557, -7380, 41314, -645, 162471, 152863, -101538, -31, -2946, 1063, -22400, 415, -22996, -86521, -38, 1246, 23164, -73813, -7447, -178103, -169632, 66841, -31080, -134477, -40372, 1613, -1895, -23025, -50373, 1651, 268, 2041, -396]
def q54 : List ℤ := [-678, 0, 0, 36, 0, 0, 0, -1012, 0, -2013, -2349, -1949, -128739, -4268, -685, 0, 158781, 107572, 0, 14841, 0, -1393, 85090, -116017, -34287, 0, 161, 39779, -42172, 74133, 180, -149362, 0, -508, -57341, 681, -1333, 0, -55448, -12721, -26192, -23558, 128151, 2156, 0, 50629, 0, 0, 212, 0, 4225, 67291, 8352, -80314, -2270, 7051, -78503, -122065, 401, 45396, 62833, 49005, 41275, 41016, -113662, 0, 10328, 0, -21532, -90551, 167, 41382, -1547, -191, -1062, 0, 117133, 0, -2963, 0, 97962, 9011, 48193, -22124, 27, 0, 1634, 0, 4322, -96138, -1576, -72125, 27567, 106959, 0, -2224, 10309, -41881, 5020, 774, -79857, -3261, 883, 21497, 0, -9824, 59502, 2234, 0, 0, 0, -2327, -3856, -3864, 108703, 0, -2820, 34, -1600, 0]
def q55 : List ℤ := [1242, -542, -50, 155, -453, 240645, 194573, -147, -167, -171, -931, -988, 57149, 194508, -862, -28427, -8125, -228132, 240, -1232, -1176, 140, -5181, 56922, -34116, 125052, -772, -131330, -157712, -225086, 388, 9758, 66553, -1848, 9425, 1054, -63138, 42918, 306832, -111403, -38281, -124401, 0, 858, -22276, -274622, 60004, 95155, 278, -117521, 888, -163446, 1586, 208806, 33, 9288, -222336, -12198, -2038, -62411, -82157, 144386, -22453, 136513, 64963, 63365, 37383, 35638, 6032, 0, 0, -31861, -7, -1000, 379, -520, -71651, 0, 670, -3379, 341937, -11639, 61044, 60171, 0, -37944, 2, 148151, 4303, 92664, -418, 107333, 325347, 0, 223, -1030, 3870, 2115, 3148, 2929, 87768, 747, -97, -108346, 104833, 36183, -49646, -154258, -51227, 17158, 121498, -8060, 714, -8374, -80313, -38952, -1767, 35, -19, 287]
def q56 : List ℤ := [84, 0, 0, 1167, 0, 0, 0, 125, 0, -204, -1287, -518, 9565, 86142, -69, 0, -15835, -128936, 0, 28443, 0, -824, -36909, 11792, 60950, 0, 88, -4043, 851167, 112964, -297, 11097, 0, 63, 23190, 373, 135, 0, 143444, -30381, 348182, 60944, 20481, 1381, 0, -90000, 0, 0, -2, 0, -43, 522129, 6230, 151022, -1950, -2782, 1043554, 229531, 57, -603454, -111695, -989073, -4920, 97956, 602298, 0, -4076, 0, 8497, 625789, 740, -107056, 308, 2, -912, 0, -140396, 0, -909, 0, -519103, -899, 15413, 8947, 408, 0, -325, 0, 3224, -30746, -933, -172253, -743257, -6248, 0, 442, 1472, 4992, 1145, -336, 5933, 2371, 235, 4534, 0, -2072, 12549, -60229, 0, 0, 0, 277, -880, -2883, -10841, 0, -643, 1078, -491, 0]
def q57 : List ℤ := [-1433, 644, 273, 155, -363, -130039, 194573, -139, -225, -171, -1243, -988, 32870, -220730, -862, -238749, -78522, -228132, -315, -1232, 1182, 140, -5181, 124211, 193767, -21089, 921, 69225, -101388, -225086, 388, 94681, -29969, 1705, 9425, -424, 65219, 41720, 12885, 114021, -53579, 260238, 0, 858, -35280, 38877, -65700, 25310, -183, 75827, 998, -163446, 8789, 208806, 33, -1971, -52985, -12198, -2038, 221620, -210414, 156693, -1303, -144954, 64963, -38353, -26666, -151554, -28376, 0, 0, -206753, -706, 915, 379, 428, -71651, 0, 670, -60366, 341937, 6722, 61044, 60171, 0, -37944, 750, 52861, 1066, 92664, -418, -92490, 325347, 0, -35, 6, 3870, 21990, 622, 2929, -31929, 747, -97, 49203, -149870, -9156, -114053, -154258, -48840, 89399, 59410, 9399, -3610, 3574, 20993, 93970, -351, 35, -19, 132]
end NuclearUltrapower.SL3Certificate
end

end OAI
end


