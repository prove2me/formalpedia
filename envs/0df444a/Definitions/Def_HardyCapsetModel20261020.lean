-- Prove2me | Definitions.Def_HardyCapsetModel20261020
-- name    : HardyCapsetModel20261020
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-20T13:30:35.967872+00:00
-- url     : https://prove2.me/theorems/7efa4c23-8b3f-4fea-be9e-115f70d138fc
-- title:
--   Exact 512-point cap and full-space hyperplane-completion model
-- statement:
--   The ambient space is the set of eight-tuples over ZMod 3. The baseline S is the image under big-endian ternary decoding of the complete explicit 512-entry input list. A cap has no three pairwise distinct members summing to zero. A hyperplane is given by a normal n and level t; theorem statements separately require n nonzero. The fixed core is S minus that hyperplane. The candidate pool ranges over the entire 6561-point ambient space and excludes the core and all points forming a zero-sum triple with two distinct core points. This definition contains no asserted upper bound and no proof placeholders. Baseline identity: SHA256(sorted ternary strings joined by LF without a trailing LF) = fa12b2dc4918c38248b3039df101b5bb66ee85fd56c313389015c64979d7fb88.
-- source:
--   Private local manuscript, 八维 cap 的超平面补点定理, 2026-10-13, sections 2, 3 and 5.1; F:/Hardy_CapSet_2026-10-12/share/CapSet_Hyperplane_2026-10-13; baseline_points.json, exact complete coordinates.

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace HardyCapset20261020

abbrev Point := Fin 8 → ZMod 3

/-- Big-endian ternary decoding; the first coordinate is the most significant. -/
def decode (q : ℕ) : Point := fun i => (((q / 3 ^ (7 - i.val)) % 3 : ℕ) : ZMod 3)

def baselineIds : List ℕ := [277, 278, 280, 281, 285, 289, 290, 294, 304, 305, 307, 308, 312, 316, 317, 321, 340, 341, 349, 350, 352, 353, 357, 379, 380, 384, 421, 422, 430, 431, 433, 434, 438, 460, 461, 465, 517, 518, 523, 524, 525, 532, 533, 534, 544, 545, 550, 551, 552, 559, 560, 561, 580, 581, 589, 590, 595, 596, 597, 622, 623, 624, 661, 662, 670, 671, 676, 677, 678, 703, 704, 705, 761, 764, 767, 768, 771, 776, 777, 780, 788, 791, 794, 795, 798, 803, 804, 807, 824, 827, 833, 836, 839, 840, 843, 866, 867, 870, 905, 908, 914, 917, 920, 921, 924, 947, 948, 951, 1001, 1005, 1028, 1032, 1064, 1068, 1073, 1077, 1145, 1149, 1154, 1158, 1244, 1245, 1271, 1272, 1307, 1308, 1316, 1317, 1388, 1389, 1397, 1398, 1489, 1492, 1495, 1497, 1500, 1504, 1506, 1509, 1516, 1519, 1522, 1524, 1527, 1531, 1533, 1536, 1552, 1555, 1561, 1564, 1567, 1569, 1572, 1594, 1596, 1599, 1633, 1636, 1642, 1645, 1648, 1650, 1653, 1675, 1677, 1680, 1729, 1734, 1756, 1761, 1792, 1797, 1801, 1806, 1873, 1878, 1882, 1887, 1972, 1974, 1999, 2001, 2035, 2037, 2044, 2046, 2116, 2118, 2125, 2127, 2200, 2201, 2203, 2204, 2209, 2210, 2212, 2213, 2272, 2273, 2275, 2276, 2314, 2315, 2316, 2319, 2341, 2342, 2343, 2346, 2353, 2354, 2356, 2357, 2386, 2387, 2388, 2391, 2413, 2414, 2415, 2418, 2437, 2438, 2445, 2454, 2517, 2556, 2583, 2598, 2628, 2655, 2677, 2678, 2685, 2694, 2757, 2799, 2826, 2838, 2871, 2898, 2921, 2924, 2927, 2936, 2999, 3042, 3069, 3080, 3114, 3141, 3161, 3165, 3168, 3177, 3240, 3280, 3281, 3283, 3289, 3307, 3308, 3310, 3316, 3321, 3361, 3370, 3371, 3373, 3388, 3397, 3398, 3400, 3404, 3405, 3411, 3420, 3483, 3523, 3526, 3527, 3535, 3550, 3553, 3554, 3562, 3564, 3607, 3613, 3616, 3617, 3634, 3640, 3643, 3644, 3649, 3652, 3655, 3664, 3727, 3771, 3798, 3808, 3843, 3870, 3889, 3894, 3897, 3906, 3969, 4009, 4010, 4013, 4019, 4036, 4037, 4040, 4046, 4050, 4091, 4099, 4100, 4103, 4118, 4126, 4127, 4130, 4132, 4134, 4140, 4149, 4212, 4253, 4255, 4256, 4265, 4280, 4282, 4283, 4292, 4293, 4337, 4343, 4345, 4346, 4364, 4370, 4372, 4373, 4387, 4388, 4390, 4391, 4396, 4397, 4399, 4400, 4459, 4460, 4462, 4463, 4501, 4502, 4503, 4506, 4528, 4529, 4530, 4533, 4540, 4541, 4543, 4544, 4573, 4574, 4575, 4578, 4600, 4601, 4602, 4605, 4624, 4625, 4632, 4641, 4704, 4743, 4770, 4785, 4815, 4842, 4864, 4865, 4872, 4881, 4944, 4986, 5013, 5025, 5058, 5085, 5108, 5111, 5114, 5123, 5186, 5229, 5256, 5267, 5301, 5328, 5348, 5352, 5355, 5364, 5427, 5467, 5468, 5470, 5476, 5494, 5495, 5497, 5503, 5508, 5548, 5557, 5558, 5560, 5575, 5584, 5585, 5587, 5591, 5592, 5598, 5607, 5670, 5710, 5713, 5714, 5722, 5737, 5740, 5741, 5749, 5751, 5794, 5800, 5803, 5804, 5821, 5827, 5830, 5831, 5836, 5839, 5842, 5851, 5914, 5958, 5985, 5995, 6030, 6057, 6076, 6081, 6084, 6093, 6156, 6196, 6197, 6200, 6206, 6223, 6224, 6227, 6233, 6237, 6278, 6286, 6287, 6290, 6305, 6313, 6314, 6317, 6319, 6321, 6327, 6336, 6399, 6440, 6442, 6443, 6452, 6467, 6469, 6470, 6479, 6480, 6524, 6530, 6532, 6533, 6551, 6557, 6559, 6560]

/-- The exact 512-point input, not an arbitrary cap of that size. -/
def baseline : Finset Point := (baselineIds.map decode).toFinset

def IsCap (A : Finset Point) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A,
    a ≠ b → a ≠ c → b ≠ c → a + b + c ≠ 0

def hyperplane (n : Point) (t : ZMod 3) : Finset Point :=
  Finset.univ.filter (fun x => (∑ i, n i * x i) = t)

def core (n : Point) (t : ZMod 3) : Finset Point :=
  baseline \ hyperplane n t

/-- All points of the ambient space compatible with every pair of fixed points. -/
def pool (F : Finset Point) : Finset Point :=
  Finset.univ.filter (fun q => q ∉ F ∧
    ∀ a ∈ F, ∀ b ∈ F, a ≠ b → a + b + q ≠ 0)

end HardyCapset20261020


