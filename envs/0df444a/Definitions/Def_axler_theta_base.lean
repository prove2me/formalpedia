-- Prove2me | Definitions.Def_axler_theta_base
-- name    : axler_theta_base
-- status  : Definition
-- author  : @andreaskapfer
-- created : 2026-10-01T16:42:23.994267+00:00
-- url     : https://prove2.me/theorems/1b58981f-97d7-4cfd-82c8-3b9ce6bf5455
-- title:
--   Axler theta certificate base computations
-- statement:
--   Certificate infrastructure for the Rosser-Schoenfeld style theta bound chain (Axler).
-- source:
--   Axler, Elementary proof of the Chebyshev theta bounds, internal certificate modules.

import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Ring.GeomSum
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.Order.Floor.Div

set_option autoImplicit false
set_option Elab.async false

open Finset

-- Source: Solutions/RosserCompute.lean
/-! Pure natural-number computations for the Rosser--Schoenfeld certificate.
Numerical certificate modules import only this file; real analysis and
correctness proofs remain in the separate proof modules. -/

namespace RosserBitSieve


def periodicMask (d count : ℕ) : ℕ :=
  (2 ^ (d * count) - 1) / (2 ^ d - 1)

def divisorMask (a len d : ℕ) : ℕ :=
  periodicMask d ((len + d - 1) / d) * 2 ^ ((d - a % d) % d)

def compositeMask (divisors : List ℕ) (a len : ℕ) : ℕ :=
  divisors.foldl (fun mask d => mask ||| divisorMask a len d) 0

def candidateMask (divisors : List ℕ) (a len : ℕ) : ℕ :=
  (2 ^ len - 1) ^^^ (compositeMask divisors a len % 2 ^ len)

/-- Enumerate a bit interval by halving it, skipping empty subtrees. -/
def enumBits : ℕ → ℕ → ℕ → List ℕ
  | 0, start, mask => if mask % 2 == 1 then [start] else []
  | depth + 1, start, mask =>
    if mask == 0 then [] else
    let half := 2 ^ depth
    enumBits depth start (mask % 2 ^ half) ++
      enumBits depth (start + half) (mask / 2 ^ half)

def offsets (divisors : List ℕ) (depth a len : ℕ) : List ℕ :=
  enumBits depth 0 (candidateMask divisors a len)

/-- Reuse one sieve mask for many short blocks. Offsets here start at one. -/
def windowOffsets (depth mask shift len : ℕ) : List ℕ :=
  (enumBits depth 0 (mask / 2 ^ shift % 2 ^ len)).map (· + 1)

end RosserBitSieve

namespace AlternativeProductMoments


def firstMoment (ds : List ℕ) : ℕ := ds.sum

def secondMoment (ds : List ℕ) : ℕ := (ds.map (fun (d : ℕ) => d ^ 2)).sum

def lowerNumerator (a : ℕ) (ds : List ℕ) : ℕ :=
  ds.length * a - firstMoment ds

def upperNumerator (a : ℕ) (ds : List ℕ) : ℕ :=
  ds.length * a ^ 2 - a * firstMoment ds + secondMoment ds

def pairNumerator (a : ℕ) (ds : List ℕ) : ℕ :=
  lowerNumerator a ds ^ 2 - ds.length * a ^ 2

def factorNumerator (a : ℕ) (ds : List ℕ) : ℕ :=
  (a ^ 3 - upperNumerator a ds) * (2 * a ^ 4 + pairNumerator a ds)

def factorDenominator (a : ℕ) : ℕ := 2 * a ^ 7

/-- One downward-rounded update for a whole candidate block. -/
def momentStep (v a : ℕ) (ds : List ℕ) : ℕ :=
  v * factorNumerator a ds / factorDenominator a

end AlternativeProductMoments

namespace RosserBitMoments

open RosserBitSieve AlternativeProductMoments

@[ext] structure Moments where
  count : ℕ
  first : ℕ
  second : ℕ
  deriving DecidableEq, Repr

def moments (ds : List ℕ) : Moments :=
  ⟨ds.length, ds.sum, (ds.map (fun (d : ℕ) => d ^ 2)).sum⟩

def merge (s t : Moments) : Moments :=
  ⟨s.count + t.count, s.first + t.first, s.second + t.second⟩

def translate (offset : ℕ) (s : Moments) : Moments :=
  ⟨s.count, s.first + offset * s.count,
    s.second + 2 * offset * s.first + offset ^ 2 * s.count⟩

def packedTable : ℕ := 18472300896970103792108295030754343311462210589054640814582099618958825816112921765637552819554960025580043253363337196071510397018042133440073613070599528214959555081087759177994513208873881398958301422300628985358844335629703824674989009933744813385983504668349668413339407645329016240118311102009327559169919361752210702429893649728293932236557803946372391347786424282478245140012004923246019750498074272682481869124019625063780294997972415480522849467413156748308598193741959980512364680419185912142662080168720543223372130422252685000667222028691552391144914476582653820543415241442522565567827850971540414084963023662461454138479593909733901640282571543659792227281002640358593405226625400471739963595439608037996346958976031522266509217418626068981435972643586956604265934825153588078474541062083601584565110669452202573339800164169103872550900181154149463648375952255080306757167758906906382736410940812007907700484645358916007966298027371443379797534272791198303638115965305949698405311795153919406852986359475633446763175764573556098103639551525890208319167226087125167594382204144161586295123540456912808096572570872821701693833155843103822148960692081668132802646373741121271338591023149542977379459365527447593127745781442122554270427974619422849735484296339832731170084457029930842499657049873841177855047761694425403274812125429077333590092198933962090340380251846202809362383975418479306463890842278375332614640909801129604954946001702919968537917515644728884667828251078535570507012846902588218779713741378512607411980300476879133811456575684021346503785234617675182982977540462331832399895301441454472653688500254658691068207975085644854631617042755709815233293970628383901959051862306499230180026929443703650068362443283922131960509713762221413633617444652901862094089062362383582693974422591379320268703353694406511098994725224448

def byteMoments (byte : ℕ) : Moments :=
  if byte == 0 then ⟨0, 0, 0⟩ else
  if byte &&& (byte - 1) == 0 then
    let bit := Nat.log2 byte
    ⟨1, bit, bit ^ 2⟩
  else
    let word := packedTable / 2 ^ (24 * byte) % 2 ^ 24
    ⟨word % 256, word / 256 % 256, word / 65536 % 256⟩

/-- Depth d represents 2^(d+3) bits. Empty subtrees are skipped. -/
def fastMoments : ℕ → ℕ → ℕ → Moments
  | 0, start, mask => translate start (byteMoments (mask % 256))
  | depth + 1, start, mask =>
    if mask == 0 then ⟨0, 0, 0⟩ else
    let half := 2 ^ (depth + 3)
    merge (fastMoments depth start (mask % 2 ^ half))
      (fastMoments depth (start + half) (mask / 2 ^ half))

def windowMoments (mask shift len : ℕ) : Moments :=
  fastMoments 10 1 (mask / 2 ^ shift % 2 ^ len)

def stepFromMoments (v a : ℕ) (s : Moments) : ℕ :=
  let ell := s.count * a - s.first
  let u := s.count * a ^ 2 - a * s.first + s.second
  let e := ell ^ 2 - s.count * a ^ 2
  v * ((a ^ 3 - u) * (2 * a ^ 4 + e)) / (2 * a ^ 7)

def fastMomentStep (v a mask shift len : ℕ) : ℕ :=
  stepFromMoments v a (windowMoments mask shift len)

end RosserBitMoments

namespace RosserLogCertificate


def scale : ℕ := 2 ^ 64

/-- `p` represents the current odd power, `q` the squared series argument. -/
def seriesRun (D q : ℕ) : ℕ → ℕ → ℕ → ℕ
  | _, _, 0 => 0
  | j, p, terms + 1 => p / (2 * j + 1) +
      seriesRun D q (j + 1) (p * q / D) terms

def atanhLower (num den : ℕ) : ℕ :=
  let z := num * scale / den
  let q := z * z / scale
  2 * seriesRun scale q 0 z 12

/-- One shared constant, checked from the same twelve-term integer algorithm. -/
def logTwoLower : ℕ := 12786308645200714054

def logLower (n : ℕ) : ℕ :=
  let k := Nat.log2 n
  let t := 2 ^ k
  k * logTwoLower + atanhLower (n - t) (n + t)

end RosserLogCertificate

namespace RosserBlockCheck

open RosserLogCertificate

def sqrtUpper (b : ℕ) : ℕ := Nat.sqrt b + 1

def check (a b v : ℕ) : Bool :=
  decide (0 < v ∧
    scale * scale * 10 ^ 8 * sqrtUpper b <
      v * 178107239 * (logLower a * sqrtUpper b + 2 * scale))

end RosserBlockCheck

namespace RosserScan

open RosserBitSieve AlternativeProductMoments RosserLogCertificate RosserBlockCheck RosserBitMoments

/-- Force a natural-number state before the next recursive call. This avoids
re-evaluating a growing expression during kernel reduction. -/
def forceNat {α : Type} (n : ℕ) (f : ℕ → α) : α :=
  match n with
  | 0 => f 0
  | n + 1 => f (n + 1)

def stepOffsets (base mask a b : ℕ) : List ℕ :=
  windowOffsets 13 mask (a - base) (b - a)

def stepCheck (a b v : ℕ) (ds : List ℕ) : Bool :=
  decide (2 ≤ a ∧ a < b ∧ b - a ≤ 2 ^ 13 ∧
    firstMoment ds ≤ ds.length * a ∧ upperNumerator a ds ≤ a ^ 3) &&
      check a b (momentStep v a ds)

def stepData (base mask a b v : ℕ) : Bool × ℕ :=
  let s := windowMoments mask (a - base) (b - a)
  let w := stepFromMoments v a s
  (decide (2 ≤ a ∧ a < b ∧ b - a ≤ 2 ^ 13 ∧
    s.first ≤ s.count * a ∧ s.count * a ^ 2 - a * s.first + s.second ≤ a ^ 3) &&
      check a b w, w)

/-- Try a block, halving its width if the numerical test does not pass. -/
def attempt (base top mask a v : ℕ) : ℕ → ℕ → Option (ℕ × ℕ)
  | 0, _ => none
  | fuel + 1, width =>
    let b := min top (a + width)
    let data := stepData base mask a b v
    if data.1 then some (b, data.2)
    else attempt base top mask a v fuel (width / 2)

def run (base top mask : ℕ) : ℕ → ℕ → ℕ → Option ℕ
  | 0, a, v => if a == top then some v else none
  | fuel + 1, a, v =>
    if a == top then some v else
    match attempt base top mask a v 20 (max 1 (Nat.sqrt a / 2)) with
    | none => none
    | some (b, w) => forceNat b (fun b => forceNat w (fun w => run base top mask fuel b w))

end RosserScan

namespace RosserSieveData

open RosserBitSieve RosserScan

def divisors : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593, 2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797, 3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989, 4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177, 4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397, 4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597, 4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799, 4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999, 5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197, 5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399, 5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591, 5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791, 5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987, 6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199, 6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397, 6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599, 6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793, 6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997, 7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193, 7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393, 7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591, 7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793, 7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993, 8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191, 8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389, 8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599, 8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783, 8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999, 9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199, 9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397, 9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587, 9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791, 9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973]

def smallDivisors (base : ℕ) := divisors.filter (fun d => decide (d ≤ base))

def mask (base top : ℕ) := candidateMask (smallDivisors base) (base + 1) (top - base)

def segment (base top v : ℕ) :=
  forceNat (mask base top) (fun m => run base top m 4096 base v)

end RosserSieveData

-- Source: Solutions/RosserProductBlocks.lean
/-!
Reusable, kernel-checked parts of a block certificate for Rosser--Schoenfeld.
This module does not assert the target on [4500, 10^8]. In particular, it does
not trust the Python sieve or import any open platform theorem.
-/

namespace RosserProductCertificate

noncomputable def eulerProduct (n : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE n, (p : ℝ) / ((p : ℝ) - 1)

theorem eulerProduct_mono : Monotone eulerProduct := by
  intro a b hab
  apply Finset.prod_le_prod_of_subset_of_one_le (Nat.primesLE_mono hab)
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    exact div_nonneg (by positivity) (by linarith)
  · intro p hp _
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    apply (le_div_iff₀ (by linarith : (0 : ℝ) < p - 1)).mpr
    linarith

/-- A single comparison closes every real x in [a, B]. The square-root
term is bounded at B, while the logarithm is bounded at a. -/
theorem block_bound (B : ℕ) (a x U g L S : ℝ)
    (ha : 1 ≤ a) (hax : a ≤ x) (hxB : x ≤ B)
    (hU : eulerProduct B ≤ U)
    (hg : g ≤ Real.exp Real.eulerMascheroniConstant)
    (hL0 : 0 ≤ L) (hL : L ≤ Real.log a)
    (hS : 0 < S) (hBS : (B : ℝ) ≤ S ^ 2)
    (hcheck : U < g * (L + 2 / S)) :
    eulerProduct ⌊x⌋₊ <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  have hxpos : 0 < x := by linarith
  have hlog : L ≤ Real.log x := hL.trans (Real.log_le_log (by linarith) hax)
  have hsqrt : Real.sqrt x ≤ S :=
    Real.sqrt_le_iff.mpr ⟨hS.le, hxB.trans hBS⟩
  have hdiv : (2 : ℝ) / S ≤ 2 / Real.sqrt x :=
    div_le_div_of_nonneg_left (by norm_num) (Real.sqrt_pos.mpr hxpos) hsqrt
  have hbase : 0 ≤ L + 2 / S := by positivity
  calc
    eulerProduct ⌊x⌋₊ ≤ eulerProduct B := eulerProduct_mono (Nat.floor_le_of_le hxB)
    _ ≤ U := hU
    _ < g * (L + 2 / S) := hcheck
    _ ≤ Real.exp Real.eulerMascheroniConstant * (L + 2 / S) :=
      mul_le_mul_of_nonneg_right hg hbase
    _ ≤ Real.exp Real.eulerMascheroniConstant * (Real.log x + 2 / Real.sqrt x) :=
      mul_le_mul_of_nonneg_left (add_le_add hlog hdiv) (Real.exp_pos _).le
    _ = _ := by ring

/-- Integer update for a downward-rounded reciprocal product. -/
def downStep (v p : ℕ) : ℕ := v * (p - 1) / p

/-- Rounding down preserves a lower bound for the reciprocal product. -/
theorem downStep_sound (D v p : ℕ) (Q : ℝ)
    (hD : 0 < D) (hp : 2 ≤ p) (hv : (v : ℝ) / D ≤ Q) :
    (downStep v p : ℝ) / D ≤ Q * (((p : ℝ) - 1) / p) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hround : (downStep v p : ℝ) ≤ (v : ℝ) * (p - 1) / p := by
    simpa [downStep, Nat.cast_mul, hcast] using
      (Nat.cast_div_le (m := v * (p - 1)) (n := p) (α := ℝ))
  calc
    (downStep v p : ℝ) / D ≤ ((v : ℝ) * (p - 1) / p) / D :=
      div_le_div_of_nonneg_right hround hD'.le
    _ = ((v : ℝ) / D) * ((p - 1) / p) := by ring
    _ ≤ Q * ((p - 1) / p) :=
      mul_le_mul_of_nonneg_right hv (div_nonneg (by linarith) (by linarith))

/-- The rounding invariant for an entire list, including repeated or composite
entries. A separate coverage proof connects this list to the target primes. -/
theorem downRun_sound (ps : List ℕ) (D v : ℕ) (Q : ℝ)
    (hD : 0 < D) (hps : ∀ p ∈ ps, 2 ≤ p) (hv : (v : ℝ) / D ≤ Q) :
    ((ps.foldl downStep v : ℕ) : ℝ) / D ≤
      Q * (ps.map (fun (p : ℕ) => ((p : ℝ) - 1) / p)).prod := by
  induction ps generalizing v Q with
  | nil => simpa using hv
  | cons p ps ih =>
    have hp : 2 ≤ p := hps p (by simp)
    have htail : ∀ q ∈ ps, 2 ≤ q := by
      intro q hq
      exact hps q (by simp [hq])
    have hstep := downStep_sound D v p Q hD hp hv
    simpa [List.foldl_cons, List.map_cons, List.prod_cons, mul_assoc] using
      ih (downStep v p) (Q * (((p : ℝ) - 1) / p)) htail hstep

/-- Convert a positive lower bound on the reciprocal product into the needed
upper bound on the original Euler product. -/
theorem eulerProduct_le_of_reciprocal (n : ℕ) (r : ℝ) (hr : 0 < r)
    (hrecip : r ≤ ∏ p ∈ Nat.primesLE n, (((p : ℝ) - 1) / p)) :
    eulerProduct n ≤ 1 / r := by
  have hnonneg : 0 ≤ eulerProduct n := by
    apply Finset.prod_nonneg
    intro p hp
    have h : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    exact div_nonneg (by positivity) (by linarith)
  have hcancel :
      (∏ p ∈ Nat.primesLE n, (((p : ℝ) - 1) / p)) * eulerProduct n = 1 := by
    unfold eulerProduct
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have h : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]
  apply (le_div_iff₀ hr).mpr
  have := mul_le_mul_of_nonneg_right hrecip hnonneg
  nlinarith

/-- Sieving with any divisor d >= 2 cannot discard a prime p > d.
This is the mathematical invariant required of an optimized sieve. -/
theorem prime_survives_sieve (p d : ℕ) (hp : Nat.Prime p) (hd : 2 ≤ d)
    (hdp : d < p) : ¬d ∣ p := by
  intro hdiv
  rcases hp.eq_one_or_self_of_dvd d hdiv with h | h <;> omega

/-- No assertion of primality is needed for retained sieve candidates:
including extra integers >= 2 only makes a reciprocal-product bound smaller. -/
theorem reciprocal_product_of_superset (s t : Finset ℕ)
    (hst : s ⊆ t) (ht : ∀ p ∈ t, 2 ≤ p) :
    (∏ p ∈ t, (((p : ℝ) - 1) / p)) ≤ ∏ p ∈ s, (((p : ℝ) - 1) / p) := by
  apply Finset.prod_le_prod_of_subset_of_le_one hst
  · intro p hp
    have h : (2 : ℝ) ≤ p := by exact_mod_cast ht p hp
    exact div_nonneg (by linarith) (by linarith)
  · intro p hp _
    have h : (2 : ℝ) ≤ p := by exact_mod_cast ht p hp
    apply (div_le_one (by linarith : (0 : ℝ) < p)).mpr
    linarith

/-- The short positive series used by the experiment for logarithm bounds.
Range reduction n = 2^k * m keeps its argument at most 1/3. -/
theorem log_series_lower (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) (terms : ℕ) :
    2 * (∑ i ∈ Finset.range terms, z ^ (2 * i + 1) / (2 * i + 1)) ≤
      Real.log ((1 + z) / (1 - z)) := by
  have h := Real.sum_range_le_log_div hz0 hz1 terms
  linarith

end RosserProductCertificate

-- Source: Solutions/ImportedGammaLower.lean
/-!
Accepted Prove2Me proof by andreaskapfer, submission
https://prove2.me/submissions/5b7f3df2-2c10-4572-822a-c64a9d656697
for theorem 9563c569-6ee9-44dd-84a3-163bdd7ea018.
Only changes: added provenance and an enclosing namespace; removed #print;
replaced the all-tactics import with the specific imports used by the proof.
The complete proof is included so local builds do not trust a platform status.
-/

namespace Prove2MeGammaLower

set_option maxRecDepth 1000000

open Real Filter

set_option maxHeartbeats 2000000

namespace TaoFivePrimes


lemma pw (k : ℕ) (hk : 201 ≤ k) :
    2/(2*(k:ℝ)+1) + (2/3)/((2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1)) - 1/((k:ℝ)+1)
      ≤ 18/((6*(k:ℝ)+1)*(6*(k:ℝ)+7)) := by
  have hk403 : (403:ℝ) ≤ 2*(k:ℝ)+1 := by exact_mod_cast (by omega : 403 ≤ 2*k+1)
  have h2 : (0:ℝ) < 2*(k:ℝ)+1 := by linarith
  have hsq : (0:ℝ) < (2*(k:ℝ)+1)^2 - 1 := by nlinarith [sq_nonneg ((2*(k:ℝ)+1) - 403), hk403]
  have hk1 : (0:ℝ) < (k:ℝ)+1 := by positivity
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have h6 : (0:ℝ) < 6*(k:ℝ)+1 := by linarith
  have h7 : (0:ℝ) < 6*(k:ℝ)+7 := by linarith
  have hu : (0:ℝ) ≤ (k:ℝ) - 201 := by linarith
  have hA : 2/(2*(k:ℝ)+1) + (2/3)/((2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1))
      = (6*((2*(k:ℝ)+1)^2 - 1) + 2)/(3*(2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1)) := by
    field_simp <;> ring_nf
  have hB : 18/((6*(k:ℝ)+1)*(6*(k:ℝ)+7)) + 1/((k:ℝ)+1)
      = (18*((k:ℝ)+1) + (6*(k:ℝ)+1)*(6*(k:ℝ)+7))/((6*(k:ℝ)+1)*(6*(k:ℝ)+7)*((k:ℝ)+1)) := by
    field_simp <;> ring_nf
  suffices hs : (6*((2*(k:ℝ)+1)^2 - 1) + 2)/(3*(2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1))
      ≤ (18*((k:ℝ)+1) + (6*(k:ℝ)+1)*(6*(k:ℝ)+7))/((6*(k:ℝ)+1)*(6*(k:ℝ)+7)*((k:ℝ)+1)) by
    linarith [hA, hB]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 3*(2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1))]
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < ((6*(k:ℝ)+1)*(6*(k:ℝ)+7))*((k:ℝ)+1))]
  have hdec : (0:ℝ) ≤ 36*((k:ℝ)-201)^2 + 14494*((k:ℝ)-201) + 1458844 := by positivity
  nlinarith [hdec, hu, sq_nonneg ((k:ℝ)-201)]



lemma log_series_le (k : ℕ) (hk : 1 ≤ k) :
    Real.log (1 + 1/(k:ℝ)) ≤
      2/(2*(k:ℝ)+1) + (2/3)/((2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1)) := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have ha : (0:ℝ) ≤ 1/(k:ℝ) := by positivity
  have hHS : HasSum (fun j : ℕ => 2 * (1 / (2 * (j:ℝ) + 1)) * ((1/(k:ℝ)) / ((1/(k:ℝ)) + 2)) ^ (2 * j + 1))
      (Real.log (1 + 1/(k:ℝ))) := Real.hasSum_log_one_add ha
  have hq : (1/(k:ℝ)) / ((1/(k:ℝ)) + 2) = 1/(2*(k:ℝ)+1) := by
    field_simp
    ring
  simp only [hq] at hHS
  have hsumm : Summable (fun j : ℕ => 2 * (1 / (2 * (j:ℝ) + 1)) * (1/(2*(k:ℝ)+1)) ^ (2 * j + 1)) :=
    hHS.summable
  have hsplit := Summable.sum_add_tsum_nat_add 1 hsumm
  rw [Finset.sum_range_one, hHS.tsum_eq] at hsplit
  have htail_le : (∑' i : ℕ, (fun j : ℕ => 2 * (1 / (2 * (j:ℝ) + 1)) * (1/(2*(k:ℝ)+1)) ^ (2 * j + 1)) (i+1))
      ≤ (2/3) * (1/(2*(k:ℝ)+1))^3 / (1 - (1/(2*(k:ℝ)+1))^2) := by
    have hq0 : (0:ℝ) ≤ (1/(2*(k:ℝ)+1))^2 := sq_nonneg _
    have hq1 : (1/(2*(k:ℝ)+1))^2 < 1 := by
      rw [div_pow, one_pow, div_lt_one (by positivity)]
      nlinarith [hk0, sq_nonneg ((k:ℝ))]
    have hgeo : HasSum (fun j : ℕ => (2/3) * (1/(2*(k:ℝ)+1))^3 * ((1/(2*(k:ℝ)+1))^2)^j)
        ((2/3) * (1/(2*(k:ℝ)+1))^3 / (1 - (1/(2*(k:ℝ)+1))^2)) := by
      have := (hasSum_geometric_of_norm_lt_one
        (show ‖(1/(2*(k:ℝ)+1))^2‖ < 1 by rwa [Real.norm_eq_abs, abs_of_nonneg hq0])).mul_left
        ((2/3) * (1/(2*(k:ℝ)+1))^3)
      rwa [div_eq_mul_inv]
    have hmain := ((summable_nat_add_iff 1).mpr hsumm).tsum_le_tsum (fun j => by
      push_cast
      have hcoe : 2 * (1 / (2 * ((j:ℝ) + 1) + 1)) ≤ 2/3 := by
        rw [show 2 * (1 / (2 * ((j:ℝ) + 1) + 1)) = 2/(2*((j:ℝ)+1)+1) by ring]
        rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*((j:ℝ)+1)+1)]
        linarith
      have hpow : (1/(2*(k:ℝ)+1)) ^ (2 * (j + 1) + 1)
          = (1/(2*(k:ℝ)+1))^3 * ((1/(2*(k:ℝ)+1))^2)^j := by
        rw [show 2 * (j + 1) + 1 = 3 + 2 * j by omega, pow_add, pow_mul]
      calc 2 * (1 / (2 * ((j:ℝ) + 1) + 1)) * (1/(2*(k:ℝ)+1)) ^ (2 * (j + 1) + 1)
          = (2 * (1 / (2 * ((j:ℝ) + 1) + 1))) * ((1/(2*(k:ℝ)+1))^3 * ((1/(2*(k:ℝ)+1))^2)^j) := by
            rw [hpow]
        _ ≤ (2/3) * ((1/(2*(k:ℝ)+1))^3 * ((1/(2*(k:ℝ)+1))^2)^j) := by
            apply mul_le_mul_of_nonneg_right hcoe
            positivity
        _ = (2/3) * (1/(2*(k:ℝ)+1))^3 * ((1/(2*(k:ℝ)+1))^2)^j := by ring) hgeo.summable
    exact hmain.trans_eq hgeo.tsum_eq
  have hconv : (2/3) * (1/(2*(k:ℝ)+1))^3 / (1 - (1/(2*(k:ℝ)+1))^2)
      = (2/3)/((2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1)) := by
    field_simp
  have hlog : Real.log (1 + 1/(k:ℝ)) = 2 * (1/(2*(k:ℝ)+1))
      + (∑' i : ℕ, (fun j : ℕ => 2 * (1 / (2 * (j:ℝ) + 1)) * (1/(2*(k:ℝ)+1)) ^ (2 * j + 1)) (i+1)) := by
    rw [← hsplit]
    congr 1
    norm_num
  have hid : 2 * (1/(2*(k:ℝ)+1)) = 2/(2*(k:ℝ)+1) := by ring
  have htail_le' : (∑' i : ℕ, (fun j : ℕ => 2 * (1 / (2 * (j:ℝ) + 1)) * (1/(2*(k:ℝ)+1)) ^ (2 * j + 1)) (i+1))
      ≤ (2/3)/((2*(k:ℝ)+1)*((2*(k:ℝ)+1)^2 - 1)) := htail_le.trans_eq hconv
  rw [hlog]
  linarith [htail_le', hid]


lemma term_le (k : ℕ) (hk : 201 ≤ k) :
    ZetaAsymptotics.term k 1 ≤ 18/((6*(k:ℝ)+1)*(6*(k:ℝ)+7)) := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  rw [ZetaAsymptotics.term_one (by omega : 0 < k)]
  have h1 : Real.log ((k:ℝ)+1) - Real.log (k:ℝ) = Real.log (1 + 1/(k:ℝ)) := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  rw [h1]
  linarith [log_series_le k (by omega : 1 ≤ k), pw k hk]

lemma tail_bound : (∑' k : ℕ, ZetaAsymptotics.term (k + 201) 1) ≤ 3/1207 := by
  have htel : ∀ k : ℕ, (18:ℝ)/((6*(((k+201:ℕ)):ℝ)+1)*(6*(((k+201:ℕ)):ℝ)+7))
      = (1/2)/((k:ℝ)+201+1/6) - (1/2)/(((k+1:ℕ):ℝ)+201+1/6) := by
    intro k
    push_cast
    have h1 : (6*((k:ℝ)+201)+1) ≠ 0 := by positivity
    have h2 : (6*((k:ℝ)+201)+7) ≠ 0 := by positivity
    have h3 : ((k:ℝ)+201+1/6) ≠ 0 := by positivity
    have h4 : ((k:ℝ)+1+201+1/6) ≠ 0 := by positivity
    field_simp [h1, h2, h3, h4]
    ring
  have hu_tend : Tendsto (fun n : ℕ => (1/2)/((n:ℝ)+201+1/6)) atTop (nhds 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n:ℝ) + (201 + 1/6))) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => (((n:ℝ) + (201 + 1/6)))⁻¹) atTop (nhds 0) := h1.inv_tendsto_atTop
    have h3 : Tendsto (fun n : ℕ => (1/2) * (((n:ℝ) + (201 + 1/6)))⁻¹) atTop (nhds (1/2 * 0)) :=
      tendsto_const_nhds.mul h2
    rw [mul_zero] at h3
    simpa [div_eq_mul_inv, add_assoc] using h3
  have hRsum : HasSum (fun k : ℕ => (18:ℝ)/((6*(((k+201:ℕ)):ℝ)+1)*(6*(((k+201:ℕ)):ℝ)+7)))
      ((1/2)/((201:ℝ)+1/6)) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity)]
    have hps : ∀ n, ∑ k ∈ Finset.range n, (18:ℝ)/((6*(((k+201:ℕ)):ℝ)+1)*(6*(((k+201:ℕ)):ℝ)+7))
        = (1/2)/((0:ℝ)+201+1/6) - (1/2)/((n:ℝ)+201+1/6) := by
      intro n
      calc ∑ k ∈ Finset.range n, (18:ℝ)/((6*(((k+201:ℕ)):ℝ)+1)*(6*(((k+201:ℕ)):ℝ)+7))
          = ∑ k ∈ Finset.range n, ((1/2)/((k:ℝ)+201+1/6) - (1/2)/(((k+1:ℕ):ℝ)+201+1/6)) := by
            apply Finset.sum_congr rfl
            intro k _
            exact htel k
        _ = -(∑ k ∈ Finset.range n, ((1/2)/(((k+1:ℕ):ℝ)+201+1/6) - (1/2)/((k:ℝ)+201+1/6))) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro k _
            ring
        _ = -((1/2)/((n:ℝ)+201+1/6) - (1/2)/(((0:ℕ):ℝ)+201+1/6)) := by
            rw [Finset.sum_range_sub (fun k : ℕ => (1/2)/((k:ℝ)+201+1/6)) n]
        _ = (1/2)/((0:ℝ)+201+1/6) - (1/2)/((n:ℝ)+201+1/6) := by
            simp only [Nat.cast_zero]
            ring
    simp_rw [hps]
    simpa using tendsto_const_nhds.sub hu_tend
  have hsumg : Summable (fun k : ℕ => ZetaAsymptotics.term (k + 201) 1) := by
    have hf : Summable (fun n : ℕ => ZetaAsymptotics.term (n+1) 1) :=
      ZetaAsymptotics.term_tsum_one.summable
    exact (summable_nat_add_iff 200).mpr hf
  have hRsummable : Summable (fun k : ℕ =>
      (18:ℝ)/((6*(((k+201:ℕ)):ℝ)+1)*(6*(((k+201:ℕ)):ℝ)+7))) := hRsum.summable
  have key := hsumg.tsum_le_tsum (fun k => term_le (k+201) (by omega)) hRsummable
  rw [hRsum.tsum_eq] at key
  norm_num at key ⊢
  exact key

/-- Lower bound for Euler--Mascheroni: `57721565/10^8 ≤ γ`. -/
theorem solution : (57721565/10^8 : ℝ) ≤ Real.eulerMascheroniConstant := by
  have hf : Summable (fun n : ℕ => ZetaAsymptotics.term (n+1) 1) :=
    ZetaAsymptotics.term_tsum_one.summable
  have hsplit := Summable.sum_add_tsum_nat_add 200 hf
  rw [ZetaAsymptotics.term_tsum_one.tsum_eq] at hsplit
  have htail_eq : (∑' i : ℕ, (fun n : ℕ => ZetaAsymptotics.term (n+1) 1) (i+200))
      = (∑' k : ℕ, ZetaAsymptotics.term (k+201) 1) := by
    apply tsum_congr
    intro i
    congr 1
  rw [htail_eq] at hsplit
  have htermSum : (∑ i ∈ Finset.range 200, ZetaAsymptotics.term (i+1) 1)
      = Real.log 201 - (harmonic 201 : ℝ) + 1 := by
    have h := ZetaAsymptotics.termSum_one 200
    unfold ZetaAsymptotics.termSum at h
    rw [show ((200:ℕ):ℝ) + 1 = 201 by norm_num, show (200 + 1 : ℕ) = 201 by norm_num] at h
    exact h
  rw [htermSum] at hsplit
  have hγ : Real.eulerMascheroniConstant = (harmonic 201 : ℝ) - Real.log 201
      - (∑' k : ℕ, ZetaAsymptotics.term (k+201) 1) := by
    linarith
  have hr : Real.log 201 ≤ (530330491/10^8 : ℝ) := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 201)]
    calc (201:ℝ) ≤ (2.7182818283:ℝ)^5 * (∑ i ∈ Finset.range 10, (30330491/10^8:ℝ)^i / (i.factorial : ℝ)) := by
          norm_num
      _ ≤ (Real.exp 1)^5 * Real.exp (30330491/10^8) := by
          gcongr
          · exact le_of_lt Real.exp_one_gt_d9
          · exact Real.sum_le_exp_of_nonneg (by norm_num) 10
      _ = Real.exp 5 * Real.exp (30330491/10^8) := by
          rw [← Real.exp_nat_mul 1 5]
          norm_num
      _ = Real.exp (5 + 30330491/10^8) := by rw [← Real.exp_add]
      _ = Real.exp (530330491/10^8) := by norm_num
  have hnum : (57721565/10^8 : ℝ) ≤ (harmonic 201 : ℝ) - (530330491/10^8) - 3/1207 := by
    norm_num [harmonic]
  calc (57721565/10^8 : ℝ) ≤ (harmonic 201 : ℝ) - (530330491/10^8) - 3/1207 := hnum
    _ ≤ Real.eulerMascheroniConstant := by
        rw [hγ]
        linarith [hr, tail_bound]

end TaoFivePrimes

open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution : (57721565/10^8 : ℝ) ≤ Real.eulerMascheroniConstant :=
  TaoFivePrimes.solution


end Prove2MeGammaLower

-- Source: Solutions/RosserProductPilot.lean
/-!
A fully proved pilot interval, using the same downward-rounding scheme as
scripts/rosser_product_experiment.py. All concrete computations below are
checked by Lean; there is no native_decide or external numerical oracle.
The slow reference prime enumeration is only intended for this small pilot.
-/

namespace RosserProductCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def referencePrimes (B : ℕ) : List ℕ :=
  (List.range (B + 1)).filter (fun p => decide (2 ≤ p ∧ Nat.minFac p = p))

theorem referencePrimes_toFinset (B : ℕ) :
    (referencePrimes B).toFinset = Nat.primesLE B := by
  ext p
  simp [referencePrimes, Nat.mem_primesLE, Nat.prime_def_minFac]

theorem referencePrimes_nodup (B : ℕ) : (referencePrimes B).Nodup :=
  List.nodup_range.filter _

theorem referencePrimes_ge_two (B p : ℕ) (hp : p ∈ referencePrimes B) : 2 ≤ p := by
  have h := (List.mem_filter.mp hp).2
  exact (of_decide_eq_true h).1

theorem exp_gamma_lower :
    (178107239 / 10 ^ 8 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by
  have h := Real.sum_le_exp_of_nonneg
    (show (0 : ℝ) ≤ 57721565 / 10 ^ 8 by norm_num) 16
  have hnum : (178107239 / 10 ^ 8 : ℝ) ≤
      ∑ i ∈ Finset.range 16, (57721565 / 10 ^ 8 : ℝ) ^ i / i.factorial := by
    norm_num [Finset.sum_range_succ]
  exact (hnum.trans h).trans (Real.exp_le_exp.mpr Prove2MeGammaLower.solution)

theorem log_4500_lower : (8411832675757 / 10 ^ 12 : ℝ) ≤ Real.log 4500 := by
  have htwo := log_series_lower (1 / 3 : ℝ) (by norm_num) (by norm_num) 12
  have hrest := log_series_lower (101 / 2149 : ℝ) (by norm_num) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at htwo hrest
  have heq : Real.log 4500 = 12 * Real.log 2 + Real.log (1125 / 1024) := by
    have hn : (4500 : ℝ) = 2 ^ 12 * (1125 / 1024) := by norm_num
    rw [hn, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  rw [heq]
  linarith

/-- A kernel computation with a fixed 64-bit denominator; no huge exact
numerator and denominator for the Euler product are constructed. -/
theorem reciprocal_4533_lower :
    (1227903923884082104 : ℝ) / 2 ^ 64 ≤
      ∏ p ∈ Nat.primesLE 4533, (((p : ℝ) - 1) / p) := by
  have hcalc : (referencePrimes 4533).foldl downStep (2 ^ 64) =
      1227903923884082104 := by decide +kernel
  have h := downRun_sound (referencePrimes 4533) (2 ^ 64) (2 ^ 64) 1
    (by norm_num) (referencePrimes_ge_two 4533) (by norm_num)
  rw [hcalc] at h
  rw [← List.prod_toFinset _ (referencePrimes_nodup 4533), referencePrimes_toFinset] at h
  simpa only [Nat.cast_pow, Nat.cast_ofNat, one_mul] using h

/-- The original platform inequality, proved without additional hypotheses
on the closed real interval [4500, 4533]. -/
theorem product_bound_4500_to_4533 (x : ℝ) (hx : 4500 ≤ x) (hx' : x ≤ 4533) :
    ∏ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ) / ((p : ℝ) - 1) <
      Real.exp Real.eulerMascheroniConstant * Real.log x +
        2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x := by
  have hu := eulerProduct_le_of_reciprocal 4533
    (1227903923884082104 / 2 ^ 64) (by norm_num) reciprocal_4533_lower
  apply block_bound 4533 4500 x (1 / (1227903923884082104 / 2 ^ 64))
    (178107239 / 10 ^ 8) (8411832675757 / 10 ^ 12) 68
    (by norm_num) hx hx' hu exp_gamma_lower (by norm_num) log_4500_lower
    (by norm_num) (by norm_num)
  norm_num

end RosserProductCertificate

-- Source: Solutions/RosserLogCertificate.lean
/-!
A table-free lower bound for log(n). All evaluation uses natural numbers
with fixed denominator 2^64. There are twelve positive atanh-series terms;
every division, including the power recurrence, rounds downward.
-/

namespace RosserLogCertificate

theorem scale_pos : 0 < scale := by decide

theorem rounded_mul_lower (D p q : ℕ) (x y : ℝ) (hD : 0 < D)
    (hx0 : 0 ≤ x) (hp : (p : ℝ) / D ≤ x) (hq : (q : ℝ) / D ≤ y) :
    ((p * q / D : ℕ) : ℝ) / D ≤ x * y := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hround := Nat.cast_div_le (m := p * q) (n := D) (α := ℝ)
  simp only [Nat.cast_mul] at hround
  calc
    ((p * q / D : ℕ) : ℝ) / D ≤ ((p : ℝ) * q / D) / D :=
      div_le_div_of_nonneg_right hround hD0.le
    _ = ((p : ℝ) / D) * ((q : ℝ) / D) := by ring
    _ ≤ x * y := mul_le_mul hp hq (by positivity) hx0

theorem seriesRun_sound (D q : ℕ) (z : ℝ) (hD : 0 < D) (hz : 0 ≤ z)
    (hq : (q : ℝ) / D ≤ z ^ 2) (j p terms : ℕ)
    (hp : (p : ℝ) / D ≤ z ^ (2 * j + 1)) :
    (seriesRun D q j p terms : ℝ) / D ≤
      ∑ i ∈ Finset.range terms,
        z ^ (2 * (j + i) + 1) / (2 * ((j + i : ℕ) : ℝ) + 1) := by
  induction terms generalizing j p with
  | zero => simp [seriesRun]
  | succ terms ih =>
    have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
    have hden : (0 : ℝ) < 2 * j + 1 := by positivity
    have hterm : ((p / (2 * j + 1) : ℕ) : ℝ) / D ≤
        z ^ (2 * j + 1) / (2 * (j : ℝ) + 1) := by
      have hr := Nat.cast_div_le (m := p) (n := 2 * j + 1) (α := ℝ)
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hr
      calc
        ((p / (2 * j + 1) : ℕ) : ℝ) / D ≤
            ((p : ℝ) / (2 * (j : ℝ) + 1)) / D :=
          div_le_div_of_nonneg_right hr hD0.le
        _ = ((p : ℝ) / D) / (2 * (j : ℝ) + 1) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hp hden.le
    have hnext : ((p * q / D : ℕ) : ℝ) / D ≤ z ^ (2 * (j + 1) + 1) := by
      have hr := rounded_mul_lower D p q (z ^ (2 * j + 1)) (z ^ 2)
        hD (by positivity) hp hq
      have he : z ^ (2 * j + 1) * z ^ 2 = z ^ (2 * (j + 1) + 1) := by
        rw [← pow_add]
        congr 1
      exact he ▸ hr
    have hi := ih (j + 1) (p * q / D) hnext
    rw [Finset.sum_range_succ']
    simp only [seriesRun, Nat.cast_add, add_div]
    have hshift :
        (∑ i ∈ Finset.range terms,
          z ^ (2 * (j + 1 + i) + 1) / (2 * ((j + 1 + i : ℕ) : ℝ) + 1)) =
        ∑ i ∈ Finset.range terms,
          z ^ (2 * (j + (i + 1)) + 1) / (2 * ((j + (i + 1) : ℕ) : ℝ) + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      have he : j + 1 + i = j + (i + 1) := by omega
      rw [he]
    rw [hshift] at hi
    simpa only [Nat.add_zero, Nat.cast_add, Nat.cast_zero, Nat.cast_one,
      add_zero, add_comm] using add_le_add hi hterm

theorem atanhLower_sound (num den : ℕ) (hden : 0 < den) (hnum : num < den) :
    (atanhLower num den : ℝ) / scale ≤
      Real.log ((1 + (num : ℝ) / den) / (1 - (num : ℝ) / den)) := by
  let z : ℝ := (num : ℝ) / den
  let v := num * scale / den
  let q := v * v / scale
  have hD0 : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have hden0 : (0 : ℝ) < den := by exact_mod_cast hden
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : z < 1 := by
    apply (div_lt_one hden0).mpr
    exact_mod_cast hnum
  have hv : (v : ℝ) / scale ≤ z := by
    have hr := Nat.cast_div_le (m := num * scale) (n := den) (α := ℝ)
    simp only [Nat.cast_mul] at hr
    calc
      (v : ℝ) / scale ≤ ((num : ℝ) * scale / den) / scale :=
        div_le_div_of_nonneg_right hr hD0.le
      _ = z := by dsimp [z]; field_simp
  have hq : (q : ℝ) / scale ≤ z ^ 2 := by
    simpa only [pow_two] using rounded_mul_lower scale v v z z scale_pos hz0 hv hv
  have hr := seriesRun_sound scale q z scale_pos hz0 hq 0 v 12
    (by simpa using hv)
  simp only [Nat.zero_add] at hr
  have hl := Real.sum_range_le_log_div hz0 hz1 12
  change (2 * seriesRun scale q 0 v 12 : ℕ) / (scale : ℝ) ≤ _
  push_cast
  change 2 * (seriesRun scale q 0 v 12 : ℝ) / scale ≤
    Real.log ((1 + z) / (1 - z))
  calc
    2 * (seriesRun scale q 0 v 12 : ℝ) / scale =
        2 * ((seriesRun scale q 0 v 12 : ℝ) / scale) := by ring
    _ ≤ _ := by linarith only [hr, hl]

theorem logTwoLower_eval : atanhLower 1 3 = logTwoLower := by decide +kernel

theorem logTwoLower_sound : (logTwoLower : ℝ) / scale ≤ Real.log 2 := by
  have h := atanhLower_sound 1 3 (by decide) (by decide)
  rw [logTwoLower_eval] at h
  norm_num at h ⊢
  exact h

theorem logLower_sound (n : ℕ) (hn : 1 ≤ n) :
    (logLower n : ℝ) / scale ≤ Real.log n := by
  let k := Nat.log2 n
  let t : ℕ := 2 ^ k
  have hn0 : n ≠ 0 := by omega
  have ht0 : 0 < t := by dsimp [t]; positivity
  have htn : t ≤ n := (Nat.le_log2 hn0).mp (le_refl _)
  have hnum : n - t < n + t := by omega
  have hden : 0 < n + t := by omega
  have hrest := atanhLower_sound (n - t) (n + t) hden hnum
  have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
  have hn0' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hid : (1 + ((n - t : ℕ) : ℝ) / (n + t : ℕ)) /
      (1 - ((n - t : ℕ) : ℝ) / (n + t : ℕ)) = (n : ℝ) / t := by
    rw [Nat.cast_sub htn, Nat.cast_add]
    field_simp [ne_of_gt ht0', ne_of_gt (add_pos hn0' ht0')]
    ring
  rw [hid, Real.log_div (ne_of_gt hn0') (ne_of_gt ht0')] at hrest
  have htlog : Real.log (t : ℝ) = (k : ℝ) * Real.log 2 := by
    simp only [t, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [htlog] at hrest
  have htwo := mul_le_mul_of_nonneg_left logTwoLower_sound
    (show (0 : ℝ) ≤ k by positivity)
  change ((k * logTwoLower + atanhLower (n - t) (n + t) : ℕ) : ℝ) / scale ≤ _
  rw [Nat.cast_add, Nat.cast_mul, add_div, mul_div_assoc]
  linarith only [htwo, hrest]

theorem logLower_4500_eval : logLower 4500 = 155170924560559531400 := by decide +kernel

theorem logLower_4500_ge_pilot :
    (8411832675757 / 10 ^ 12 : ℝ) ≤ (logLower 4500 : ℝ) / scale := by
  rw [logLower_4500_eval]
  norm_num [scale]

end RosserLogCertificate

-- Source: Solutions/RosserBlockCheck.lean
/-! A single exact integer comparison proves the real bound on a block. -/

namespace RosserBlockCheck

open RosserProductCertificate RosserLogCertificate

def Bound (x : ℝ) : Prop :=
  eulerProduct ⌊x⌋₊ <
    Real.exp Real.eulerMascheroniConstant * Real.log x +
      2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x

theorem check_sound (a b v : ℕ) (ha : 1 ≤ a) (hcheck : check a b v = true)
    (hv : (v : ℝ) / scale ≤ ∏ p ∈ Nat.primesLE b, (((p : ℝ) - 1) / p))
    (x : ℝ) (hax : (a : ℝ) ≤ x) (hxb : x ≤ b) : Bound x := by
  obtain ⟨hv0, hnum⟩ := of_decide_eq_true hcheck
  have hv0' : (0 : ℝ) < v := by exact_mod_cast hv0
  have hD : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have hS : (0 : ℝ) < sqrtUpper b := by
    exact_mod_cast (show 0 < sqrtUpper b by unfold sqrtUpper; omega)
  have hBS : (b : ℝ) ≤ (sqrtUpper b : ℝ) ^ 2 := by
    have h : b ≤ sqrtUpper b ^ 2 := (Nat.lt_succ_sqrt' b).le
    exact_mod_cast h
  have hineq : (scale : ℝ) * scale * 10 ^ 8 * sqrtUpper b <
      (v : ℝ) * 178107239 * ((logLower a : ℝ) * sqrtUpper b + 2 * scale) := by
    exact_mod_cast hnum
  have hc : (1 : ℝ) / ((v : ℝ) / scale) <
      (178107239 / 10 ^ 8 : ℝ) *
        ((logLower a : ℝ) / scale + 2 / sqrtUpper b) := by
    apply (div_lt_iff₀ (div_pos hv0' hD)).mpr
    field_simp
    nlinarith only [hineq]
  exact block_bound b a x (1 / ((v : ℝ) / scale)) (178107239 / 10 ^ 8)
    ((logLower a : ℝ) / scale) (sqrtUpper b)
    (by exact_mod_cast ha) hax hxb
    (eulerProduct_le_of_reciprocal b _ (div_pos hv0' hD) hv)
    exp_gamma_lower (div_nonneg (Nat.cast_nonneg _) hD.le)
    (logLower_sound a ha) hS hBS hc

end RosserBlockCheck

-- Source: Solutions/AlternativeProductMoments.lean
/-!
A different arithmetic kernel for a finite Euler-product certificate.
It replaces multiplication/division for every prime by three integer moments
per block. This file proves the mathematical inequalities, not the full
Rosser--Schoenfeld bound through 10^8.
-/

namespace AlternativeProductMoments

theorem square_sum_ge_sum_squares (xs : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x) :
    (xs.map (fun x => x ^ 2)).sum ≤ xs.sum ^ 2 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have htail : ∀ y ∈ xs, 0 ≤ y := by
      intro y hy
      exact hxs y (by simp [hy])
    have hs : 0 ≤ xs.sum := List.sum_nonneg htail
    have hi := ih htail
    simp only [List.map_cons, List.sum_cons]
    nlinarith [mul_nonneg hx hs]

/-- A conservative third-order Bonferroni bound. Its induction only uses
the nonnegative first two moments; no exponential or logarithm is needed. -/
theorem product_lower (xs : List ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1) :
    (1 - xs.sum) * (1 + (xs.sum ^ 2 - (xs.map (fun x => x ^ 2)).sum) / 2) ≤
      (xs.map (fun x => 1 - x)).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have htail : ∀ y ∈ xs, 0 ≤ y ∧ y ≤ 1 := by
      intro y hy
      exact hxs y (by simp [hy])
    have hs : 0 ≤ xs.sum := List.sum_nonneg (fun y hy => (htail y hy).1)
    have he : 0 ≤ xs.sum ^ 2 - (xs.map (fun y => y ^ 2)).sum :=
      sub_nonneg.mpr (square_sum_ge_sum_squares xs (fun y hy => (htail y hy).1))
    have hmul := mul_le_mul_of_nonneg_left (ih htail) (sub_nonneg.mpr hx.2)
    have herr : 0 ≤ x * xs.sum *
        ((xs.sum ^ 2 - (xs.map (fun y => y ^ 2)).sum) / 2 + xs.sum + x) := by
      exact mul_nonneg (mul_nonneg hx.1 hs)
        (add_nonneg (add_nonneg (div_nonneg he (by norm_num)) hs) hx.1)
    simp only [List.map_cons, List.sum_cons, List.prod_cons]
    nlinarith only [hmul, herr]

/-- Safe interval versions of the two moments. The max allows blocks with
zero or one candidate, for which the approximate pair correction is negative. -/
theorem product_lower_of_moment_bounds (xs : List ℝ) (L U T : ℝ)
    (hxs : ∀ x ∈ xs, 0 ≤ x ∧ x ≤ 1)
    (hL0 : 0 ≤ L) (hL : L ≤ xs.sum) (hU : xs.sum ≤ U) (hU1 : U ≤ 1)
    (hT : (xs.map (fun x => x ^ 2)).sum ≤ T) :
    (1 - U) * (1 + max 0 ((L ^ 2 - T) / 2)) ≤
      (xs.map (fun x => 1 - x)).prod := by
  have hs : 0 ≤ xs.sum := List.sum_nonneg (fun y hy => (hxs y hy).1)
  have he := square_sum_ge_sum_squares xs (fun y hy => (hxs y hy).1)
  have hpair : max 0 ((L ^ 2 - T) / 2) ≤
      (xs.sum ^ 2 - (xs.map (fun x => x ^ 2)).sum) / 2 := by
    apply max_le
    · linarith
    · nlinarith [sq_nonneg (xs.sum - L)]
  calc
    (1 - U) * (1 + max 0 ((L ^ 2 - T) / 2)) ≤
        (1 - xs.sum) * (1 + (xs.sum ^ 2 - (xs.map (fun x => x ^ 2)).sum) / 2) := by
      apply mul_le_mul
      · linarith
      · linarith
      · positivity
      · linarith
    _ ≤ _ := product_lower xs hxs

/-- The first three terms of the geometric expansion enclose 1/(a+d).
Summing this uses only the count, sum, and sum of squares of integer offsets. -/
theorem inverse_bounds (a d : ℝ) (ha : 0 < a) (hd : 0 ≤ d) :
    1 / a - d / a ^ 2 ≤ 1 / (a + d) ∧
    1 / (a + d) ≤ 1 / a - d / a ^ 2 + d ^ 2 / a ^ 3 := by
  have had : 0 < a + d := by linarith
  constructor
  · apply (le_div_iff₀ had).mpr
    field_simp
    nlinarith [sq_nonneg d]
  · apply (div_le_iff₀ had).mpr
    field_simp
    nlinarith [mul_nonneg hd (sq_nonneg d)]

/-- Moment bounds for all candidates of the form a+d in a block. -/
theorem reciprocal_moment_bounds (a : ℝ) (ds : List ℝ)
    (ha : 0 < a) (hds : ∀ d ∈ ds, 0 ≤ d) :
    ((ds.length : ℝ) / a - ds.sum / a ^ 2 ≤
        (ds.map (fun d => 1 / (a + d))).sum) ∧
    ((ds.map (fun d => 1 / (a + d))).sum ≤
        (ds.length : ℝ) / a - ds.sum / a ^ 2 +
          (ds.map (fun d => d ^ 2)).sum / a ^ 3) ∧
    ((ds.map (fun d => (1 / (a + d)) ^ 2)).sum ≤
        (ds.length : ℝ) / a ^ 2) := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have hd := hds d (by simp)
    have htail : ∀ e ∈ ds, 0 ≤ e := by
      intro e he
      exact hds e (by simp [he])
    have hi := ih htail
    have hb := inverse_bounds a d ha hd
    have had : 0 < a + d := by linarith
    have hsq : (1 / (a + d)) ^ 2 ≤ 1 / a ^ 2 := by
      rw [div_pow, one_pow]
      apply div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos ha)
      nlinarith [sq_nonneg d, mul_nonneg ha.le hd]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one,
      List.map_cons, List.sum_cons]
    constructor
    · convert add_le_add hb.1 hi.1 using 1 <;> first | rfl | ring
    constructor
    · convert add_le_add hb.2 hi.2.1 using 1 <;> first | rfl | ring
    · convert add_le_add hsq hi.2.2 using 1 <;> first | rfl | ring

/-- The exact factor used by the alternative experiment. Checking the three
integer moments suffices for the product bound for an entire block. -/
theorem block_factor_lower (a : ℝ) (ds : List ℝ)
    (ha : 1 ≤ a) (hds : ∀ d ∈ ds, 0 ≤ d)
    (hL : 0 ≤ (ds.length : ℝ) / a - ds.sum / a ^ 2)
    (hU : (ds.length : ℝ) / a - ds.sum / a ^ 2 +
      (ds.map (fun d => d ^ 2)).sum / a ^ 3 ≤ 1) :
    (1 - ((ds.length : ℝ) / a - ds.sum / a ^ 2 +
        (ds.map (fun d => d ^ 2)).sum / a ^ 3)) *
      (1 + max 0 ((((ds.length : ℝ) / a - ds.sum / a ^ 2) ^ 2 -
        (ds.length : ℝ) / a ^ 2) / 2)) ≤
      (ds.map (fun d => 1 - 1 / (a + d))).prod := by
  have ha0 : 0 < a := by linarith
  have hb := reciprocal_moment_bounds a ds ha0 hds
  have hxs : ∀ x ∈ ds.map (fun d => 1 / (a + d)), 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    have hd0 := hds d hd
    have had : 0 < a + d := by linarith
    constructor
    · positivity
    · apply (div_le_one had).mpr
      linarith
  simpa only [List.map_map, Function.comp_def] using
    product_lower_of_moment_bounds (ds.map (fun d => 1 / (a + d)))
      ((ds.length : ℝ) / a - ds.sum / a ^ 2)
      ((ds.length : ℝ) / a - ds.sum / a ^ 2 +
        (ds.map (fun d => d ^ 2)).sum / a ^ 3)
      ((ds.length : ℝ) / a ^ 2) hxs hL hb.1 hb.2.1 hU
      (by simpa only [List.map_map, Function.comp_def] using hb.2.2)

private theorem cast_sub_max (n m : ℕ) :
    ((n - m : ℕ) : ℝ) = max 0 ((n : ℝ) - m) := by
  by_cases h : m ≤ n
  · rw [Nat.cast_sub h, max_eq_right]
    exact sub_nonneg.mpr (by exact_mod_cast h)
  · have hmn : n ≤ m := by omega
    rw [Nat.sub_eq_zero_of_le hmn, Nat.cast_zero, max_eq_left]
    exact sub_nonpos.mpr (by exact_mod_cast hmn)

/-- Cast the three integer moments once, outside the computational loop. -/
theorem integer_factor_lower (a : ℕ) (ds : List ℕ)
    (ha : 2 ≤ a) (hfirst : firstMoment ds ≤ ds.length * a)
    (hupper : upperNumerator a ds ≤ a ^ 3) :
    (factorNumerator a ds : ℝ) / factorDenominator a ≤
      (ds.map (fun (d : ℕ) => 1 - 1 / ((a : ℝ) + d))).prod := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have ha_ne : (a : ℝ) ≠ 0 := ne_of_gt ha0
  have hfirst' : a * firstMoment ds ≤ ds.length * a ^ 2 := by
    calc
      a * firstMoment ds ≤ a * (ds.length * a) := Nat.mul_le_mul_left a hfirst
      _ = ds.length * a ^ 2 := by ring
  have hcastL : (lowerNumerator a ds : ℝ) =
      (ds.length : ℝ) * a - firstMoment ds := by
    simp only [lowerNumerator, Nat.cast_sub hfirst, Nat.cast_mul]
  have hcastU : (upperNumerator a ds : ℝ) =
      (ds.length : ℝ) * (a : ℝ) ^ 2 - a * firstMoment ds + secondMoment ds := by
    simp only [upperNumerator, Nat.cast_add, Nat.cast_sub hfirst', Nat.cast_mul,
      Nat.cast_pow]
  have hcastE : (pairNumerator a ds : ℝ) =
      max 0 (((ds.length : ℝ) * a - firstMoment ds) ^ 2 -
        (ds.length : ℝ) * (a : ℝ) ^ 2) := by
    simp only [pairNumerator, cast_sub_max, Nat.cast_pow, Nat.cast_mul, hcastL]
  have hL : 0 ≤ (ds.length : ℝ) / a - (firstMoment ds : ℝ) / (a : ℝ) ^ 2 := by
    have heq : (ds.length : ℝ) / a - (firstMoment ds : ℝ) / (a : ℝ) ^ 2 =
        (lowerNumerator a ds : ℝ) / (a : ℝ) ^ 2 := by
      rw [hcastL]
      field_simp
    rw [heq]
    positivity
  have hU : (ds.length : ℝ) / a - (firstMoment ds : ℝ) / (a : ℝ) ^ 2 +
      (secondMoment ds : ℝ) / (a : ℝ) ^ 3 ≤ 1 := by
    have hcast := (show (upperNumerator a ds : ℝ) ≤ (a : ℝ) ^ 3 by exact_mod_cast hupper)
    have heq : (ds.length : ℝ) / a - (firstMoment ds : ℝ) / (a : ℝ) ^ 2 +
        (secondMoment ds : ℝ) / (a : ℝ) ^ 3 =
        (upperNumerator a ds : ℝ) / (a : ℝ) ^ 3 := by
      rw [hcastU]
      field_simp
    rw [heq]
    exact (div_le_one (pow_pos ha0 3)).mpr hcast
  have hsum : (ds.map (fun (d : ℕ) => (d : ℝ))).sum = (firstMoment ds : ℝ) := by
    simp only [firstMoment, Nat.cast_list_sum]
  have hsquares :
      ((ds.map (fun (d : ℕ) => (d : ℝ))).map (fun d => d ^ 2)).sum =
        (secondMoment ds : ℝ) := by
    simp only [secondMoment, Nat.cast_list_sum, List.map_map, Function.comp_def,
      Nat.cast_pow]
  have hsquares' : (ds.map (fun (d : ℕ) => (d : ℝ) ^ 2)).sum =
      (secondMoment ds : ℝ) := by
    simpa only [List.map_map, Function.comp_def] using hsquares
  have hb := block_factor_lower (a : ℝ) (ds.map (fun (d : ℕ) => (d : ℝ)))
    (by exact_mod_cast (show 1 ≤ a by omega))
    (by intro d hd; obtain ⟨n, _, rfl⟩ := List.mem_map.mp hd; positivity)
    (by simpa only [List.length_map, hsum] using hL)
    (by simpa only [List.length_map, hsum, hsquares] using hU)
  simp only [List.length_map, hsum, List.map_map, Function.comp_def, hsquares'] at hb
  have hpair : (pairNumerator a ds : ℝ) / (2 * (a : ℝ) ^ 4) =
      max 0 ((((ds.length : ℝ) / a - (firstMoment ds : ℝ) / (a : ℝ) ^ 2) ^ 2 -
        (ds.length : ℝ) / (a : ℝ) ^ 2) / 2) := by
    rw [hcastE, ← max_div_div_right (by positivity : (0 : ℝ) ≤ 2 * (a : ℝ) ^ 4),
      zero_div]
    congr 1
    field_simp
  have hfactor : (factorNumerator a ds : ℝ) / factorDenominator a =
      (1 - ((ds.length : ℝ) / a - (firstMoment ds : ℝ) / (a : ℝ) ^ 2 +
        (secondMoment ds : ℝ) / (a : ℝ) ^ 3)) *
        (1 + max 0 ((((ds.length : ℝ) / a - (firstMoment ds : ℝ) / (a : ℝ) ^ 2) ^ 2 -
          (ds.length : ℝ) / (a : ℝ) ^ 2) / 2)) := by
    rw [← hpair]
    simp only [factorNumerator, factorDenominator, Nat.cast_mul,
      Nat.cast_sub hupper, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, hcastU]
    field_simp
  rw [hfactor]
  exact hb

/-- The complete integer step: all candidates may be composite and all
computations are on natural numbers. A separate sieve coverage theorem
relates their product to the actual prime product. -/
theorem momentStep_sound (D v a : ℕ) (ds : List ℕ) (Q : ℝ)
    (hD : 0 < D) (ha : 2 ≤ a) (hfirst : firstMoment ds ≤ ds.length * a)
    (hupper : upperNumerator a ds ≤ a ^ 3) (hv : (v : ℝ) / D ≤ Q) :
    (momentStep v a ds : ℝ) / D ≤
      Q * (ds.map (fun (d : ℕ) => 1 - 1 / ((a : ℝ) + d))).prod := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hQ : 0 ≤ Q := (by positivity : (0 : ℝ) ≤ (v : ℝ) / D).trans hv
  have hround : (momentStep v a ds : ℝ) ≤
      (v : ℝ) * (factorNumerator a ds : ℝ) / factorDenominator a := by
    simpa only [momentStep, Nat.cast_mul] using
      (Nat.cast_div_le (m := v * factorNumerator a ds)
        (n := factorDenominator a) (α := ℝ))
  calc
    (momentStep v a ds : ℝ) / D ≤
        ((v : ℝ) * (factorNumerator a ds : ℝ) / factorDenominator a) / D :=
      div_le_div_of_nonneg_right hround hD0.le
    _ = ((v : ℝ) / D) * ((factorNumerator a ds : ℝ) / factorDenominator a) := by ring
    _ ≤ Q * ((factorNumerator a ds : ℝ) / factorDenominator a) :=
      mul_le_mul_of_nonneg_right hv (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (integer_factor_lower a ds ha hfirst hupper) hQ

end AlternativeProductMoments

-- Source: Solutions/RosserMomentBridge.lean
/-!
Connect a rounded moment update to the genuine reciprocal prime product.
The candidate list only needs to cover all primes in the block; it may also
contain composites. Its correctness is separate from the arithmetic update.
-/

namespace RosserMomentBridge

open AlternativeProductMoments

noncomputable def reciprocalProduct (n : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE n, (((p : ℝ) - 1) / p)

theorem reciprocalProduct_nonneg (n : ℕ) : 0 ≤ reciprocalProduct n := by
  apply Finset.prod_nonneg
  intro p hp
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesLE hp
  exact div_nonneg (by linarith) (by linarith)

/-- The list product bounds the product over new primes in (a,b]. -/
theorem candidate_product_le_prime_block (a b : ℕ) (ds : List ℕ)
    (ha : 2 ≤ a) (hds : ds.Nodup)
    (hbounds : ∀ d ∈ ds, 0 < d ∧ d ≤ b - a)
    (hcover : ∀ p : ℕ, Nat.Prime p → a < p → p ≤ b → p - a ∈ ds) :
    (ds.map (fun (d : ℕ) => 1 - 1 / ((a : ℝ) + d))).prod ≤
      ∏ p ∈ Nat.primesLE b \ Nat.primesLE a, (((p : ℝ) - 1) / p) := by
  let ps := ds.map (fun (d : ℕ) => a + d)
  have hps : ps.Nodup := List.Nodup.map (by intro x y h; dsimp at h; omega) hds
  have hps_bounds : ∀ p ∈ ps.toFinset, a < p ∧ p ≤ b := by
    intro p hp
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    have hb := hbounds d hd
    omega
  have hsubset : Nat.primesLE b \ Nat.primesLE a ⊆ ps.toFinset := by
    intro p hp
    obtain ⟨hpb, hpa⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpb', hpprime⟩ := Nat.mem_primesLE.mp hpb
    have hap : a < p := by
      by_contra h
      exact hpa (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨p - a, hcover p hpprime hap hpb', by omega⟩
  have hbound := RosserProductCertificate.reciprocal_product_of_superset
    (Nat.primesLE b \ Nat.primesLE a) ps.toFinset hsubset
    (by intro p hp; have h := hps_bounds p hp; omega)
  have hprod :
      (∏ p ∈ ps.toFinset, (((p : ℝ) - 1) / p)) =
        (ds.map (fun (d : ℕ) => 1 - 1 / ((a : ℝ) + d))).prod := by
    rw [List.prod_toFinset _ hps]
    change ((ds.map (fun (d : ℕ) => a + d)).map
      (fun (p : ℕ) => ((p : ℝ) - 1) / p)).prod = _
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro d _
    have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
    have had : (0 : ℝ) < a + d := by positivity
    simp only [Function.comp_def, Nat.cast_add]
    field_simp
  rwa [hprod] at hbound

/-- A verified update of the reciprocal product across one whole block.
Every prime in (a,b] must survive the candidate sieve. Extra composite
candidates are harmless because their factors lie between zero and one. -/
theorem momentStep_reciprocalProduct (D v a b : ℕ) (ds : List ℕ)
    (hD : 0 < D) (hab : a ≤ b) (ha : 2 ≤ a) (hds : ds.Nodup)
    (hbounds : ∀ d ∈ ds, 0 < d ∧ d ≤ b - a)
    (hcover : ∀ p : ℕ, Nat.Prime p → a < p → p ≤ b → p - a ∈ ds)
    (hfirst : firstMoment ds ≤ ds.length * a)
    (hupper : upperNumerator a ds ≤ a ^ 3)
    (hv : (v : ℝ) / D ≤ reciprocalProduct a) :
    (momentStep v a ds : ℝ) / D ≤ reciprocalProduct b := by
  have hstep := momentStep_sound D v a ds (reciprocalProduct a)
    hD ha hfirst hupper hv
  have hblock := candidate_product_le_prime_block a b ds ha hds hbounds hcover
  have hsplit :
      reciprocalProduct a *
        (∏ p ∈ Nat.primesLE b \ Nat.primesLE a, (((p : ℝ) - 1) / p)) =
        reciprocalProduct b := by
    unfold reciprocalProduct
    rw [mul_comm]
    exact Finset.prod_sdiff (Nat.primesLE_mono hab)
  calc
    (momentStep v a ds : ℝ) / D ≤
        reciprocalProduct a * (ds.map (fun (d : ℕ) => 1 - 1 / ((a : ℝ) + d))).prod :=
      hstep
    _ ≤ reciprocalProduct a *
        (∏ p ∈ Nat.primesLE b \ Nat.primesLE a, (((p : ℝ) - 1) / p)) :=
      mul_le_mul_of_nonneg_left hblock (reciprocalProduct_nonneg a)
    _ = reciprocalProduct b := hsplit

end RosserMomentBridge

-- Source: Solutions/RosserBernoulli.lean
/-! An elementary lower bound for the product of prime factors in a block. -/

namespace RosserBernoulli

theorem one_sub_sum_le_prod {α : Type*} (s : Finset α) (u : α → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ u i) (h1 : ∀ i ∈ s, u i ≤ 1) :
    1 - ∑ i ∈ s, u i ≤ ∏ i ∈ s, (1 - u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hui0 : 0 ≤ u i := h0 i (Finset.mem_insert_self _ _)
    have hui1 : u i ≤ 1 := h1 i (Finset.mem_insert_self _ _)
    have htail0 : ∀ j ∈ s, 0 ≤ u j := by
      intro j hj
      exact h0 j (Finset.mem_insert_of_mem hj)
    have htail1 : ∀ j ∈ s, u j ≤ 1 := by
      intro j hj
      exact h1 j (Finset.mem_insert_of_mem hj)
    have hs0 : 0 ≤ ∑ j ∈ s, u j := Finset.sum_nonneg htail0
    have htail := ih htail0 htail1
    have hmul := mul_le_mul_of_nonneg_left htail (by linarith : 0 ≤ 1 - u i)
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    nlinarith only [hmul, hui0, hs0]

theorem prime_block_lower (a n k : ℕ) (ha : 2 ≤ a) (han : a ≤ n)
    (hcard : (Nat.primesLE n \ Nat.primesLE a).card ≤ k) :
    1 - (k : ℝ) / (a + 1) ≤
      ∏ p ∈ Nat.primesLE n \ Nat.primesLE a, (((p : ℝ) - 1) / p) := by
  let s := Nat.primesLE n \ Nat.primesLE a
  have hpa : ∀ p ∈ s, a < p := by
    intro p hp
    have hp' := Finset.mem_sdiff.mp hp
    have hprime := (Nat.mem_primesLE.mp hp'.1).2
    by_contra h
    exact hp'.2 (Nat.mem_primesLE.mpr ⟨by omega, hprime⟩)
  have hp2 : ∀ p ∈ s, (2 : ℝ) ≤ p := by
    intro p hp
    exact_mod_cast (show 2 ≤ p by have := hpa p hp; omega)
  have h0 : ∀ p ∈ s, (0 : ℝ) ≤ 1 / p := by
    intro p hp
    positivity
  have h1 : ∀ p ∈ s, (1 : ℝ) / p ≤ 1 := by
    intro p hp
    have h := hp2 p hp
    apply (div_le_iff₀ (by linarith : (0 : ℝ) < p)).mpr
    linarith
  have hpoint : ∀ p ∈ s, (1 : ℝ) / p ≤ 1 / (a + 1) := by
    intro p hp
    have h := hpa p hp
    have h' : (a + 1 : ℝ) ≤ p := by exact_mod_cast h
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) h'
  have hsum : (∑ p ∈ s, (1 : ℝ) / p) ≤ (k : ℝ) / (a + 1) := by
    calc
      (∑ p ∈ s, (1 : ℝ) / p) ≤ ∑ _p ∈ s, (1 : ℝ) / (a + 1) :=
        Finset.sum_le_sum hpoint
      _ = (s.card : ℝ) / (a + 1) := by simp [div_eq_mul_inv]
      _ ≤ (k : ℝ) / (a + 1) :=
        div_le_div_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have hb := one_sub_sum_le_prod s (fun p => (1 : ℝ) / p) h0 h1
  have heq : (∏ p ∈ s, (1 - (1 : ℝ) / p)) =
      ∏ p ∈ s, (((p : ℝ) - 1) / p) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 : (0 : ℝ) < p := by have := hp2 p hp; linarith
    field_simp
    <;> ring
  calc
    1 - (k : ℝ) / (a + 1) ≤ 1 - ∑ p ∈ s, (1 : ℝ) / p := by linarith only [hsum]
    _ ≤ ∏ p ∈ s, (1 - (1 : ℝ) / p) := hb
    _ = _ := heq

theorem reciprocal_prefix_lower (a n k : ℕ) (ha : 2 ≤ a) (han : a ≤ n)
    (hcard : (Nat.primesLE n \ Nat.primesLE a).card ≤ k) :
    RosserMomentBridge.reciprocalProduct a * (1 - (k : ℝ) / (a + 1)) ≤
      RosserMomentBridge.reciprocalProduct n := by
  have hblock := prime_block_lower a n k ha han hcard
  have hnonneg := RosserMomentBridge.reciprocalProduct_nonneg a
  have hmul := mul_le_mul_of_nonneg_left hblock hnonneg
  have hsplit : RosserMomentBridge.reciprocalProduct a *
      (∏ p ∈ Nat.primesLE n \ Nat.primesLE a, (((p : ℝ) - 1) / p)) =
      RosserMomentBridge.reciprocalProduct n := by
    unfold RosserMomentBridge.reciprocalProduct
    rw [mul_comm]
    exact Finset.prod_sdiff (Nat.primesLE_mono han)
  exact hmul.trans_eq hsplit

end RosserBernoulli

-- Source: Solutions/RosserPrefixBounds.lean
/-! Elementary interval bounds for the fast finite Rosser certificate. -/

namespace RosserPrefixBounds

theorem log_step (a b x : ℝ) (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    (x - a) / b ≤ Real.log x - Real.log a := by
  have hx : 0 < x := lt_of_lt_of_le ha hax
  have hb : 0 < b := lt_of_lt_of_le hx hxb
  have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hx ha)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt ha)] at hlog
  have heq : 1 - (x / a)⁻¹ = (x - a) / x := by
    field_simp
  rw [heq] at hlog
  exact (div_le_div_of_nonneg_left (sub_nonneg.mpr hax) hx hxb).trans hlog

theorem sqrt_reciprocal_step (a x : ℝ) (ha : 0 < a) (hax : a ≤ x) :
    -(x - a) / (a * Real.sqrt a) ≤
      2 / Real.sqrt x - 2 / Real.sqrt a := by
  let s := Real.sqrt x
  let t := Real.sqrt a
  have hx : 0 < x := lt_of_lt_of_le ha hax
  have hs : 0 < s := Real.sqrt_pos.mpr hx
  have ht : 0 < t := Real.sqrt_pos.mpr ha
  have hst : t ≤ s := Real.sqrt_le_sqrt hax
  have hsa : s ^ 2 = x := Real.sq_sqrt hx.le
  have hta : t ^ 2 = a := Real.sq_sqrt ha.le
  have hden : 2 * a * t ≤ s * t * (s + t) := by
    have hfactor : 0 ≤ t * (s - t) * (s + 2 * t) := by positivity
    calc
      2 * a * t = 2 * t ^ 3 := by rw [← hta]; ring
      _ ≤ s * t * (s + t) := by nlinarith only [hfactor]
  have hdenpos : 0 < s * t * (s + t) := by positivity
  have hatpos : 0 < a * t := by positivity
  have hfrac : 2 / (s * t * (s + t)) ≤ 1 / (a * t) := by
    apply (div_le_div_iff₀ hdenpos hatpos).mpr
    nlinarith only [hden]
  have hmul := mul_le_mul_of_nonneg_right hfrac (sub_nonneg.mpr hax)
  have hidentity : 2 / t - 2 / s =
      (x - a) * (2 / (s * t * (s + t))) := by
    rw [← hsa, ← hta]
    field_simp
    <;> ring
  have hnegative : -(x - a) * (1 / (a * t)) ≤
      -(x - a) * (2 / (s * t * (s + t))) := by
    simpa only [neg_mul, mul_comm] using neg_le_neg hmul
  calc
    -(x - a) / (a * Real.sqrt a) = -(x - a) * (1 / (a * t)) := by
      dsimp [t]; ring
    _ ≤ -(x - a) * (2 / (s * t * (s + t))) := hnegative
    _ = -((x - a) * (2 / (s * t * (s + t)))) := by ring
    _ = -(2 / t - 2 / s) := by rw [← hidentity]
    _ = 2 / s - 2 / t := by ring
    _ = 2 / Real.sqrt x - 2 / Real.sqrt a := rfl

theorem log_sqrt_linear (a b x : ℝ) (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    Real.log a + 2 / Real.sqrt a +
        (1 / b - 1 / (a * Real.sqrt a)) * (x - a) ≤
      Real.log x + 2 / Real.sqrt x := by
  have hlog := log_step a b x ha hax hxb
  have hsqrt := sqrt_reciprocal_step a x ha hax
  simp only [neg_div] at hsqrt
  calc
    Real.log a + 2 / Real.sqrt a +
        (1 / b - 1 / (a * Real.sqrt a)) * (x - a) =
      Real.log a + 2 / Real.sqrt a +
        (x - a) / b - (x - a) / (a * Real.sqrt a) := by ring
    _ ≤ Real.log x + 2 / Real.sqrt x := by linarith only [hlog, hsqrt]

theorem reciprocal_barrier_chord (A U B C h d : ℝ)
    (hA : 0 ≤ A) (hU : 0 ≤ U) (hB : 0 < B) (hC : 0 ≤ C)
    (hd : 0 ≤ d) (hdh : d ≤ h) :
    A * (1 - U / B) + A * U * C / (B * (B + C * h)) * d ≤
      A * (1 - U / (B + C * d)) := by
  have hh : 0 ≤ h := le_trans hd hdh
  have hbh : 0 < B + C * h := by positivity
  have hbd : 0 < B + C * d := by positivity
  have hhd : 0 ≤ h - d := sub_nonneg.mpr hdh
  have hnum : 0 ≤ A * U * C ^ 2 * d * (h - d) := by positivity
  have hden : 0 < B * (B + C * d) * (B + C * h) := by positivity
  have hid :
      A * (1 - U / (B + C * d)) -
        (A * (1 - U / B) + A * U * C / (B * (B + C * h)) * d) =
      (A * U * C ^ 2 * d * (h - d)) /
        (B * (B + C * d) * (B + C * h)) := by
    field_simp
    <;> ring
  have hnonneg := div_nonneg hnum hden.le
  linarith only [hid, hnonneg]

/-- A lower affine envelope for the full real-valued target on an interval. -/
theorem target_linear_lower (a b x g B C : ℝ)
    (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b)
    (hg : 0 ≤ g) (hgamma : g ≤ Real.exp Real.eulerMascheroniConstant)
    (hB : B ≤ g * (Real.log a + 2 / Real.sqrt a))
    (hC : C ≤ g * (1 / b - 1 / (a * Real.sqrt a)))
    (hFx : 0 ≤ Real.log x + 2 / Real.sqrt x) :
    B + C * (x - a) ≤
      Real.exp Real.eulerMascheroniConstant *
        (Real.log x + 2 / Real.sqrt x) := by
  have hd : 0 ≤ x - a := sub_nonneg.mpr hax
  have hlin := log_sqrt_linear a b x ha hax hxb
  have hC' := mul_le_mul_of_nonneg_right hC hd
  have hlin' := mul_le_mul_of_nonneg_left hlin hg
  have hgamma' := mul_le_mul_of_nonneg_right hgamma hFx
  nlinarith only [hB, hC', hlin', hgamma']

/-- Integer square-root bounds may be used with opposite rounding directions
in the intercept and the slope. -/
theorem rounded_target_linear_lower (a b x g L r S : ℝ)
    (ha : 1 ≤ a) (hax : a ≤ x) (hxb : x ≤ b)
    (hg : 0 ≤ g) (hgamma : g ≤ Real.exp Real.eulerMascheroniConstant)
    (hL : L ≤ Real.log a) (hr : 0 < r) (hrS : r ≤ Real.sqrt a)
    (hS : 0 < S) (hSa : Real.sqrt a ≤ S) :
    g * (L + 2 / S) +
      g * (1 / b - 1 / (a * r)) * (x - a) ≤
      Real.exp Real.eulerMascheroniConstant *
        (Real.log x + 2 / Real.sqrt x) := by
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr (by linarith)
  have hSdiv : 2 / S ≤ 2 / Real.sqrt a :=
    div_le_div_of_nonneg_left (by norm_num) hsa hSa
  have hB : g * (L + 2 / S) ≤
      g * (Real.log a + 2 / Real.sqrt a) := by
    apply mul_le_mul_of_nonneg_left _ hg
    linarith only [hL, hSdiv]
  have har : 0 < a * r := mul_pos (by linarith) hr
  have hsar : a * r ≤ a * Real.sqrt a :=
    mul_le_mul_of_nonneg_left hrS (by linarith)
  have hRdiv : 1 / (a * Real.sqrt a) ≤ 1 / (a * r) :=
    div_le_div_of_nonneg_left (by norm_num) har hsar
  have hC : g * (1 / b - 1 / (a * r)) ≤
      g * (1 / b - 1 / (a * Real.sqrt a)) := by
    apply mul_le_mul_of_nonneg_left _ hg
    linarith only [hRdiv]
  have hx1 : (1 : ℝ) ≤ x := ha.trans hax
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  have hFx : 0 ≤ Real.log x + 2 / Real.sqrt x := by positivity
  exact target_linear_lower a b x g _ _ (by linarith) hax hxb hg
    hgamma hB hC hFx

/-- A strict count bound in a prefix converts a reciprocal-product lower
bound into a strict upper bound on the Euler product. -/
theorem prefix_count_to_product (a n k : ℕ) (q T : ℝ)
    (ha : 2 ≤ a) (han : a ≤ n) (hq : 0 < q) (hT : 0 < T)
    (hv : q ≤ RosserMomentBridge.reciprocalProduct a)
    (hcard : (Nat.primesLE n \ Nat.primesLE a).card ≤ k)
    (hcount : (k : ℝ) < (a + 1) * (1 - (1 / q) / T)) :
    RosserProductCertificate.eulerProduct n < T := by
  let A : ℝ := a + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hfrac : (k : ℝ) / A < 1 - (1 / q) / T := by
    apply (div_lt_iff₀ hA).mpr
    dsimp [A] at hcount ⊢
    nlinarith only [hcount]
  have hfactor : 0 < 1 - (k : ℝ) / A := by
    have : 0 < (1 / q) / T := by positivity
    linarith only [hfrac, this]
  have hqprod : q * (1 - (k : ℝ) / A) ≤
      RosserMomentBridge.reciprocalProduct n := by
    have hmul := mul_le_mul_of_nonneg_right hv hfactor.le
    exact hmul.trans (by simpa only [A] using
      RosserBernoulli.reciprocal_prefix_lower a n k ha han hcard)
  have hbar : 1 < T * (q * (1 - (k : ℝ) / A)) := by
    have hqt : 0 < q * T := mul_pos hq hT
    have hrewrite : (1 / q) / T = 1 / (q * T) := by ring
    rw [hrewrite] at hfrac
    have h : 1 < (1 - (k : ℝ) / A) * (q * T) :=
      (div_lt_iff₀ hqt).mp (by linarith only [hfrac])
    nlinarith only [h]
  have hr : 0 < q * (1 - (k : ℝ) / A) := mul_pos hq hfactor
  have hupper := RosserProductCertificate.eulerProduct_le_of_reciprocal n
    _ hr hqprod
  have hstrict : 1 / (q * (1 - (k : ℝ) / A)) < T :=
    (div_lt_iff₀ hr).mpr (by nlinarith only [hbar])
  exact hupper.trans_lt hstrict

/-- A certified affine count bound at any point of a block suffices for the
prime product at that point. -/
theorem affine_prefix_to_product (a n k : ℕ) (q B C h d I M : ℝ)
    (ha : 2 ≤ a) (han : a ≤ n) (hq : 0 < q) (hB : 0 < B)
    (hC : 0 ≤ C) (hd : 0 ≤ d) (hdh : d ≤ h)
    (hv : q ≤ RosserMomentBridge.reciprocalProduct a)
    (hcard : (Nat.primesLE n \ Nat.primesLE a).card ≤ k)
    (hI : I ≤ (a + 1) * (1 - (1 / q) / B))
    (hM : M ≤ (a + 1) * (1 / q) * C / (B * (B + C * h)))
    (hk : (k : ℝ) < I + M * d) :
    RosserProductCertificate.eulerProduct n < B + C * d := by
  have hT : 0 < B + C * d := by positivity
  have hchord := reciprocal_barrier_chord (a + 1 : ℝ) (1 / q) B C h d
    (by positivity) (by positivity) hB hC hd hdh
  have hMd := mul_le_mul_of_nonneg_right hM hd
  have hbound : (k : ℝ) < (a + 1) * (1 - (1 / q) / (B + C * d)) := by
    linarith only [hk, hI, hMd, hchord]
  exact prefix_count_to_product a n k q (B + C * d)
    ha han hq hT hv hcard hbound

end RosserPrefixBounds

-- Source: Solutions/RosserPrefixParams.lean
/-! Exact arithmetic for the downward-rounded affine barrier parameters. -/

namespace RosserPrefixParams

open RosserLogCertificate

private theorem forceNat_eq {α : Type} (n : ℕ) (f : ℕ → α) :
    RosserScan.forceNat n f = f n := by
  cases n <;> rfl

structure Parameters where
  intercept : ℕ
  slope : ℕ
  valid : Bool

def parameters (a b v : ℕ) : Parameters :=
  RosserScan.forceNat (Nat.sqrt a) fun r =>
  RosserScan.forceNat (178107239 * (logLower a * (r + 1) + 2 * scale)) fun bn =>
  RosserScan.forceNat (10 ^ 8 * scale * (r + 1)) fun bd =>
  RosserScan.forceNat (178107239 * (a * r - b)) fun cn =>
  RosserScan.forceNat (10 ^ 8 * b * a * r) fun cd =>
    ⟨16384 * (a + 1) * (v * bn - scale * bd) / (v * bn),
     16384 * (a + 1) * scale * cn * bd ^ 2 /
       (v * bn * (bn * cd + cn * bd * (b - a))),
     decide (4500 ≤ a ∧ a < b ∧ b ≤ 10 ^ 8 ∧ 0 < v ∧
       b < a * r ∧ scale * bd < v * bn)⟩

theorem parameters_valid (a b v : ℕ) (h : (parameters a b v).valid = true) :
    4500 ≤ a ∧ a < b ∧ b ≤ 10 ^ 8 ∧ 0 < v ∧
      b < a * Nat.sqrt a ∧
      scale * (10 ^ 8 * scale * (Nat.sqrt a + 1)) <
        v * (178107239 *
          (logLower a * (Nat.sqrt a + 1) + 2 * scale)) := by
  simpa only [parameters, forceNat_eq, decide_eq_true_eq] using h

theorem sqrt_bracket (a : ℕ) (ha : 1 ≤ a) :
    0 < (Nat.sqrt a : ℝ) ∧
      (Nat.sqrt a : ℝ) ≤ Real.sqrt a ∧
      Real.sqrt a ≤ (Nat.sqrt a + 1 : ℕ) := by
  have hr1 : 1 ≤ Nat.sqrt a := by
    apply Nat.le_sqrt.mpr
    simpa using ha
  have hr0 : (0 : ℝ) < Nat.sqrt a := by exact_mod_cast hr1
  have hlow : (Nat.sqrt a : ℝ) ^ 2 ≤ a := by
    exact_mod_cast Nat.sqrt_le' a
  have hhigh : (a : ℝ) ≤ (Nat.sqrt a + 1 : ℕ) ^ 2 := by
    exact_mod_cast (Nat.lt_succ_sqrt' a).le
  exact ⟨hr0, Real.le_sqrt_of_sq_le hlow,
    Real.sqrt_le_iff.mpr ⟨by positivity, hhigh⟩⟩

theorem intercept_lower (J A D v bn bd : ℕ)
    (hJ : 0 < J) (hv : 0 < v) (hbn : 0 < bn) (hbd : 0 < bd)
    (hsub : D * bd ≤ v * bn) :
    ((J * A * (v * bn - D * bd) / (v * bn) : ℕ) : ℝ) / J ≤
      (A : ℝ) * (1 - ((D : ℝ) / v) / ((bn : ℝ) / bd)) := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hbn' : (0 : ℝ) < bn := by exact_mod_cast hbn
  have hbd' : (0 : ℝ) < bd := by exact_mod_cast hbd
  have hsub' : ((v * bn - D * bd : ℕ) : ℝ) =
      (v : ℝ) * bn - D * bd := by
    rw [Nat.cast_sub hsub]
    push_cast
    ring
  have hround := Nat.cast_div_le
    (m := J * A * (v * bn - D * bd)) (n := v * bn) (α := ℝ)
  have heq :
      (((J * A * (v * bn - D * bd) : ℕ) : ℝ) / (v * bn : ℕ)) / J =
        (A : ℝ) * (1 - ((D : ℝ) / v) / ((bn : ℝ) / bd)) := by
    rw [Nat.cast_mul, Nat.cast_mul, hsub', Nat.cast_mul]
    field_simp
    <;> ring
  calc
    ((J * A * (v * bn - D * bd) / (v * bn) : ℕ) : ℝ) / J ≤
        (((J * A * (v * bn - D * bd) : ℕ) : ℝ) / (v * bn : ℕ)) / J :=
      div_le_div_of_nonneg_right hround hJ'.le
    _ = _ := heq

theorem slope_lower (J A D v bn bd cn cd h : ℕ)
    (hJ : 0 < J) (hv : 0 < v) (hbn : 0 < bn) (hbd : 0 < bd)
    (hcd : 0 < cd) :
    ((J * A * D * cn * bd ^ 2 /
        (v * bn * (bn * cd + cn * bd * h)) : ℕ) : ℝ) / J ≤
      (A : ℝ) * ((D : ℝ) / v) * ((cn : ℝ) / cd) /
        (((bn : ℝ) / bd) *
          ((bn : ℝ) / bd + ((cn : ℝ) / cd) * h)) := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hbn' : (0 : ℝ) < bn := by exact_mod_cast hbn
  have hbd' : (0 : ℝ) < bd := by exact_mod_cast hbd
  have hcd' : (0 : ℝ) < cd := by exact_mod_cast hcd
  have hden : 0 < v * bn * (bn * cd + cn * bd * h) := by
    have hterm : 0 < bn * cd := Nat.mul_pos hbn hcd
    positivity
  have hround := Nat.cast_div_le
    (m := J * A * D * cn * bd ^ 2)
    (n := v * bn * (bn * cd + cn * bd * h)) (α := ℝ)
  have heq :
      (((J * A * D * cn * bd ^ 2 : ℕ) : ℝ) /
        (v * bn * (bn * cd + cn * bd * h) : ℕ)) / J =
      (A : ℝ) * ((D : ℝ) / v) * ((cn : ℝ) / cd) /
        (((bn : ℝ) / bd) *
          ((bn : ℝ) / bd + ((cn : ℝ) / cd) * h)) := by
    push_cast
    field_simp
    <;> ring
  calc
    ((J * A * D * cn * bd ^ 2 /
        (v * bn * (bn * cd + cn * bd * h)) : ℕ) : ℝ) / J ≤
      (((J * A * D * cn * bd ^ 2 : ℕ) : ℝ) /
        (v * bn * (bn * cd + cn * bd * h) : ℕ)) / J :=
      div_le_div_of_nonneg_right hround hJ'.le
    _ = _ := heq

theorem intercept_value (D a r ell : ℕ) (hD : 0 < D) :
    ((178107239 * (ell * (r + 1) + 2 * D) : ℕ) : ℝ) /
        (10 ^ 8 * D * (r + 1) : ℕ) =
      (178107239 / 10 ^ 8 : ℝ) *
        ((ell : ℝ) / D + 2 / (r + 1)) := by
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hr' : (0 : ℝ) < r + 1 := by positivity
  push_cast
  field_simp
  <;> ring

theorem slope_value (a b r : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (hbar : b ≤ a * r) :
    ((178107239 * (a * r - b) : ℕ) : ℝ) /
        (10 ^ 8 * b * a * r : ℕ) =
      (178107239 / 10 ^ 8 : ℝ) *
        (1 / b - 1 / ((a : ℝ) * r)) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hbar]
  push_cast
  field_simp
  <;> ring

theorem parameters_intercept_lower (a b v : ℕ)
    (hvalid : (parameters a b v).valid = true) :
    ((parameters a b v).intercept : ℝ) / 16384 ≤
      (a + 1 : ℝ) *
        (1 - (1 / ((v : ℝ) / scale)) /
          ((178107239 / 10 ^ 8 : ℝ) *
            ((logLower a : ℝ) / scale +
              2 / (Nat.sqrt a + 1 : ℕ)))) := by
  rcases parameters_valid a b v hvalid with
    ⟨ha, hab, hbound, hv, hbar, hnum⟩
  let r := Nat.sqrt a
  let bn := 178107239 * (logLower a * (r + 1) + 2 * scale)
  let bd := 10 ^ 8 * scale * (r + 1)
  have hbn : 0 < bn := by
    dsimp [bn]
    have h2 : 0 < 2 * scale := Nat.mul_pos (by decide) scale_pos
    exact Nat.mul_pos (by decide) (by omega)
  have hbd : 0 < bd := by
    dsimp [bd]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) scale_pos) (by omega)
  have hnum' : scale * bd ≤ v * bn := by
    simpa only [bn, bd, r] using hnum.le
  have hi := intercept_lower 16384 (a + 1) scale v bn bd
    (by norm_num) hv hbn hbd hnum'
  have hbnval : ((bn : ℝ) / bd) =
      (178107239 / 10 ^ 8 : ℝ) *
        ((logLower a : ℝ) / scale + 2 / (r + 1 : ℕ)) :=
    by simpa only [bn, bd, Nat.cast_add, Nat.cast_one] using
      intercept_value scale a r (logLower a) scale_pos
  have hq : (1 : ℝ) / ((v : ℝ) / scale) = (scale : ℝ) / v := by
    have hv' : (0 : ℝ) < v := by exact_mod_cast hv
    have hD' : (0 : ℝ) < scale := by exact_mod_cast scale_pos
    field_simp
  change ((parameters a b v).intercept : ℝ) / 16384 ≤
    (a + 1 : ℝ) *
      (1 - (1 / ((v : ℝ) / scale)) /
        ((178107239 / 10 ^ 8 : ℝ) *
          ((logLower a : ℝ) / scale + 2 / (r + 1 : ℕ))))
  rw [hq, ← hbnval]
  simpa only [parameters, forceNat_eq, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, r, bn, bd] using hi

theorem parameters_slope_lower (a b v : ℕ)
    (hvalid : (parameters a b v).valid = true) :
    ((parameters a b v).slope : ℝ) / 16384 ≤
      (a + 1 : ℝ) * (1 / ((v : ℝ) / scale)) *
        ((178107239 / 10 ^ 8 : ℝ) *
          (1 / b - 1 / ((a : ℝ) * Nat.sqrt a))) /
        (((178107239 / 10 ^ 8 : ℝ) *
          ((logLower a : ℝ) / scale + 2 / (Nat.sqrt a + 1 : ℕ))) *
          ((178107239 / 10 ^ 8 : ℝ) *
            ((logLower a : ℝ) / scale + 2 / (Nat.sqrt a + 1 : ℕ)) +
            ((178107239 / 10 ^ 8 : ℝ) *
              (1 / b - 1 / ((a : ℝ) * Nat.sqrt a))) * (b - a : ℕ))) := by
  rcases parameters_valid a b v hvalid with
    ⟨ha, hab, hbound, hv, hbar, hnum⟩
  let r := Nat.sqrt a
  let bn := 178107239 * (logLower a * (r + 1) + 2 * scale)
  let bd := 10 ^ 8 * scale * (r + 1)
  let cn := 178107239 * (a * r - b)
  let cd := 10 ^ 8 * b * a * r
  have hbn : 0 < bn := by
    dsimp [bn]
    have h2 : 0 < 2 * scale := Nat.mul_pos (by decide) scale_pos
    exact Nat.mul_pos (by decide) (by omega)
  have hbd : 0 < bd := by
    dsimp [bd]
    exact Nat.mul_pos (Nat.mul_pos (by norm_num) scale_pos) (by omega)
  have hr : 0 < r := by
    have := (sqrt_bracket a (by omega : 1 ≤ a)).1
    exact_mod_cast this
  have hcd : 0 < cd := by
    dsimp [cd]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num)
      (by omega : 0 < b)) (by omega : 0 < a)) hr
  have hvalB : ((bn : ℝ) / bd) =
      (178107239 / 10 ^ 8 : ℝ) *
        ((logLower a : ℝ) / scale + 2 / (r + 1 : ℕ)) := by
    simpa only [bn, bd, Nat.cast_add, Nat.cast_one] using
      intercept_value scale a r (logLower a) scale_pos
  have hvalC : ((cn : ℝ) / cd) =
      (178107239 / 10 ^ 8 : ℝ) *
        (1 / b - 1 / ((a : ℝ) * r)) := by
    simpa only [cn, cd] using slope_value a b r
      (by omega) (by omega) hr hbar.le
  have hq : (1 : ℝ) / ((v : ℝ) / scale) = (scale : ℝ) / v := by
    have hv' : (0 : ℝ) < v := by exact_mod_cast hv
    have hD' : (0 : ℝ) < scale := by exact_mod_cast scale_pos
    field_simp
  have hs := slope_lower 16384 (a + 1) scale v bn bd cn cd (b - a)
    (by norm_num) hv hbn hbd hcd
  change ((parameters a b v).slope : ℝ) / 16384 ≤
    (a + 1 : ℝ) * (1 / ((v : ℝ) / scale)) *
      ((178107239 / 10 ^ 8 : ℝ) *
        (1 / b - 1 / ((a : ℝ) * r))) /
      (((178107239 / 10 ^ 8 : ℝ) *
        ((logLower a : ℝ) / scale + 2 / (r + 1 : ℕ))) *
        ((178107239 / 10 ^ 8 : ℝ) *
          ((logLower a : ℝ) / scale + 2 / (r + 1 : ℕ)) +
          ((178107239 / 10 ^ 8 : ℝ) *
            (1 / b - 1 / ((a : ℝ) * r))) * (b - a : ℕ)))
  rw [hq, ← hvalB, ← hvalC]
  simpa only [parameters, forceNat_eq, Nat.cast_add, Nat.cast_one,
    Nat.cast_ofNat, r, bn, bd, cn, cd] using hs

theorem parameterized_bound (a b v k : ℕ) (x : ℝ)
    (hvalid : (parameters a b v).valid = true)
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ b)
    (hv : ((v : ℝ) / scale) ≤ RosserMomentBridge.reciprocalProduct a)
    (hcard : (Nat.primesLE ⌊x⌋₊ \ Nat.primesLE a).card ≤ k)
    (hcount : (k : ℝ) <
      ((parameters a b v).intercept : ℝ) / 16384 +
        ((parameters a b v).slope : ℝ) / 16384 * (x - a)) :
    RosserBlockCheck.Bound x := by
  rcases parameters_valid a b v hvalid with
    ⟨ha, hab, hbmax, hv0, hbar, hnum⟩
  let r := Nat.sqrt a
  let g : ℝ := 178107239 / 10 ^ 8
  let L : ℝ := (logLower a : ℝ) / scale
  let S : ℝ := (r + 1 : ℕ)
  let B : ℝ := g * (L + 2 / S)
  let C : ℝ := g * (1 / b - 1 / ((a : ℝ) * r))
  let q : ℝ := (v : ℝ) / scale
  have hg : 0 ≤ g := by dsimp [g]; norm_num
  have hgamma : g ≤ Real.exp Real.eulerMascheroniConstant :=
    RosserProductCertificate.exp_gamma_lower
  have hsqrt := sqrt_bracket a (by omega : 1 ≤ a)
  have hr : 0 < (r : ℝ) := hsqrt.1
  have hrS : (r : ℝ) ≤ Real.sqrt a := hsqrt.2.1
  have hS : 0 < S := by dsimp [S]; positivity
  have hSa : Real.sqrt a ≤ S := hsqrt.2.2
  have hL : L ≤ Real.log a :=
    logLower_sound a (by omega : 1 ≤ a)
  have hB : 0 < B := by
    have hgp : 0 < g := by dsimp [g]; norm_num
    have hD : (0 : ℝ) < scale := by exact_mod_cast scale_pos
    have hL0 : 0 ≤ L :=
      div_nonneg (by exact_mod_cast Nat.zero_le (logLower a))
        (by exact_mod_cast Nat.zero_le scale)
    have h2 : 0 < 2 / S := by positivity
    exact mul_pos hgp (by linarith only [hL0, h2])
  have hC : 0 ≤ C := by
    have hval := slope_value a b r (by omega) (by omega)
      (by exact_mod_cast hr) hbar.le
    have hnonneg : (0 : ℝ) ≤
        ((178107239 * (a * r - b) : ℕ) : ℝ) /
          (10 ^ 8 * b * a * r : ℕ) := by positivity
    dsimp [C, g, r]
    rw [hval] at hnonneg
    exact hnonneg
  have hq : 0 < q := by
    dsimp [q]
    have hD : (0 : ℝ) < scale := by exact_mod_cast scale_pos
    have hv' : (0 : ℝ) < v := by exact_mod_cast hv0
    positivity
  have hI : ((parameters a b v).intercept : ℝ) / 16384 ≤
      (a + 1 : ℝ) * (1 - (1 / q) / B) :=
    parameters_intercept_lower a b v hvalid
  have hM : ((parameters a b v).slope : ℝ) / 16384 ≤
      (a + 1 : ℝ) * (1 / q) * C / (B * (B + C * (b - a : ℕ))) :=
    parameters_slope_lower a b v hvalid
  have hfloor : a ≤ ⌊x⌋₊ := Nat.le_floor hax
  have hrealha : (2 : ℝ) ≤ a := by exact_mod_cast (show 2 ≤ a by omega)
  have hd : 0 ≤ x - a := sub_nonneg.mpr hax
  have hdh : x - (a : ℝ) ≤ (b - a : ℕ) := by
    rw [Nat.cast_sub hab.le]
    linarith only [hxb]
  have hp := RosserPrefixBounds.affine_prefix_to_product a ⌊x⌋₊ k q B C
    (b - a : ℕ) (x - a)
    (((parameters a b v).intercept : ℝ) / 16384)
    (((parameters a b v).slope : ℝ) / 16384)
    (by omega) hfloor hq hB hC hd hdh hv hcard hI hM hcount
  have ht := RosserPrefixBounds.rounded_target_linear_lower
    (a : ℝ) b x g L r S (by linarith only [hrealha]) hax hxb hg hgamma
    hL hr hrS hS hSa
  change RosserProductCertificate.eulerProduct ⌊x⌋₊ <
    Real.exp Real.eulerMascheroniConstant * Real.log x +
      2 * Real.exp Real.eulerMascheroniConstant / Real.sqrt x
  calc
    RosserProductCertificate.eulerProduct ⌊x⌋₊ < B + C * (x - a) := hp
    _ ≤ Real.exp Real.eulerMascheroniConstant *
        (Real.log x + 2 / Real.sqrt x) := ht
    _ = _ := by ring

end RosserPrefixParams

-- Source: Solutions/RosserBitSieve.lean
/-!
A bit sieve using only natural-number arithmetic, suitable for kernel reduction.
The divisors are untrusted data: they need only satisfy 2 <= d < a.
No claim that the divisor list is complete or consists of primes is required.
-/

namespace RosserBitSieve

theorem periodicMask_eq_sum (d count : ℕ) (hd : 0 < d) :
    periodicMask d count = ∑ i ∈ Finset.range count, (2 ^ d) ^ i := by
  rw [Nat.geomSum_eq (Nat.one_lt_two_pow (Nat.ne_of_gt hd)), periodicMask, pow_mul]

theorem periodicMask_succ (d count : ℕ) (hd : 0 < d) :
    periodicMask d (count + 1) = 2 ^ d * periodicMask d count + 1 := by
  rw [periodicMask_eq_sum d (count + 1) hd, periodicMask_eq_sum d count hd,
    geom_sum_succ]

/-- Every set bit in a periodic mask has index divisible by d. -/
theorem periodicMask_bit_dvd (d count i : ℕ) (hd : 0 < d)
    (hbit : (periodicMask d count).testBit i = true) : d ∣ i := by
  induction count generalizing i with
  | zero => simp [periodicMask] at hbit
  | succ count ih =>
    rw [periodicMask_succ d count hd,
      Nat.testBit_two_pow_mul_add _ (Nat.one_lt_two_pow (Nat.ne_of_gt hd))] at hbit
    split at hbit
    · have hone : (1 : ℕ).testBit i = decide (i = 0) := by
        simpa only [Nat.pow_zero, eq_comm] using (Nat.testBit_two_pow (n := 0) (m := i))
      rw [hone] at hbit
      have hi : i = 0 := of_decide_eq_true hbit
      subst i
      exact dvd_zero d
    · rename_i hi
      have hdiv := ih (i - d) hbit
      have heq : i = (i - d) + d := by omega
      rw [heq]
      exact dvd_add hdiv (dvd_refl d)

theorem first_multiple (a d : ℕ) (hd : 0 < d) :
    d ∣ a + (d - a % d) % d := by
  apply Nat.dvd_of_mod_eq_zero
  by_cases hz : a % d = 0
  · simp [hz]
  · have hm := Nat.mod_lt a hd
    have hsmall : d - a % d < d := by omega
    rw [Nat.mod_eq_of_lt hsmall, Nat.add_mod]
    rw [Nat.mod_eq_of_lt hsmall, Nat.add_sub_of_le hm.le, Nat.mod_self]

theorem divisorMask_bit_dvd (a len d i : ℕ) (hd : 0 < d)
    (hbit : (divisorMask a len d).testBit i = true) : d ∣ a + i := by
  unfold divisorMask at hbit
  rw [Nat.testBit_mul_two_pow, Bool.and_eq_true] at hbit
  obtain ⟨hoffset, hperiodic⟩ := hbit
  have hoffset' : (d - a % d) % d ≤ i := of_decide_eq_true hoffset
  have hp := periodicMask_bit_dvd d _ _ hd hperiodic
  have hfirst := first_multiple a d hd
  have heq : a + i = (a + (d - a % d) % d) + (i - (d - a % d) % d) := by omega
  rw [heq]
  exact dvd_add hfirst hp

theorem divisorMask_preserves_prime (a len d i : ℕ)
    (hd : 2 ≤ d) (hda : d < a) (hp : Nat.Prime (a + i)) :
    (divisorMask a len d).testBit i = false := by
  apply Bool.eq_false_iff.mpr
  intro hbit
  have hdiv := divisorMask_bit_dvd a len d i (by omega) hbit
  rcases hp.eq_one_or_self_of_dvd d hdiv with h | h <;> omega

theorem compositeMask_preserves_prime (divisors : List ℕ) (a len i : ℕ)
    (hds : ∀ d ∈ divisors, 2 ≤ d ∧ d < a) (hp : Nat.Prime (a + i)) :
    (compositeMask divisors a len).testBit i = false := by
  suffices h : ∀ mask : ℕ, mask.testBit i = false →
      (divisors.foldl (fun mask d => mask ||| divisorMask a len d) mask).testBit i = false by
    exact h 0 (by simp)
  induction divisors with
  | nil => simp
  | cons d ds ih =>
    intro mask hmask
    apply ih (fun q hq => hds q (by simp [hq]))
    rw [Nat.testBit_or, hmask, divisorMask_preserves_prime a len d i
      (hds d (by simp)).1 (hds d (by simp)).2 hp]
    rfl

theorem candidateMask_preserves_prime (divisors : List ℕ) (a len i : ℕ)
    (hds : ∀ d ∈ divisors, 2 ≤ d ∧ d < a) (hi : i < len)
    (hp : Nat.Prime (a + i)) :
    (candidateMask divisors a len).testBit i = true := by
  simp [candidateMask, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, hi, compositeMask_preserves_prime divisors a len i hds hp]

theorem mem_enumBits (depth start mask x : ℕ) :
    x ∈ enumBits depth start mask ↔
      start ≤ x ∧ x < start + 2 ^ depth ∧ mask.testBit (x - start) = true := by
  induction depth generalizing start mask with
  | zero =>
    simp only [enumBits, Nat.pow_zero]
    split
    · rename_i h
      have hm : mask % 2 = 1 := by simpa using h
      constructor
      · intro hx
        have hx' : x = start := by simpa using hx
        subst x
        simp [Nat.testBit_eq_decide_div_mod_eq, hm]
      · intro hx
        have hx' : x = start := by omega
        simp [hx']
    · rename_i h
      have hm : mask % 2 ≠ 1 := by simpa using h
      constructor
      · simp
      · intro hx
        have hx' : x = start := by omega
        subst x
        simp [Nat.testBit_eq_decide_div_mod_eq, hm] at hx
  | succ depth ih =>
    by_cases hm : mask = 0
    · subst mask
      simp [enumBits]
    · simp only [enumBits, beq_iff_eq, hm, if_false, List.mem_append, ih,
        Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Bool.and_eq_true,
        decide_eq_true_eq, Nat.pow_succ]
      constructor
      · intro hx
        rcases hx with ⟨hlo, hhi, _, hb⟩ | ⟨hlo, hhi, hb⟩
        · exact ⟨hlo, by omega, hb⟩
        · refine ⟨by omega, by omega, ?_⟩
          have heq : x - (start + 2 ^ depth) + 2 ^ depth = x - start := by omega
          simpa only [heq] using hb
      · intro ⟨hlo, hhi, hb⟩
        by_cases hleft : x < start + 2 ^ depth
        · exact Or.inl ⟨hlo, hleft, by omega, hb⟩
        · right
          refine ⟨by omega, by omega, ?_⟩
          have heq : x - (start + 2 ^ depth) + 2 ^ depth = x - start := by omega
          simpa only [heq] using hb

theorem enumBits_nodup (depth start mask : ℕ) : (enumBits depth start mask).Nodup := by
  induction depth generalizing start mask with
  | zero => simp only [enumBits]; split <;> simp
  | succ depth ih =>
    simp only [enumBits]
    split
    · simp
    · apply List.Nodup.append (ih _ _) (ih _ _)
      apply List.disjoint_left.mpr
      intro x hx hx'
      have hleft := (mem_enumBits _ _ _ _).mp hx
      have hright := (mem_enumBits _ _ _ _).mp hx'
      omega

theorem candidateMask_bit (divisors : List ℕ) (a len i : ℕ) :
    (candidateMask divisors a len).testBit i =
      (decide (i < len) && !(compositeMask divisors a len).testBit i) := by
  by_cases hi : i < len <;>
    simp [candidateMask, Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
      Nat.testBit_mod_two_pow, hi]

theorem offsets_lt (divisors : List ℕ) (depth a len i : ℕ)
    (hi : i ∈ offsets divisors depth a len) : i < len := by
  have hb := (mem_enumBits _ _ _ _).mp hi
  simp only [Nat.sub_zero, candidateMask_bit, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact hb.2.2.1

theorem offsets_preserve_primes (divisors : List ℕ) (depth a len p : ℕ)
    (hds : ∀ d ∈ divisors, 2 ≤ d ∧ d < a) (hlen : len ≤ 2 ^ depth)
    (hpa : a ≤ p) (hpB : p < a + len) (hp : Nat.Prime p) :
    p - a ∈ offsets divisors depth a len := by
  apply (mem_enumBits _ _ _ _).mpr
  refine ⟨Nat.zero_le _, by omega, ?_⟩
  simp only [Nat.sub_zero]
  apply candidateMask_preserves_prime divisors a len (p - a) hds (by omega)
  simpa only [Nat.add_sub_of_le hpa] using hp

theorem offsets_nodup (divisors : List ℕ) (depth a len : ℕ) :
    (offsets divisors depth a len).Nodup := enumBits_nodup _ _ _

theorem mem_windowOffsets (depth mask shift len d : ℕ) :
    d ∈ windowOffsets depth mask shift len ↔
      0 < d ∧ d ≤ len ∧ d ≤ 2 ^ depth ∧ mask.testBit (d - 1 + shift) = true := by
  simp only [windowOffsets, List.mem_map, mem_enumBits, Nat.zero_add, Nat.sub_zero,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨i, ⟨_, hi, hlen, hb⟩, rfl⟩
    exact ⟨by omega, by omega, by omega, by simpa using hb⟩
  · rintro ⟨hd, hlen, hdepth, hb⟩
    exact ⟨d - 1, ⟨Nat.zero_le _, by omega, by omega, hb⟩, by omega⟩

theorem windowOffsets_nodup (depth mask shift len : ℕ) :
    (windowOffsets depth mask shift len).Nodup := by
  apply List.Nodup.map _ (enumBits_nodup _ _ _)
  intro a b h
  change a + 1 = b + 1 at h
  omega

end RosserBitSieve

-- Source: Solutions/RosserPackedBarrier.lean
/-! Arithmetic lemmas for the packed prefix-count certificate. -/

namespace RosserPackedBarrier

theorem forceNat_eq {α : Sort _} (n : ℕ) (f : ℕ → α) :
    RosserScan.forceNat n f = f n := by
  cases n <;> rfl

def candidateCount (mask d : ℕ) : ℕ :=
  ((List.range d).filter (fun i => mask.testBit i)).length

/-- Little-endian packing with a fixed number of digits. -/
def pack (q : ℕ) : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, f => f 0 + q * pack q n (fun i => f (i + 1))

theorem pack_congr (q n : ℕ) {f g : ℕ → ℕ}
    (h : ∀ i < n, f i = g i) : pack q n f = pack q n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [pack]
    rw [h 0 (by omega), ih (fun i hi => h (i + 1) (by omega))]

theorem pack_add (q n : ℕ) (f g : ℕ → ℕ) :
    pack q n (fun i => f i + g i) = pack q n f + pack q n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [pack, ih]; ring

theorem pack_mul (q n c : ℕ) (f : ℕ → ℕ) :
    pack q n (fun i => c * f i) = c * pack q n f := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih => simp only [pack, ih]; ring

theorem pack_mono (q n : ℕ) {f g : ℕ → ℕ}
    (h : ∀ i < n, f i ≤ g i) : pack q n f ≤ pack q n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    exact Nat.add_le_add (h 0 (by omega))
      (Nat.mul_le_mul_left q (ih (fun i hi => h (i + 1) (by omega))))

theorem pack_sub (q n : ℕ) {f g : ℕ → ℕ}
    (h : ∀ i < n, g i ≤ f i) :
    pack q n (fun i => f i - g i) = pack q n f - pack q n g := by
  have heq : pack q n (fun i => f i - g i) + pack q n g = pack q n f := by
    rw [← pack_add]
    exact pack_congr q n (fun i hi => Nat.sub_add_cancel (h i hi))
  omega

theorem pack_lt (q n : ℕ) (hq : 0 < q) {f : ℕ → ℕ}
    (h : ∀ i < n, f i < q) : pack q n f < q ^ n := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    have htail := ih (fun i hi => h (i + 1) (by omega))
    have hhead := h 0 (by omega)
    simp only [pack, pow_succ]
    nlinarith

theorem pack_mod (q n : ℕ) (hq : 0 < q) {f : ℕ → ℕ}
    (h : f 0 < q) : pack q (n + 1) f % q = f 0 := by
  simp [pack, Nat.mod_eq_of_lt h]

theorem pack_div (q n : ℕ) (hq : 0 < q) {f : ℕ → ℕ}
    (h : f 0 < q) : pack q (n + 1) f / q = pack q n (fun i => f (i + 1)) := by
  simp [pack, Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt h]

theorem pack_digit (q n i : ℕ) (hq : 0 < q) {f : ℕ → ℕ}
    (h : ∀ j < n, f j < q) (hi : i < n) :
    pack q n f / q ^ i % q = f i := by
  induction i generalizing n f with
  | zero =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa using pack_mod q n hq (h 0 (by omega))
  | succ i ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [pow_succ', ← Nat.div_div_eq_div_mul, pack_div q n hq (h 0 (by omega))]
    exact ih n (fun j hj => h (j + 1) (by omega)) (by omega)

theorem pack_eq_sum (q n : ℕ) (f : ℕ → ℕ) :
    pack q n f = ∑ i ∈ Finset.range n, f i * q ^ i := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    rw [pack, ih, Finset.sum_range_succ']
    simp only [pow_zero, Nat.mul_one, Finset.mul_sum, pow_succ]
    rw [Nat.add_comm (f 0)]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem pack_const_one (q n : ℕ) (hq : 1 < q) :
    pack q n (fun _ => 1) = (q ^ n - 1) / (q - 1) := by
  rw [pack_eq_sum]
  simp only [Nat.one_mul]
  exact Nat.geomSum_eq hq n

theorem pack_const (q n c : ℕ) :
    pack q n (fun _ => c) = c * pack q n (fun _ => 1) := by
  simpa using pack_mul q n c (fun _ => 1)

theorem pack_one_identity (q n : ℕ) (hq : 1 ≤ q) :
    (q - 1) * pack q n (fun _ => 1) + 1 = q ^ n := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    simp only [pack, pow_succ]
    have hq' := Nat.sub_add_cancel hq
    nlinarith

def prefixSum (f : ℕ → ℕ) (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, f i

@[simp] theorem prefixSum_one (f : ℕ → ℕ) : prefixSum f 1 = f 0 := by
  simp [prefixSum]

theorem prefixSum_shift (f : ℕ → ℕ) (n : ℕ) :
    prefixSum f (n + 1) = f 0 + prefixSum (fun i => f (i + 1)) n := by
  simp [prefixSum, Finset.sum_range_succ', Nat.add_comm]

theorem pack_prefix_identity (q n : ℕ) (f : ℕ → ℕ) (hq : 1 ≤ q) :
    (q - 1) * pack q n (fun i => prefixSum f (i + 1)) + pack q n f =
      q ^ n * prefixSum f n := by
  induction n generalizing f with
  | zero => simp [pack, prefixSum]
  | succ n ih =>
    have hy : pack q (n + 1) (fun i => prefixSum f (i + 1)) =
        f 0 + q * (f 0 * pack q n (fun _ => 1) +
          pack q n (fun i => prefixSum (fun j => f (j + 1)) (i + 1))) := by
      rw [pack, prefixSum_one, ← pack_const, ← pack_add]
      congr 2
      apply pack_congr
      intro i hi
      exact prefixSum_shift f (i + 1)
    rw [hy, pack, prefixSum_shift, pow_succ]
    have htail := congrArg (fun x => q * x) (ih (fun i => f (i + 1)))
    have hr := congrArg (fun x => q * f 0 * x) (pack_one_identity q n hq)
    have hq' := Nat.sub_add_cancel hq
    nlinarith

theorem prefixSum_mono (f : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) :
    prefixSum f a ≤ prefixSum f b := by
  exact Finset.sum_le_sum_of_subset (Finset.range_mono h)

/-- Multiplication by a repunit packs all cumulative digit sums at once. -/
theorem pack_prefix_mod (q n : ℕ) (f : ℕ → ℕ) (hq : 1 < q)
    (hsum : prefixSum f n < q) :
    (pack q n f * pack q n (fun _ => 1)) % q ^ n =
      pack q n (fun i => prefixSum f (i + 1)) := by
  have hcop : Nat.Coprime (q ^ n) (q - 1) := by
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_self_sub_right (by omega : 1 ≤ q)).mpr (by simp)
  have hx : (q - 1) * (pack q n f * pack q n (fun _ => 1)) + pack q n f =
      q ^ n * pack q n f := by
    have := congrArg (fun x => pack q n f * x) (pack_one_identity q n (by omega))
    nlinarith
  have heq :
      (q - 1) * (pack q n f * pack q n (fun _ => 1)) + pack q n f ≡
      (q - 1) * pack q n (fun i => prefixSum f (i + 1)) + pack q n f [MOD q ^ n] := by
    rw [hx, pack_prefix_identity q n f (by omega)]
    simp [Nat.ModEq]
  have heq' := Nat.ModEq.add_right_cancel (Nat.ModEq.refl (pack q n f)) heq
  have hc := Nat.ModEq.cancel_left_of_coprime hcop heq'
  rw [Nat.ModEq, Nat.mod_eq_of_lt (pack_lt q n (by omega) (fun i hi =>
    (prefixSum_mono f (by omega : i + 1 ≤ n)).trans_lt hsum))] at hc
  exact hc

theorem pack_testBit (w n i j : ℕ) {f : ℕ → ℕ}
    (h : ∀ k < n, f k < 2 ^ w) (hi : i < n) (hj : j < w) :
    (pack (2 ^ w) n f).testBit (w * i + j) = (f i).testBit j := by
  have hd := pack_digit (2 ^ w) n i (by positivity) h hi
  have hb := congrArg (fun x : ℕ => x.testBit j) hd
  rw [Nat.testBit_mod_two_pow, show decide (j < w) = true by simp [hj],
    Bool.true_and] at hb
  simpa only [← pow_mul, Nat.testBit_div_two_pow, Nat.add_comm] using hb

theorem pack_testBit_all (w n k : ℕ) (hw : 0 < w) {f : ℕ → ℕ}
    (h : ∀ i < n, f i < 2 ^ w) :
    (pack (2 ^ w) n f).testBit k =
      if k / w < n then (f (k / w)).testBit (k % w) else false := by
  have hdecomp := Nat.mod_add_div k w
  by_cases hi : k / w < n
  · rw [if_pos hi]
    have hk : k = w * (k / w) + k % w := by omega
    simpa only [← hk] using pack_testBit w n (k / w) (k % w) h hi (Nat.mod_lt k hw)
  · rw [if_neg hi]
    have hkn : w * n ≤ k := by
      have := Nat.mul_le_mul_left w (by omega : n ≤ k / w)
      omega
    apply Nat.testBit_eq_false_of_lt
    apply (pack_lt (2 ^ w) n (by positivity) h).trans_le
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) hkn

theorem pack_and (w n : ℕ) (hw : 0 < w) (f g : ℕ → ℕ)
    (hf : ∀ i < n, f i < 2 ^ w) (hg : ∀ i < n, g i < 2 ^ w) :
    pack (2 ^ w) n f &&& pack (2 ^ w) n g =
      pack (2 ^ w) n (fun i => f i &&& g i) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, pack_testBit_all w n k hw hf, pack_testBit_all w n k hw hg,
    pack_testBit_all w n k hw (fun i hi => Nat.and_le_left.trans_lt (hf i hi))]
  split_ifs <;> simp [Nat.testBit_and]

/-- A low mask discards exactly the bits shifted in from the next digit. -/
theorem pack_shift_and (w n s : ℕ) (hw : 0 < w) (hs : s ≤ w) (f g : ℕ → ℕ)
    (hf : ∀ i < n, f i < 2 ^ w) (hg : ∀ i < n, g i < 2 ^ (w - s)) :
    (pack (2 ^ w) n f >>> s) &&& pack (2 ^ w) n g =
      pack (2 ^ w) n (fun i => (f i >>> s) &&& g i) := by
  have hg' : ∀ i < n, g i < 2 ^ w := fun i hi =>
    (hg i hi).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
  have hout : ∀ i < n, ((f i >>> s) &&& g i) < 2 ^ w := fun i hi =>
    Nat.and_le_right.trans_lt (hg' i hi)
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, pack_testBit_all w n k hw hg', pack_testBit_all w n k hw hout]
  by_cases hi : k / w < n
  · rw [if_pos hi, if_pos hi, Nat.testBit_and]
    by_cases hb : (g (k / w)).testBit (k % w) = true
    · have hsmall : k % w < w - s := by
        by_contra hh
        have hfals := Nat.testBit_eq_false_of_lt ((hg (k / w) hi).trans_le
          (Nat.pow_le_pow_right (by omega) (by omega : w - s ≤ k % w)))
        simp [hb] at hfals
      have hd := Nat.mod_add_div k w
      have heq : s + k = w * (k / w) + (k % w + s) := by omega
      rw [Nat.testBit_shiftRight, heq, pack_testBit w n (k / w) (k % w + s) hf hi
        (by omega), Nat.testBit_shiftRight]
      simp [Nat.add_comm]
    · simp [Bool.eq_false_iff.mpr hb]
  · simp [hi]

theorem pack_pair (q n : ℕ) (f : ℕ → ℕ) :
    pack q (2 * n) f = pack (q * q) n (fun i => f (2 * i) + q * f (2 * i + 1)) := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    simp only [pack]
    rw [ih]
    have heq :
        pack (q * q) n (fun i => f (2 * i + 1 + 1) + q * f (2 * i + 1 + 1 + 1)) =
        pack (q * q) n (fun i => f (2 * (i + 1)) + q * f (2 * (i + 1) + 1)) := by
      apply pack_congr
      intro i hi
      congr 2 <;> omega
    rw [heq]
    ring

theorem pack_digits (w n mask : ℕ) (hw : 0 < w) (hm : mask < 2 ^ (w * n)) :
    pack (2 ^ w) n (fun i => mask / 2 ^ (w * i) % 2 ^ w) = mask := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [pack_testBit_all w n k hw (fun i hi => Nat.mod_lt _ (by positivity))]
  by_cases hi : k / w < n
  · rw [if_pos hi, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    have hj := Nat.mod_lt k hw
    simp only [show decide (k % w < w) = true by simp [hj], Bool.true_and]
    rw [Nat.mod_add_div]
  · rw [if_neg hi]
    symm
    apply Nat.testBit_eq_false_of_lt
    apply hm.trans_le (Nat.pow_le_pow_right (by omega) ?_)
    have hdecomp := Nat.mod_add_div k w
    have := Nat.mul_le_mul_left w (by omega : n ≤ k / w)
    omega

theorem stripe_eq (w n : ℕ) (hw : 0 < w) :
    (2 ^ (2 * w * n) - 1) / (2 ^ w + 1) =
      pack (2 ^ (2 * w)) n (fun _ => 2 ^ w - 1) := by
  have hq : 1 ≤ 2 ^ w := Nat.succ_le_of_lt (Nat.two_pow_pos w)
  have hr := pack_one_identity (2 ^ (2 * w)) n
    (Nat.succ_le_of_lt (Nat.two_pow_pos (2 * w)))
  have hpow : 2 ^ (2 * w) = 2 ^ w * 2 ^ w := by
    rw [two_mul, pow_add]
  have hsub : 2 ^ (2 * w) - 1 = (2 ^ w + 1) * (2 ^ w - 1) := by
    have := Nat.sub_add_cancel hq
    rw [hpow]
    have hs := Nat.sub_add_cancel (show 1 ≤ 2 ^ w * 2 ^ w by nlinarith)
    nlinarith
  have hall : 2 ^ (2 * w * n) - 1 =
      (2 ^ w + 1) * ((2 ^ w - 1) * pack (2 ^ (2 * w)) n (fun _ => 1)) := by
    rw [pow_mul, ← hr, Nat.add_sub_cancel, hsub]
    ring
  rw [hall, Nat.mul_div_cancel_left _ (by positivity)]
  exact (pack_const _ _ _).symm

/-- One parallel pairwise population-count step. -/
def mergeCounts (w n x : ℕ) : ℕ :=
  RosserScan.forceNat ((2 ^ (2 * w * n) - 1) / (2 ^ w + 1)) fun stripe =>
    (x &&& stripe) + ((x >>> w) &&& stripe)

theorem mergeCounts_sound (w n : ℕ) (hw : 0 < w) (f : ℕ → ℕ)
    (hf : ∀ i < 2 * n, f i < 2 ^ w) :
    mergeCounts w n (pack (2 ^ w) (2 * n) f) =
      pack (2 ^ (2 * w)) n (fun i => f (2 * i) + f (2 * i + 1)) := by
  have hq : 0 < 2 ^ w := by positivity
  have hpow : 2 ^ w * 2 ^ w = 2 ^ (2 * w) := by rw [two_mul, pow_add]
  let g := fun i => f (2 * i) + 2 ^ w * f (2 * i + 1)
  have hg : ∀ i < n, g i < 2 ^ (2 * w) := by
    intro i hi
    have h0 := hf (2 * i) (by omega)
    have h1 := hf (2 * i + 1) (by omega)
    dsimp [g]
    rw [← hpow]
    nlinarith
  have hm : ∀ i < n, 2 ^ w - 1 < 2 ^ (2 * w - w) := by
    intro i hi
    rw [show 2 * w - w = w by omega]
    omega
  have hlo : ∀ i < n, (g i &&& (2 ^ w - 1)) = f (2 * i) := by
    intro i hi
    simp only [g, Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hf (2 * i) (by omega))]
  have hhi : ∀ i < n, ((g i >>> w) &&& (2 ^ w - 1)) = f (2 * i + 1) := by
    intro i hi
    simp only [g, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ hq,
      Nat.div_eq_of_lt (hf (2 * i) (by omega)), Nat.zero_add,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hf (2 * i + 1) (by omega))]
  simp only [mergeCounts, forceNat_eq, stripe_eq w n hw, pack_pair, hpow]
  change (pack (2 ^ (2 * w)) n g &&& pack (2 ^ (2 * w)) n (fun _ => 2 ^ w - 1)) +
    ((pack (2 ^ (2 * w)) n g >>> w) &&& pack (2 ^ (2 * w)) n (fun _ => 2 ^ w - 1)) = _
  rw [pack_and (2 * w) n (by omega) g _ hg (fun i hi => (hm i hi).trans_le
    (Nat.pow_le_pow_right (by omega) (by omega))),
    pack_shift_and (2 * w) n w (by omega) (by omega) g _ hg hm, ← pack_add]
  apply pack_congr
  intro i hi
  rw [hlo i hi, hhi i hi]

def bitValue (mask i : ℕ) : ℕ := (mask.testBit i).toNat

theorem bitValue_le_one (mask i : ℕ) : bitValue mask i ≤ 1 := by
  unfold bitValue
  cases mask.testBit i <;> decide

theorem bitValue_eq_digit (mask i : ℕ) : bitValue mask i = mask / 2 ^ i % 2 := by
  simp only [bitValue, Nat.testBit_eq_decide_div_mod_eq]
  have h := Nat.mod_lt (mask / 2 ^ i) (by omega : 0 < 2)
  by_cases heq : mask / 2 ^ i % 2 = 1
  · simp [heq]
  · have hz : mask / 2 ^ i % 2 = 0 := by omega
    simp [hz]

theorem candidateCount_eq_sum (mask d : ℕ) :
    candidateCount mask d = prefixSum (bitValue mask) d := by
  induction d with
  | zero => simp [candidateCount, prefixSum]
  | succ d ih =>
    simp only [candidateCount, List.range_succ, List.filter_append, List.length_append,
      prefixSum, Finset.sum_range_succ] at *
    rw [ih]
    cases h : mask.testBit d <;> simp [List.filter, bitValue, h]

def blockSum (f : ℕ → ℕ) (w j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range w, f (w * j + i)

@[simp] theorem blockSum_one (f : ℕ → ℕ) (j : ℕ) : blockSum f 1 j = f j := by
  simp [blockSum]

theorem blockSum_le (f : ℕ → ℕ) (hf : ∀ i, f i ≤ 1) (w j : ℕ) :
    blockSum f w j ≤ w := by
  calc
    _ ≤ ∑ _i ∈ Finset.range w, 1 := Finset.sum_le_sum (fun i hi => hf _)
    _ = _ := by simp

theorem blockSum_pair (f : ℕ → ℕ) (w j : ℕ) :
    blockSum f (2 * w) j = blockSum f w (2 * j) + blockSum f w (2 * j + 1) := by
  unfold blockSum
  rw [show 2 * w = w + w by omega, Finset.sum_range_add]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> congr 1 <;> ring

theorem prefixSum_blocks (f : ℕ → ℕ) (w n : ℕ) :
    prefixSum (blockSum f w) n = prefixSum f (w * n) := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
    change (∑ i ∈ Finset.range (n + 1), blockSum f w i) = _
    rw [Finset.sum_range_succ]
    change prefixSum (blockSum f w) n + blockSum f w n = _
    rw [ih, Nat.mul_add, Nat.mul_one]
    simp only [prefixSum, blockSum, Finset.sum_range_add]

theorem mergeCounts_blocks (w n : ℕ) (hw : 0 < w) (f : ℕ → ℕ)
    (hf : ∀ i, f i ≤ 1) :
    mergeCounts w n (pack (2 ^ w) (2 * n) (blockSum f w)) =
      pack (2 ^ (2 * w)) n (blockSum f (2 * w)) := by
  rw [mergeCounts_sound w n hw _ (fun i hi =>
    (blockSum_le f hf w i).trans_lt Nat.lt_two_pow_self)]
  apply pack_congr
  intro i hi
  exact (blockSum_pair f w i).symm

/-- Five pairwise merge stages give one population count per 32-bit digit. -/
def packedCounts32 (mask n : ℕ) : ℕ :=
  RosserScan.forceNat (mergeCounts 1 (16 * n) mask) fun x =>
  RosserScan.forceNat (mergeCounts 2 (8 * n) x) fun x =>
  RosserScan.forceNat (mergeCounts 4 (4 * n) x) fun x =>
  RosserScan.forceNat (mergeCounts 8 (2 * n) x) fun x =>
    mergeCounts 16 n x

theorem packedCounts32_sound (mask n : ℕ) (hm : mask < 2 ^ (32 * n)) :
    packedCounts32 mask n = pack (2 ^ 32) n (blockSum (bitValue mask) 32) := by
  have hzero : pack 2 (32 * n) (blockSum (bitValue mask) 1) = mask := by
    calc
      _ = pack 2 (32 * n) (fun i => mask / 2 ^ i % 2) := by
        apply pack_congr
        intro i hi
        rw [blockSum_one, bitValue_eq_digit]
      _ = mask := by
        simpa only [Nat.one_mul, pow_one] using
          pack_digits 1 (32 * n) mask (by omega) (by simpa using hm)
  have h1 := mergeCounts_blocks 1 (16 * n) (by omega) (bitValue mask) (bitValue_le_one mask)
  have h2 := mergeCounts_blocks 2 (8 * n) (by omega) (bitValue mask) (bitValue_le_one mask)
  have h4 := mergeCounts_blocks 4 (4 * n) (by omega) (bitValue mask) (bitValue_le_one mask)
  have h8 := mergeCounts_blocks 8 (2 * n) (by omega) (bitValue mask) (bitValue_le_one mask)
  have h16 := mergeCounts_blocks 16 n (by omega) (bitValue mask) (bitValue_le_one mask)
  norm_num only [← Nat.mul_assoc, Nat.reduceMul] at h1 h2 h4 h8 h16
  rw [hzero] at h1
  simp only [packedCounts32, forceNat_eq, h1, h2, h4, h8, h16]
  norm_num

/-- With half-width guards, subtraction is digitwise and every comparison is checked. -/
theorem guard_sound32 (n : ℕ) (f g : ℕ → ℕ)
    (hf : ∀ i < n, f i < 2 ^ 31) (hg : ∀ i < n, g i < 2 ^ 31)
    (hcheck :
      ((pack (2 ^ 32) n g + pack (2 ^ 32) n (fun _ => 2 ^ 31) -
        pack (2 ^ 32) n f) &&& pack (2 ^ 32) n (fun _ => 2 ^ 31)) =
          pack (2 ^ 32) n (fun _ => 2 ^ 31)) :
    ∀ i < n, f i ≤ g i := by
  have hsub :
      pack (2 ^ 32) n g + pack (2 ^ 32) n (fun _ => 2 ^ 31) - pack (2 ^ 32) n f =
        pack (2 ^ 32) n (fun i => g i + 2 ^ 31 - f i) := by
    rw [← pack_add, pack_sub]
    intro i hi
    have := hf i hi
    omega
  rw [hsub] at hcheck
  have hout : ∀ i < n, g i + 2 ^ 31 - f i < 2 ^ 32 := by
    intro i hi
    have := hg i hi
    omega
  intro i hi
  have hb := congrArg (fun x : ℕ => x.testBit (32 * i + 31)) hcheck
  rw [Nat.testBit_and, pack_testBit 32 n i 31 hout hi (by omega),
    pack_testBit 32 n i 31 (by intro j hj; norm_num) hi (by omega)] at hb
  have hguard : (2 ^ 31 : ℕ).testBit 31 = true := by decide
  simp only [hguard, Bool.and_true] at hb
  simp only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq] at hb
  have := hout i hi
  omega

theorem pack_index_identity (q n : ℕ) (hq : 1 ≤ q) (hn : 0 < n) :
    (q - 1) * pack q n (fun i => i) + pack q n (fun _ => 1) =
      (n - 1) * q ^ n + 1 := by
  have hprefix := pack_prefix_identity q n (fun _ => 1) hq
  have heq : pack q n (fun i => prefixSum (fun _ => 1) (i + 1)) =
      pack q n (fun i => i) + pack q n (fun _ => 1) := by
    rw [← pack_add]
    apply pack_congr
    intro i hi
    simp [prefixSum]
  rw [heq] at hprefix
  simp [prefixSum] at hprefix
  have hr := pack_one_identity q n hq
  have hn' := Nat.sub_add_cancel (by omega : 1 ≤ n)
  have hn'' := congrArg (fun x => x * q ^ n) hn'
  nlinarith

theorem pack_index_eq (q n : ℕ) (hq : 1 < q) (hn : 0 < n) :
    pack q n (fun i => i) =
      ((n - 1) * q ^ n + 1 - pack q n (fun _ => 1)) / (q - 1) := by
  have h := pack_index_identity q n (by omega) hn
  have heq : (n - 1) * q ^ n + 1 - pack q n (fun _ => 1) =
      (q - 1) * pack q n (fun i => i) := by omega
  rw [heq, Nat.mul_div_cancel_left _ (by omega)]

def checkFromCounts (counts n intercept slope : ℕ) : Bool :=
  RosserScan.forceNat (32 * n) fun L =>
  RosserScan.forceNat ((2 ^ L - 1) / (2 ^ 32 - 1)) fun R =>
  RosserScan.forceNat ((((counts <<< L) - counts) / (2 ^ 32 - 1)) % 2 ^ L) fun pref =>
  RosserScan.forceNat (32 * (((n - 1) * 2 ^ L + 1 - R) / (2 ^ 32 - 1))) fun pos =>
  RosserScan.forceNat (16384 * pref) fun lhs =>
  RosserScan.forceNat (intercept * R + slope * pos) fun rhs =>
  RosserScan.forceNat (2 ^ 31 * R) fun guard =>
    decide (((rhs + guard - lhs) &&& guard) = guard)

theorem packed_prefix_formula (n : ℕ) (f : ℕ → ℕ)
    (hsum : prefixSum f n < 2 ^ 32) :
    ((((pack (2 ^ 32) n f <<< (32 * n)) - pack (2 ^ 32) n f) /
      (2 ^ 32 - 1)) % 2 ^ (32 * n)) =
      pack (2 ^ 32) n (fun i => prefixSum f (i + 1)) := by
  have hr := pack_one_identity (2 ^ 32) n (by norm_num)
  have hp : 2 ^ (32 * n) - 1 =
      (2 ^ 32 - 1) * pack (2 ^ 32) n (fun _ => 1) := by
    rw [pow_mul]
    omega
  rw [Nat.shiftLeft_eq]
  have hnum : pack (2 ^ 32) n f * 2 ^ (32 * n) - pack (2 ^ 32) n f =
      (pack (2 ^ 32) n f * pack (2 ^ 32) n (fun _ => 1)) * (2 ^ 32 - 1) := by
    calc
      _ = pack (2 ^ 32) n f * (2 ^ (32 * n) - 1) := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      _ = _ := by rw [hp]; ring
  rw [hnum, Nat.mul_div_cancel _ (by norm_num), pow_mul]
  exact pack_prefix_mod (2 ^ 32) n f (by norm_num) hsum

/-- The prefix/guard stage, with a semantic specification for its packed count input. -/
theorem checkFromCounts_sound (n intercept slope : ℕ) (f : ℕ → ℕ)
    (hn : 0 < n) (hcount : 16384 * prefixSum f n < 2 ^ 31)
    (hrhs : intercept + slope * (32 * (n - 1)) < 2 ^ 31)
    (hcheck : checkFromCounts (pack (2 ^ 32) n f) n intercept slope = true) :
    ∀ i < n, 16384 * prefixSum f (i + 1) ≤ intercept + slope * (32 * i) := by
  have hsum : prefixSum f n < 2 ^ 32 := by omega
  have hR : (2 ^ (32 * n) - 1) / (2 ^ 32 - 1) =
      pack (2 ^ 32) n (fun _ => 1) := by
    rw [pack_const_one _ _ (by norm_num), pow_mul]
  have hpos : ((n - 1) * 2 ^ (32 * n) + 1 - pack (2 ^ 32) n (fun _ => 1)) /
      (2 ^ 32 - 1) = pack (2 ^ 32) n (fun i => i) := by
    rw [pack_index_eq _ _ (by norm_num) hn, pow_mul]
  simp only [checkFromCounts, forceNat_eq, decide_eq_true_eq] at hcheck
  rw [hR, packed_prefix_formula n f hsum, hpos] at hcheck
  have hguard := guard_sound32 n
    (fun i => 16384 * prefixSum f (i + 1))
    (fun i => intercept + slope * (32 * i))
  apply hguard
  · intro i hi
    exact (Nat.mul_le_mul_left _ (prefixSum_mono f (by omega))).trans_lt hcount
  · intro i hi
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left slope
      (Nat.mul_le_mul_left 32 (by omega : i ≤ n - 1))) intercept).trans_lt hrhs
  · simp only [pack_add, pack_mul, pack_const (2 ^ 32) n intercept,
      pack_const (2 ^ 32) n (2 ^ 31)]
    rw [show pack (2 ^ 32) n (HMul.hMul 32) =
      32 * pack (2 ^ 32) n (fun i => i) from pack_mul (2 ^ 32) n 32 (fun i => i)]
    exact hcheck

theorem candidateCount_mono (mask : ℕ) {a b : ℕ} (h : a ≤ b) :
    candidateCount mask a ≤ candidateCount mask b := by
  rw [candidateCount_eq_sum, candidateCount_eq_sum]
  exact prefixSum_mono _ h

theorem bitValue_eq_zero (mask len i : ℕ) (hm : mask < 2 ^ len) (hi : len ≤ i) :
    bitValue mask i = 0 := by
  have hb := Nat.testBit_eq_false_of_lt
    (hm.trans_le (Nat.pow_le_pow_right (by omega) hi))
  simp [bitValue, hb]

theorem candidateCount_pad (mask len top : ℕ) (hm : mask < 2 ^ len) (hl : len ≤ top) :
    candidateCount mask top = candidateCount mask len := by
  rw [candidateCount_eq_sum, candidateCount_eq_sum]
  have ht : top = len + (top - len) := by omega
  rw [ht]
  simp only [prefixSum, Finset.sum_range_add]
  have hz : ∑ i ∈ Finset.range (top - len), bitValue mask (len + i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact bitValue_eq_zero mask len (len + i) hm (by omega)
  rw [hz, Nat.add_zero]

def packedCheck (mask len intercept slope : ℕ) : Bool :=
  RosserScan.forceNat ((len + 31) / 32) fun n =>
  RosserScan.forceNat (packedCounts32 mask n) fun counts =>
    checkFromCounts counts n intercept slope

/-- A successful packed test bounds every candidate prefix, including a partial final bucket. -/
theorem packedCheck_sound (mask len intercept slope : ℕ)
    (hlen : 0 < len) (hm : mask < 2 ^ len)
    (hcount : 16384 * candidateCount mask len < 2 ^ 31)
    (hrhs : intercept + slope * (32 * ((len + 31) / 32 - 1)) < 2 ^ 31)
    (hcheck : packedCheck mask len intercept slope = true) :
    ∀ d ≤ len, 16384 * candidateCount mask d ≤
      intercept + slope * 32 * ((d - 1) / 32) := by
  let n := (len + 31) / 32
  have hn : 0 < n := by dsimp [n]; omega
  have hl : len ≤ 32 * n := by dsimp [n]; omega
  have hm32 : mask < 2 ^ (32 * n) :=
    hm.trans_le (Nat.pow_le_pow_right (by omega) hl)
  have hsum : prefixSum (blockSum (bitValue mask) 32) n = candidateCount mask len := by
    rw [prefixSum_blocks, ← candidateCount_eq_sum, candidateCount_pad mask len _ hm hl]
  have hc : checkFromCounts (pack (2 ^ 32) n (blockSum (bitValue mask) 32))
      n intercept slope = true := by
    simp only [packedCheck, forceNat_eq] at hcheck
    change checkFromCounts (packedCounts32 mask n) n intercept slope = true at hcheck
    rw [packedCounts32_sound mask n hm32] at hcheck
    exact hcheck
  have hbound := checkFromCounts_sound n intercept slope (blockSum (bitValue mask) 32)
    hn (by simpa only [hsum] using hcount) hrhs hc
  intro d hd
  by_cases hz : d = 0
  · subst d
    simp [candidateCount]
  · have hi : (d - 1) / 32 < n := by dsimp [n]; omega
    have hend : d ≤ 32 * ((d - 1) / 32 + 1) := by omega
    have hb := hbound ((d - 1) / 32) hi
    rw [prefixSum_blocks, ← candidateCount_eq_sum] at hb
    exact (Nat.mul_le_mul_left 16384 (candidateCount_mono mask hend)).trans
      (by simpa only [Nat.mul_assoc] using hb)

end RosserPackedBarrier

-- Source: Solutions/RosserBitMoments.lean
/-! Compute the three moments of a bit window by bytes. A single packed
256-entry lookup table replaces eight recursive bit inspections. Its entire
contents are certified by `decide +kernel`; no native computation is trusted. -/

namespace RosserBitMoments

open RosserBitSieve AlternativeProductMoments

theorem moments_append (xs ys : List ℕ) :
    moments (xs ++ ys) = merge (moments xs) (moments ys) := by
  simp [moments, merge, List.map_append, List.sum_append]

theorem moments_shift (ds : List ℕ) (offset : ℕ) :
    moments (ds.map (fun d => offset + d)) = translate offset (moments ds) := by
  induction ds with
  | nil => simp [moments, translate]
  | cons d ds ih =>
    have hi := congrArg Moments.first ih
    have hj := congrArg Moments.second ih
    simp only [moments, translate] at hi hj
    apply Moments.ext
    · simp [moments, translate]
    · simp only [moments, translate, List.map_cons, List.sum_cons, List.length_cons]
      rw [hi]
      ring
    · simp only [moments, translate, List.map_cons, List.sum_cons, List.length_cons]
      rw [hj]
      ring

theorem moments_perm {xs ys : List ℕ} (h : xs.Perm ys) : moments xs = moments ys := by
  apply Moments.ext
  · exact h.length_eq
  · exact h.sum_eq
  · exact (h.map (fun (d : ℕ) => d ^ 2)).sum_eq

theorem enumBits_shift (depth start mask : ℕ) :
    enumBits depth start mask = (enumBits depth 0 mask).map (fun d => start + d) := by
  induction depth generalizing start mask with
  | zero => simp only [enumBits]; split <;> simp
  | succ depth ih =>
    simp only [enumBits]
    split
    · simp
    · rw [ih start, ih (start + 2 ^ depth), ih (0 + 2 ^ depth), List.map_append,
        List.map_map]
      simp only [Nat.zero_add, Function.comp_def, Nat.add_assoc]

theorem enumBits_mod_perm (depth start mask : ℕ) :
    (enumBits depth start (mask % 2 ^ (2 ^ depth))).Perm (enumBits depth start mask) := by
  apply (List.perm_ext_iff_of_nodup (enumBits_nodup _ _ _) (enumBits_nodup _ _ _)).mpr
  intro x
  simp only [mem_enumBits, Nat.testBit_mod_two_pow, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hlo, hhi, _, hb⟩
    exact ⟨hlo, hhi, hb⟩
  · rintro ⟨hlo, hhi, hb⟩
    exact ⟨hlo, hhi, by omega, hb⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem byteMoments_table : ∀ byte : Fin 256,
    byteMoments byte = moments (enumBits 3 0 byte) := by decide +kernel

theorem byteMoments_sound (mask : ℕ) :
    byteMoments (mask % 256) = moments (enumBits 3 0 mask) := by
  have h := byteMoments_table ⟨mask % 256, Nat.mod_lt _ (by decide)⟩
  have hm := moments_perm (enumBits_mod_perm 3 0 mask)
  norm_num only [Nat.reducePow] at hm
  exact h.trans hm

theorem fastMoments_sound (depth start mask : ℕ) :
    fastMoments depth start mask = moments (enumBits (depth + 3) start mask) := by
  induction depth generalizing start mask with
  | zero =>
    rw [fastMoments, byteMoments_sound, enumBits_shift 3 start mask, moments_shift]
  | succ depth ih =>
    change (if mask == 0 then _ else _) =
      moments (enumBits ((depth + 3) + 1) start mask)
    rw [enumBits]
    split
    · rfl
    · dsimp only
      rw [moments_append, ih, ih]

theorem windowMoments_sound (mask shift len : ℕ) :
    windowMoments mask shift len = moments (windowOffsets 13 mask shift len) := by
  rw [windowMoments, fastMoments_sound]
  change moments (enumBits 13 1 _) = _
  rw [enumBits_shift]
  simp only [windowOffsets, Nat.add_comm]

theorem stepFromMoments_eq (v a : ℕ) (ds : List ℕ) :
    stepFromMoments v a (moments ds) = momentStep v a ds := by
  rfl

theorem fastMomentStep_eq (v a mask shift len : ℕ) :
    fastMomentStep v a mask shift len =
      momentStep v a (windowOffsets 13 mask shift len) := by
  rw [fastMomentStep, windowMoments_sound, stepFromMoments_eq]

end RosserBitMoments

-- Source: Solutions/RosserScan.lean
/-!
Generic verifier for an interval. A shared bit mask covers all primes in the
interval; short blocks reuse windows of this mask. Successful execution is
proved to imply both the real inequality and the next reciprocal bound.
-/

namespace RosserScan

open RosserBitSieve AlternativeProductMoments RosserMomentBridge
open RosserLogCertificate RosserBlockCheck
open RosserBitMoments

theorem forceNat_eq {α : Type} (n : ℕ) (f : ℕ → α) : forceNat n f = f n := by
  cases n <;> rfl

def Covers (base top mask : ℕ) : Prop :=
  ∀ p, Nat.Prime p → base < p → p ≤ top → mask.testBit (p - (base + 1)) = true

theorem sieve_covers (divisors : List ℕ) (base top : ℕ)
    (hds : ∀ d ∈ divisors, 2 ≤ d ∧ d < base + 1) :
    Covers base top (candidateMask divisors (base + 1) (top - base)) := by
  intro p hp hlo hhi
  apply candidateMask_preserves_prime _ _ _ _ hds (by omega)
  simpa only [Nat.add_sub_of_le (show base + 1 ≤ p by omega)] using hp

def StepGood (a b w : ℕ) : Prop :=
  a < b ∧ (w : ℝ) / scale ≤ reciprocalProduct b ∧
    ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ b → Bound x

theorem step_sound (base top mask a b v : ℕ)
    (hcover : Covers base top mask) (hbase : base ≤ a) (hbt : b ≤ top)
    (hv : (v : ℝ) / scale ≤ reciprocalProduct a)
    (hc : stepCheck a b v (stepOffsets base mask a b) = true) :
    StepGood a b (momentStep v a (stepOffsets base mask a b)) := by
  simp only [stepCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨ha, hab, hlen, hfirst, hupper⟩, hcheck⟩ := hc
  have hbounds : ∀ d ∈ stepOffsets base mask a b, 0 < d ∧ d ≤ b - a := by
    intro d hd
    have h := (mem_windowOffsets _ _ _ _ _).mp hd
    exact ⟨h.1, h.2.1⟩
  have hprimes : ∀ p, Nat.Prime p → a < p → p ≤ b →
      p - a ∈ stepOffsets base mask a b := by
    intro p hp hlo hhi
    apply (mem_windowOffsets _ _ _ _ _).mpr
    refine ⟨by omega, by omega, by omega, ?_⟩
    have he : p - a - 1 + (a - base) = p - (base + 1) := by omega
    rw [he]
    exact hcover p hp (by omega) (by omega)
  have hnext := momentStep_reciprocalProduct scale v a b _ scale_pos hab.le ha
    (windowOffsets_nodup _ _ _ _) hbounds hprimes hfirst hupper hv
  exact ⟨hab, hnext, fun x hax hxb => check_sound a b _ (by omega) hcheck hnext x hax hxb⟩

theorem stepData_eq (base mask a b v : ℕ) :
    stepData base mask a b v =
      (stepCheck a b v (stepOffsets base mask a b),
        momentStep v a (stepOffsets base mask a b)) := by
  unfold stepData
  rw [windowMoments_sound]
  rfl

theorem attempt_sound (base top mask a v fuel width b w : ℕ)
    (hcover : Covers base top mask) (hbase : base ≤ a)
    (hv : (v : ℝ) / scale ≤ reciprocalProduct a)
    (h : attempt base top mask a v fuel width = some (b, w)) :
    b ≤ top ∧ StepGood a b w := by
  induction fuel generalizing width with
  | zero => simp [attempt] at h
  | succ fuel ih =>
    simp only [attempt, stepData_eq] at h
    split at h
    · rename_i hc
      have he := Option.some.inj h
      have hb := congrArg Prod.fst he
      have hw := congrArg Prod.snd he
      dsimp only at hb hw
      subst b w
      exact ⟨min_le_left _ _, step_sound _ _ _ _ _ _ hcover hbase
        (min_le_left _ _) hv hc⟩
    · exact ih (width / 2) h

theorem run_sound (base top mask fuel a v w : ℕ)
    (hcover : Covers base top mask) (hbase : base ≤ a)
    (hv : (v : ℝ) / scale ≤ reciprocalProduct a)
    (h : run base top mask fuel a v = some w) :
    (w : ℝ) / scale ≤ reciprocalProduct top ∧
      ∀ x : ℝ, (a : ℝ) < x → x ≤ top → Bound x := by
  induction fuel generalizing a v with
  | zero =>
    simp only [run, forceNat_eq] at h
    split at h
    · rename_i ha
      have ha' : a = top := by simpa using ha
      have hv' : v = w := Option.some.inj h
      subst a w
      exact ⟨hv, by intro x hx hxt; linarith⟩
    · contradiction
  | succ fuel ih =>
    simp only [run, forceNat_eq] at h
    split at h
    · rename_i ha
      have ha' : a = top := by simpa using ha
      have hv' : v = w := Option.some.inj h
      subst a w
      exact ⟨hv, by intro x hx hxt; linarith⟩
    · split at h
      · contradiction
      · rename_i b w' htry
        have hs := attempt_sound base top mask a v 20 _ b w'
          hcover hbase hv htry
        have hab := hs.2.1
        have hi := ih b w' (by omega) hs.2.2.1 h
        refine ⟨hi.1, ?_⟩
        intro x hax hxt
        by_cases hxb : x ≤ b
        · exact hs.2.2.2 x hax.le hxb
        · exact hi.2 x (lt_of_not_ge hxb) hxt

end RosserScan

-- Source: Solutions/RosserPrefixBridge.lean
/-! Connect prime coverage of a block to the fast packed prefix counter. -/

namespace RosserPrefixBridge

open RosserPackedBarrier

theorem prime_card_le_candidateCount (a b n mask : ℕ)
    (han : a ≤ n) (hnb : n ≤ b)
    (hcover : ∀ p, Nat.Prime p → a < p → p ≤ b →
      mask.testBit (p - (a + 1)) = true) :
    (Nat.primesLE n \ Nat.primesLE a).card ≤
      candidateCount mask (n - a) := by
  let t := Nat.primesLE n \ Nat.primesLE a
  let s := (List.range (n - a)).filter (fun i => mask.testBit i)
  have hmap : Set.MapsTo (fun p : ℕ => p - (a + 1))
      (t : Set ℕ) (s.toFinset : Set ℕ) := by
    intro p hp
    obtain ⟨hpn, hpa⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpn', hpprime⟩ := Nat.mem_primesLE.mp hpn
    have hap : a < p := by
      by_contra h
      exact hpa (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
    apply List.mem_toFinset.mpr
    apply List.mem_filter.mpr
    constructor
    · apply List.mem_range.mpr
      change p - (a + 1) < n - a
      omega
    · exact hcover p hpprime hap (by omega)
  have hinj : (t : Set ℕ).InjOn
      (fun p : ℕ => p - (a + 1)) := by
    intro p hp q hq heq
    have hp' := Finset.mem_sdiff.mp hp
    have hq' := Finset.mem_sdiff.mp hq
    have hpprime := (Nat.mem_primesLE.mp hp'.1).2
    have hqprime := (Nat.mem_primesLE.mp hq'.1).2
    have hap : a < p := by
      by_contra h
      exact hp'.2 (Nat.mem_primesLE.mpr ⟨by omega, hpprime⟩)
    have haq : a < q := by
      by_contra h
      exact hq'.2 (Nat.mem_primesLE.mpr ⟨by omega, hqprime⟩)
    change p - (a + 1) = q - (a + 1) at heq
    omega
  have hc := Finset.card_le_card_of_injOn (fun p : ℕ => p - (a + 1)) hmap hinj
  have hs : s.toFinset.card ≤ s.length := List.toFinset_card_le s
  have hfinal := hc.trans hs
  simpa only [t, s, candidateCount] using hfinal

theorem packed_affine_count (a : ℕ) (x : ℝ) (mask len intercept slope : ℕ)
    (hlen : 0 < len) (hm : mask < 2 ^ len) (hI : 0 < intercept)
    (hcount : 16384 * candidateCount mask len < 2 ^ 31)
    (hrhs : (intercept - 1) + slope *
      (32 * ((len + 31) / 32 - 1)) < 2 ^ 31)
    (hcheck : packedCheck mask len (intercept - 1) slope = true)
    (hax : (a : ℝ) ≤ x)
    (hfloor : ⌊x⌋₊ ≤ a + len) :
    (candidateCount mask (⌊x⌋₊ - a) : ℝ) <
      (intercept : ℝ) / 16384 +
      (slope : ℝ) / 16384 * (x - a) := by
  have han : a ≤ ⌊x⌋₊ := Nat.le_floor hax
  have hlen' : ⌊x⌋₊ - a ≤ len := by omega
  have hb := packedCheck_sound mask len (intercept - 1) slope
    hlen hm hcount hrhs hcheck (⌊x⌋₊ - a) hlen'
  let pos := 32 * ((⌊x⌋₊ - a - 1) / 32)
  have hpos : pos ≤ ⌊x⌋₊ - a := by dsimp [pos]; omega
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith only [hax])
  have hposreal : (pos : ℝ) ≤ x - a := by
    have hsub : ((⌊x⌋₊ - a : ℕ) : ℝ) = (⌊x⌋₊ : ℝ) - a :=
      Nat.cast_sub han
    have hposcast : (pos : ℝ) ≤ (⌊x⌋₊ - a : ℕ) := by exact_mod_cast hpos
    exact hposcast.trans (by rw [hsub]; linarith only [hfl])
  have hraw : 16384 * candidateCount mask (⌊x⌋₊ - a) <
      intercept + slope * pos := by
    have hb' : 16384 * candidateCount mask (⌊x⌋₊ - a) ≤
        (intercept - 1) + slope * pos := by
      simpa only [pos, Nat.mul_assoc] using hb
    omega
  have hraw' : (16384 : ℝ) * candidateCount mask (⌊x⌋₊ - a) <
      (intercept : ℝ) + slope * pos := by exact_mod_cast hraw
  have hsl : (slope : ℝ) * pos ≤ slope * (x - a) :=
    mul_le_mul_of_nonneg_left hposreal (by positivity)
  have htarget : (16384 : ℝ) * candidateCount mask (⌊x⌋₊ - a) <
      (intercept : ℝ) + slope * (x - a) := by
    linarith only [hraw', hsl]
  have heq : (intercept : ℝ) / 16384 +
      (slope : ℝ) / 16384 * (x - a) =
      ((intercept : ℝ) + slope * (x - a)) / 16384 := by ring
  rw [heq]
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 16384)).mpr
  simpa only [mul_comm] using htarget

theorem block_sound (a b v mask : ℕ)
    (hvalid : (RosserPrefixParams.parameters a b v).valid = true)
    (hm : mask < 2 ^ (b - a))
    (hI : 0 < (RosserPrefixParams.parameters a b v).intercept)
    (hcount : 16384 * candidateCount mask (b - a) < 2 ^ 31)
    (hrhs :
      ((RosserPrefixParams.parameters a b v).intercept - 1) +
        (RosserPrefixParams.parameters a b v).slope *
          (32 * (((b - a) + 31) / 32 - 1)) < 2 ^ 31)
    (hcheck : packedCheck mask (b - a)
      ((RosserPrefixParams.parameters a b v).intercept - 1)
      (RosserPrefixParams.parameters a b v).slope = true)
    (hcover : ∀ p, Nat.Prime p → a < p → p ≤ b →
      mask.testBit (p - (a + 1)) = true)
    (hv : ((v : ℝ) / RosserLogCertificate.scale) ≤
      RosserMomentBridge.reciprocalProduct a)
    (x : ℝ) (hax : (a : ℝ) ≤ x) (hxb : x ≤ b) :
    RosserBlockCheck.Bound x := by
  have hab := (RosserPrefixParams.parameters_valid a b v hvalid).2.1
  have hlen : 0 < b - a := by omega
  have hfloor : ⌊x⌋₊ ≤ b := Nat.floor_le_of_le hxb
  have hfloor' : ⌊x⌋₊ ≤ a + (b - a) := by omega
  have hcard := prime_card_le_candidateCount a b ⌊x⌋₊ mask
    (Nat.le_floor hax) hfloor hcover
  have hprefix := packed_affine_count a x mask (b - a)
    (RosserPrefixParams.parameters a b v).intercept
    (RosserPrefixParams.parameters a b v).slope
    hlen hm hI hcount hrhs hcheck hax hfloor'
  exact RosserPrefixParams.parameterized_bound a b v
    (candidateCount mask (⌊x⌋₊ - a)) x hvalid hax hxb hv hcard hprefix

theorem window_mask_covers (base top mask a b : ℕ)
    (hcover : RosserScan.Covers base top mask)
    (hbase : base ≤ a) (hbt : b ≤ top) :
    ∀ p, Nat.Prime p → a < p → p ≤ b →
      ((mask / 2 ^ (a - base)) % 2 ^ (b - a)).testBit
        (p - (a + 1)) = true := by
  intro p hp hap hpb
  have hi : p - (a + 1) < b - a := by omega
  have heq : p - (a + 1) + (a - base) = p - (base + 1) := by omega
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp only [show decide (p - (a + 1) < b - a) = true by simp [hi],
    Bool.true_and, heq]
  exact hcover p hp (by omega) (by omega)

end RosserPrefixBridge

-- Source: Solutions/RosserSieveData.lean
/-! Sieve divisors are untrusted numerical hints. Their only required property
is the elementary range check below; their primality is not assumed. -/
namespace RosserSieveData
open RosserBitSieve RosserScan RosserMomentBridge RosserLogCertificate

theorem divisors_ge_two : ∀ d ∈ divisors, 2 ≤ d := by decide +kernel

theorem smallDivisors_bounds (base : ℕ) :
    ∀ d ∈ smallDivisors base, 2 ≤ d ∧ d < base + 1 := by
  intro d hd
  obtain ⟨hd, hle⟩ := List.mem_filter.mp hd
  exact ⟨divisors_ge_two d hd, by have := of_decide_eq_true hle; omega⟩

theorem segment_sound (base top v w : ℕ)
    (hv : (v : ℝ) / scale ≤ reciprocalProduct base)
    (h : segment base top v = some w) :
    (w : ℝ) / scale ≤ reciprocalProduct top ∧
      ∀ x : ℝ, (base : ℝ) < x → x ≤ top → RosserBlockCheck.Bound x := by
  simp only [segment, forceNat_eq] at h
  exact run_sound base top (mask base top) 4096 base v w
    (sieve_covers _ _ _ (smallDivisors_bounds base)) (le_refl _) hv h

end RosserSieveData

-- Source: Solutions/RosserCachedSieve.lean
/-! A reusable table of periodic divisor masks for the fixed-size segments. -/

namespace RosserCachedSieve

open RosserBitSieve RosserScan

def withMasks {α : Type} (len : ℕ) : List ℕ → (List (ℕ × ℕ) → α) → α
  | [], f => f []
  | d :: ds, f =>
    forceNat (periodicMask d ((len + d - 1) / d)) fun m =>
      withMasks len ds fun rest => f ((d, m) :: rest)

def pairs (len : ℕ) (ds : List ℕ) : List (ℕ × ℕ) :=
  ds.map (fun d => (d, periodicMask d ((len + d - 1) / d)))

theorem withMasks_eq {α : Type} (len : ℕ) (ds : List ℕ)
    (f : List (ℕ × ℕ) → α) : withMasks len ds f = f (pairs len ds) := by
  induction ds generalizing f with
  | nil => rfl
  | cons d ds ih =>
    simp only [withMasks, RosserScan.forceNat_eq, ih, pairs, List.map_cons]

def mask (ds : List (ℕ × ℕ)) (base top : ℕ) : ℕ :=
  let len := top - base
  let composite := ds.foldl (fun acc dm =>
    if dm.1 ≤ base then
      acc ||| (dm.2 * 2 ^ ((dm.1 - (base + 1) % dm.1) % dm.1))
    else acc) 0
  (2 ^ len - 1) ^^^ (composite % 2 ^ len)

theorem mask_lt (ds : List (ℕ × ℕ)) (base top : ℕ) :
    mask ds base top < 2 ^ (top - base) := by
  unfold mask
  apply Nat.xor_lt_two_pow
  · exact Nat.sub_lt (by positivity) (by norm_num)
  · exact Nat.mod_lt _ (by positivity)

theorem pairs_fold_eq (fixedLen base : ℕ) (ds : List ℕ) (acc : ℕ) :
    (pairs fixedLen ds).foldl (fun acc dm =>
      if dm.1 ≤ base then
        acc ||| (dm.2 * 2 ^ ((dm.1 - (base + 1) % dm.1) % dm.1))
      else acc) acc =
    (ds.filter (fun d => decide (d ≤ base))).foldl (fun acc d =>
      acc ||| divisorMask (base + 1) fixedLen d) acc := by
  induction ds generalizing acc with
  | nil => rfl
  | cons d ds ih =>
    simp only [pairs, List.map_cons, List.foldl_cons, List.filter_cons]
    by_cases hd : d ≤ base
    · simp only [hd, decide_true, if_true]
      change (pairs fixedLen ds).foldl _
        (acc ||| divisorMask (base + 1) fixedLen d) = _
      exact ih _
    · simp only [hd, decide_false, Bool.false_eq_true, if_false]
      exact ih _

theorem mask_prime (fixedLen base top : ℕ) (ds : List ℕ)
    (hds : ∀ d ∈ ds, 2 ≤ d) (hbase : base < top)
    (hlen : top - base ≤ fixedLen) :
    ∀ p, Nat.Prime p → base < p → p ≤ top →
      (mask (pairs fixedLen ds) base top).testBit (p - (base + 1)) = true := by
  intro p hp hbp hpt
  let small := ds.filter (fun d => decide (d ≤ base))
  have hsmall : ∀ d ∈ small, 2 ≤ d ∧ d < base + 1 := by
    intro d hd
    obtain ⟨hdmem, hdle⟩ := List.mem_filter.mp hd
    exact ⟨hds d hdmem, by have := of_decide_eq_true hdle; omega⟩
  have hi : p - (base + 1) < top - base := by omega
  have hprim : Nat.Prime ((base + 1) + (p - (base + 1))) := by
    simpa only [Nat.add_sub_of_le (by omega : base + 1 ≤ p)] using hp
  have hcomp := compositeMask_preserves_prime small (base + 1) fixedLen
    (p - (base + 1)) hsmall hprim
  unfold mask
  rw [pairs_fold_eq]
  change ((2 ^ (top - base) - 1) ^^^
    (compositeMask small (base + 1) fixedLen % 2 ^ (top - base))).testBit
      (p - (base + 1)) = true
  simp [Nat.testBit_xor, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, hi, hcomp]

end RosserCachedSieve

-- Source: Solutions/RosserFastStep.lean
/-! Generic soundness of a fast finite block once its moments and bit mask
have been certified. -/

namespace RosserFastStep

open RosserBitSieve RosserBitMoments RosserMomentBridge
open RosserPrefixBridge RosserPackedBarrier RosserLogCertificate
open AlternativeProductMoments

theorem step_sound (a b v mask depth : ℕ) (s : Moments)
    (hvalid : (RosserPrefixParams.parameters a b v).valid = true)
    (hm : mask < 2 ^ (b - a))
    (hdepth : b - a ≤ 2 ^ depth)
    (hcover : ∀ p, Nat.Prime p → a < p → p ≤ b →
      mask.testBit (p - (a + 1)) = true)
    (hmom : s = moments (windowOffsets depth mask 0 (b - a)))
    (hfirst : s.first ≤ s.count * a)
    (hupper : s.count * a ^ 2 - a * s.first + s.second ≤ a ^ 3)
    (hI : 0 < (RosserPrefixParams.parameters a b v).intercept)
    (hcount : 16384 * candidateCount mask (b - a) < 2 ^ 31)
    (hrhs : ((RosserPrefixParams.parameters a b v).intercept - 1) +
      (RosserPrefixParams.parameters a b v).slope *
        (32 * (((b - a) + 31) / 32 - 1)) < 2 ^ 31)
    (hcheck : packedCheck mask (b - a)
      ((RosserPrefixParams.parameters a b v).intercept - 1)
      (RosserPrefixParams.parameters a b v).slope = true)
    (hv : ((v : ℝ) / scale) ≤ reciprocalProduct a) :
    ((stepFromMoments v a s : ℝ) / scale ≤ reciprocalProduct b) ∧
      ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ b → RosserBlockCheck.Bound x := by
  have hab := (RosserPrefixParams.parameters_valid a b v hvalid).2.1
  have ha : 2 ≤ a := by
    have ha' := (RosserPrefixParams.parameters_valid a b v hvalid).1
    omega
  let ds := windowOffsets depth mask 0 (b - a)
  have hnodup : ds.Nodup := windowOffsets_nodup depth mask 0 (b - a)
  have hbounds : ∀ d ∈ ds, 0 < d ∧ d ≤ b - a := by
    intro d hd
    have hb := (mem_windowOffsets depth mask 0 (b - a) d).mp hd
    exact ⟨hb.1, hb.2.1⟩
  have hprimes : ∀ p, Nat.Prime p → a < p → p ≤ b → p - a ∈ ds := by
    intro p hp hap hpb
    apply (mem_windowOffsets depth mask 0 (b - a) (p - a)).mpr
    refine ⟨by omega, by omega, by omega, ?_⟩
    have heq : p - a - 1 + 0 = p - (a + 1) := by omega
    rw [heq]
    exact hcover p hp hap hpb
  have hfirst' : firstMoment ds ≤ ds.length * a := by
    simpa only [hmom, moments, firstMoment] using hfirst
  have hupper' : upperNumerator a ds ≤ a ^ 3 := by
    simpa only [hmom, moments, upperNumerator, firstMoment,
      secondMoment] using hupper
  have hnext := momentStep_reciprocalProduct scale v a b ds scale_pos hab.le ha
    hnodup hbounds hprimes hfirst' hupper' hv
  have heq : stepFromMoments v a s = momentStep v a ds := by
    rw [hmom]
    exact stepFromMoments_eq v a ds
  refine ⟨by simpa only [heq] using hnext, ?_⟩
  intro x hax hxb
  exact block_sound a b v mask hvalid hm hI hcount hrhs hcheck
    hcover hv x hax hxb

end RosserFastStep

-- Source: Solutions/RosserPackedMomentsSound.lean
/-! Correctness of packed first and second moments. -/

namespace RosserPackedMoments

open RosserBitMoments RosserScan

def strictMoments {α : Type} (s : Moments) (f : Moments → α) : α :=
  forceNat s.count fun c => forceNat s.first fun a => forceNat s.second fun b =>
    f ⟨c, a, b⟩

def bytes (mask stripe : Nat) : Nat → Moments → Moments
  | 0, s => s
  | j + 1, s =>
    forceNat ((mask >>> j) &&& stripe) fun bit =>
      strictMoments ⟨s.count + bit, s.first + j * bit, s.second + j * j * bit⟩
        (bytes mask stripe j)

def combine (bits half : Nat) (s : Moments) : Moments :=
  let stripe := RosserBitSieve.periodicMask (2 * half) (bits / (2 * half)) *
    (2 ^ half - 1)
  forceNat stripe fun stripe =>
  forceNat ((s.count >>> half) &&& stripe) fun cr =>
  forceNat ((s.first >>> half) &&& stripe) fun fr =>
    ⟨(s.count &&& stripe) + cr,
     (s.first &&& stripe) + fr + half * cr,
     (s.second &&& stripe) + ((s.second >>> half) &&& stripe) +
       2 * half * fr + half * half * cr⟩

def reduce (bits : Nat) : Nat → Nat → Moments → Moments
  | 0, _, s => s
  | fuel + 1, half, s =>
    strictMoments (combine bits half s) (reduce bits fuel (2 * half))

def packedMoments (depth mask : Nat) : Moments :=
  let bits := 2 ^ (depth + 3)
  forceNat (RosserBitSieve.periodicMask 8 (bits / 8)) fun stripe =>
    strictMoments (bytes mask stripe 8 ⟨0, 0, 0⟩) fun s =>
      translate 1 (reduce bits depth 8 s)



open RosserPackedBarrier

theorem strictMoments_eq {α : Type} (s : Moments) (f : Moments → α) :
    strictMoments s f = f s := by
  cases s
  simp only [strictMoments, RosserPackedBarrier.forceNat_eq]

def packed (w n : ℕ) (f : ℕ → Moments) : Moments :=
  ⟨pack (2 ^ w) n (fun i => (f i).count),
   pack (2 ^ w) n (fun i => (f i).first),
   pack (2 ^ w) n (fun i => (f i).second)⟩

def lane (mask w i : ℕ) : Moments :=
  ⟨∑ j ∈ Finset.range w, bitValue mask (w * i + j),
   ∑ j ∈ Finset.range w, j * bitValue mask (w * i + j),
   ∑ j ∈ Finset.range w, j * j * bitValue mask (w * i + j)⟩

theorem pair_extract (w n : ℕ) (hw : 0 < w) (f : ℕ → ℕ)
    (hf : ∀ i < 2 * n, f i < 2 ^ w) :
    let stripe := pack (2 ^ (2 * w)) n (fun _ => 2 ^ w - 1)
    (pack (2 ^ w) (2 * n) f &&& stripe =
      pack (2 ^ (2 * w)) n (fun i => f (2 * i))) ∧
    ((pack (2 ^ w) (2 * n) f >>> w) &&& stripe =
      pack (2 ^ (2 * w)) n (fun i => f (2 * i + 1))) := by
  dsimp only
  have hq : 0 < 2 ^ w := by positivity
  have hpow : 2 ^ w * 2 ^ w = 2 ^ (2 * w) := by rw [two_mul, pow_add]
  let g := fun i => f (2 * i) + 2 ^ w * f (2 * i + 1)
  have hg : ∀ i < n, g i < 2 ^ (2 * w) := by
    intro i hi
    have h0 := hf (2 * i) (by omega)
    have h1 := hf (2 * i + 1) (by omega)
    dsimp [g]
    rw [← hpow]
    nlinarith
  have hm : ∀ i < n, 2 ^ w - 1 < 2 ^ (2 * w - w) := by
    intro i hi
    rw [show 2 * w - w = w by omega]
    omega
  rw [pack_pair, hpow]
  change (_ &&& _) = _ ∧ (_ >>> w &&& _) = _
  constructor
  · rw [pack_and (2 * w) n (by omega) g _ hg (fun i hi => (hm i hi).trans_le
      (Nat.pow_le_pow_right (by omega) (by omega)))]
    apply pack_congr
    intro i hi
    simp only [g, Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (hf (2 * i) (by omega))]
  · rw [pack_shift_and (2 * w) n w (by omega) (by omega) g _ hg hm]
    apply pack_congr
    intro i hi
    simp only [g, Nat.shiftRight_eq_div_pow, Nat.add_mul_div_left _ _ hq,
      Nat.div_eq_of_lt (hf (2 * i) (by omega)), Nat.zero_add,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (hf (2 * i + 1) (by omega))]

theorem combine_sound (w n : ℕ) (hw : 0 < w) (f : ℕ → Moments)
    (hc : ∀ i < 2 * n, (f i).count < 2 ^ w)
    (hf : ∀ i < 2 * n, (f i).first < 2 ^ w)
    (hs : ∀ i < 2 * n, (f i).second < 2 ^ w) :
    combine (2 * w * n) w (packed w (2 * n) f) =
      packed (2 * w) n (fun i => merge (f (2 * i)) (translate w (f (2 * i + 1)))) := by
  have hstripe : RosserBitSieve.periodicMask (2 * w) ((2 * w * n) / (2 * w)) *
      (2 ^ w - 1) = pack (2 ^ (2 * w)) n (fun _ => 2 ^ w - 1) := by
    rw [Nat.mul_div_cancel_left _ (by omega), pack_const]
    unfold RosserBitSieve.periodicMask
    rw [pack_const_one _ _ (Nat.one_lt_two_pow (by omega)), pow_mul]
    ring
  obtain ⟨hcl, hcr⟩ := pair_extract w n hw (fun i => (f i).count) hc
  obtain ⟨hfl, hfr⟩ := pair_extract w n hw (fun i => (f i).first) hf
  obtain ⟨hsl, hsr⟩ := pair_extract w n hw (fun i => (f i).second) hs
  simp only [combine, RosserPackedBarrier.forceNat_eq, hstripe, packed]
  rw [hcl, hcr, hfl, hfr, hsl, hsr]
  apply Moments.ext <;> simp only [merge, translate, pack_add, pack_mul] <;> ring

theorem lane_pair (mask w i : ℕ) :
    lane mask (2 * w) i = merge (lane mask w (2 * i))
      (translate w (lane mask w (2 * i + 1))) := by
  apply Moments.ext
  · exact blockSum_pair (bitValue mask) w i
  · simp only [lane, merge, translate]
    rw [show 2 * w = w + w by omega, Finset.sum_range_add]
    have hpos : ∀ j : ℕ, (w + w) * i + (w + j) = w * (2 * i + 1) + j := by
      intro j; ring
    have hpos' : ∀ j : ℕ, (w + w) * i + j = w * (2 * i) + j := by
      intro j; ring
    simp only [hpos, hpos']
    have hsum :
        (∑ j ∈ Finset.range w, (w + j) * bitValue mask (w * (2 * i + 1) + j)) =
        w * (∑ j ∈ Finset.range w, bitValue mask (w * (2 * i + 1) + j)) +
        (∑ j ∈ Finset.range w, j * bitValue mask (w * (2 * i + 1) + j)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum]
    ring
  · simp only [lane, merge, translate]
    rw [show 2 * w = w + w by omega, Finset.sum_range_add]
    have hpos : ∀ j : ℕ, (w + w) * i + (w + j) = w * (2 * i + 1) + j := by
      intro j; ring
    have hpos' : ∀ j : ℕ, (w + w) * i + j = w * (2 * i) + j := by
      intro j; ring
    simp only [hpos, hpos']
    have hsum :
        (∑ j ∈ Finset.range w, (w + j) * (w + j) * bitValue mask (w * (2 * i + 1) + j)) =
        (∑ j ∈ Finset.range w, j * j * bitValue mask (w * (2 * i + 1) + j)) +
        2 * w * (∑ j ∈ Finset.range w, j * bitValue mask (w * (2 * i + 1) + j)) +
        w * w * (∑ j ∈ Finset.range w, bitValue mask (w * (2 * i + 1) + j)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hsum]
    ring

theorem bytes_eq (mask stripe j : ℕ) (s : Moments) :
    bytes mask stripe j s =
      ⟨s.count + ∑ i ∈ Finset.range j, ((mask >>> i) &&& stripe),
       s.first + ∑ i ∈ Finset.range j, i * ((mask >>> i) &&& stripe),
       s.second + ∑ i ∈ Finset.range j, i * i * ((mask >>> i) &&& stripe)⟩ := by
  induction j generalizing s with
  | zero => simp [bytes]
  | succ j ih =>
    simp only [bytes, RosserPackedBarrier.forceNat_eq, strictMoments_eq, ih, Finset.sum_range_succ]
    apply Moments.ext <;> dsimp only <;> ring

theorem pack_sum (q n terms : ℕ) (f : ℕ → ℕ → ℕ) :
    pack q n (fun i => ∑ j ∈ Finset.range terms, f i j) =
      ∑ j ∈ Finset.range terms, pack q n (fun i => f i j) := by
  induction terms with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; rw [pack_const q n 0]; simp
  | succ terms ih => simp only [Finset.sum_range_succ, pack_add, ih]

theorem byte_plane (mask n j : ℕ) (hj : j < 8) (hm : mask < 2 ^ (8 * n)) :
    ((mask >>> j) &&& RosserBitSieve.periodicMask 8 n) =
      pack 256 n (fun i => bitValue mask (8 * i + j)) := by
  let f := fun i => mask / 2 ^ (8 * i) % 2 ^ 8
  have hf : ∀ i < n, f i < 2 ^ 8 := fun i hi => Nat.mod_lt _ (by positivity)
  have hp : pack (2 ^ 8) n f = mask := pack_digits 8 n mask (by omega) hm
  have hs : RosserBitSieve.periodicMask 8 n = pack (2 ^ 8) n (fun _ => 1) := by
    unfold RosserBitSieve.periodicMask
    rw [pack_const_one _ _ (by norm_num), pow_mul]
  rw [← hp, hs, pack_shift_and 8 n j (by omega) (by omega) f _ hf
    (fun i hi => Nat.one_lt_two_pow (by omega))]
  have hbase : (2 ^ 8 : ℕ) = 256 := by norm_num
  rw [hbase]
  apply pack_congr
  intro i hi
  have hb := pack_testBit 8 n i j hf hi hj
  rw [hp] at hb
  simp only [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rw [← bitValue_eq_digit]
  rw [← hbase, hp]
  exact (congrArg Bool.toNat hb).symm

theorem bytes_sound (mask n : ℕ) (hm : mask < 2 ^ (8 * n)) :
    bytes mask (RosserBitSieve.periodicMask 8 n) 8 ⟨0, 0, 0⟩ =
      packed 8 n (lane mask 8) := by
  rw [bytes_eq]
  apply Moments.ext <;> simp only [packed, lane, Nat.zero_add, pack_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    exact byte_plane mask n j (Finset.mem_range.mp hj) hm
  · apply Finset.sum_congr rfl
    intro j hj
    rw [byte_plane mask n j (Finset.mem_range.mp hj) hm, pack_mul]
    norm_num
  · apply Finset.sum_congr rfl
    intro j hj
    rw [byte_plane mask n j (Finset.mem_range.mp hj) hm, pack_mul]
    norm_num


def laneBudget (w : ℕ) : ℕ := ∑ j ∈ Finset.range w, (j + 1) ^ 2

theorem lane_le_budget (mask w i : ℕ) :
    (lane mask w i).count ≤ laneBudget w ∧
    (lane mask w i).first ≤ laneBudget w ∧
    (lane mask w i).second ≤ laneBudget w := by
  have hb := fun j => bitValue_le_one mask (w * i + j)
  dsimp only [lane, laneBudget]
  constructor
  · apply Finset.sum_le_sum
    intro j hj
    exact (hb j).trans (Nat.succ_le_of_lt (by positivity))
  constructor
  · apply Finset.sum_le_sum
    intro j hj
    have := hb j
    nlinarith
  · apply Finset.sum_le_sum
    intro j hj
    have h := Nat.mul_le_mul_left (j * j) (hb j)
    simp only [Nat.mul_one] at h
    nlinarith

theorem laneBudget_le_cube (w : ℕ) : laneBudget w ≤ w ^ 3 := by
  calc
    laneBudget w ≤ ∑ j ∈ Finset.range w, w ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have h := Finset.mem_range.mp hj
      exact Nat.pow_le_pow_left (by omega) 2
    _ = w ^ 3 := by simp; ring

theorem triple_lt_power (d : ℕ) : 3 * (d + 4) < 2 ^ (d + 4) := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    rw [show d + 1 + 4 = (d + 4) + 1 by omega, pow_succ]
    omega

theorem laneBudget_lt (d : ℕ) : laneBudget (2 ^ (d + 3)) < 2 ^ (2 ^ (d + 3)) := by
  cases d with
  | zero => decide
  | succ d =>
    have h := laneBudget_le_cube (2 ^ (d + 4))
    have hp : (2 ^ (d + 4)) ^ 3 < 2 ^ (2 ^ (d + 4)) := by
      rw [← pow_mul]
      apply Nat.pow_lt_pow_right (by omega)
      simpa only [Nat.mul_comm] using triple_lt_power d
    simpa only [Nat.add_assoc] using h.trans_lt hp

theorem packed_congr (w n : ℕ) {f g : ℕ → Moments}
    (h : ∀ i < n, f i = g i) : packed w n f = packed w n g := by
  apply Moments.ext <;> apply pack_congr <;> intro i hi <;> rw [h i hi]

theorem combine_lane (d n mask : ℕ) :
    combine (2 * 2 ^ (d + 3) * n) (2 ^ (d + 3))
      (packed (2 ^ (d + 3)) (2 * n) (lane mask (2 ^ (d + 3)))) =
      packed (2 * 2 ^ (d + 3)) n (lane mask (2 * 2 ^ (d + 3))) := by
  have hb := laneBudget_lt d
  rw [combine_sound _ _ (by positivity) _
    (fun i hi => ((lane_le_budget mask _ i).1).trans_lt hb)
    (fun i hi => ((lane_le_budget mask _ i).2.1).trans_lt hb)
    (fun i hi => ((lane_le_budget mask _ i).2.2).trans_lt hb)]
  apply packed_congr
  intro i hi
  exact (lane_pair mask _ i).symm

theorem reduce_sound (fuel d mask : ℕ) :
    reduce (2 ^ (fuel + d + 3)) fuel (2 ^ (d + 3))
      (packed (2 ^ (d + 3)) (2 ^ fuel) (lane mask (2 ^ (d + 3)))) =
      lane mask (2 ^ (fuel + d + 3)) 0 := by
  induction fuel generalizing d with
  | zero => simp [reduce, packed, pack]
  | succ fuel ih =>
    have hbits : 2 ^ (fuel + 1 + d + 3) = 2 * 2 ^ (d + 3) * 2 ^ fuel := by
      rw [show fuel + 1 + d + 3 = 1 + (d + 3) + fuel by omega]
      simp only [pow_add, pow_one]
    have hnext : 2 * 2 ^ (d + 3) = 2 ^ ((d + 1) + 3) := by
      rw [show d + 1 + 3 = 1 + (d + 3) by omega]
      simp only [pow_add, pow_one]
    simp only [reduce, strictMoments_eq]
    rw [hbits, show 2 ^ (fuel + 1) = 2 * 2 ^ fuel by rw [pow_succ]; omega,
      combine_lane, hnext]
    rw [← pow_add]
    convert ih (d + 1) using 1 <;> congr 2 <;> omega

theorem moments_filter_range (mask w : ℕ) :
    moments ((List.range w).filter (fun i => mask.testBit i)) = lane mask w 0 := by
  induction w with
  | zero => simp [moments, lane]
  | succ w ih =>
    have hc := congrArg Moments.count ih
    have hf := congrArg Moments.first ih
    have hs := congrArg Moments.second ih
    simp only [moments, lane, Nat.mul_zero, Nat.zero_add] at hc hf hs
    apply Moments.ext <;>
      simp only [moments, List.range_succ, List.filter_append,
        List.length_append, List.sum_append, List.map_append, lane,
        Nat.mul_zero, Nat.zero_add, Finset.sum_range_succ]
    · rw [hc]
      cases h : mask.testBit w <;> simp [List.filter, h, bitValue]
    · rw [hf]
      cases h : mask.testBit w <;> simp [List.filter, h, bitValue]
    · rw [hs]
      cases h : mask.testBit w <;> simp [List.filter, h, bitValue, pow_two]

theorem enumBits_perm_filter (depth mask : ℕ) :
    (RosserBitSieve.enumBits depth 0 mask).Perm
      ((List.range (2 ^ depth)).filter (fun i => mask.testBit i)) := by
  apply (List.perm_ext_iff_of_nodup (RosserBitSieve.enumBits_nodup _ _ _)
    ((List.nodup_range).filter _)).mpr
  intro x
  simp only [RosserBitSieve.mem_enumBits, Nat.zero_le, Nat.zero_add, Nat.sub_zero,
    true_and, List.mem_filter, List.mem_range]

theorem lane_eq_moments (depth mask : ℕ) :
    lane mask (2 ^ depth) 0 = moments (RosserBitSieve.enumBits depth 0 mask) := by
  rw [moments_perm (enumBits_perm_filter depth mask), moments_filter_range]

/-- All three SWAR moments are exactly the moments of the selected offsets. -/
theorem packedMoments_sound (depth mask : ℕ) (hm : mask < 2 ^ (2 ^ (depth + 3))) :
    packedMoments depth mask =
      moments (RosserBitSieve.enumBits (depth + 3) 1 mask) := by
  have hbits : 2 ^ (depth + 3) = 8 * 2 ^ depth := by
    rw [pow_add]
    norm_num
    omega
  have hdiv : 2 ^ (depth + 3) / 8 = 2 ^ depth := by
    rw [hbits, Nat.mul_div_cancel_left _ (by omega)]
  have hmask : mask < 2 ^ (8 * 2 ^ depth) := by rwa [← hbits]
  simp only [packedMoments, RosserPackedBarrier.forceNat_eq, strictMoments_eq, hdiv]
  rw [bytes_sound mask (2 ^ depth) hmask]
  have hr := reduce_sound depth 0 mask
  simp only [Nat.add_zero, Nat.zero_add] at hr
  norm_num only [Nat.reducePow] at hr
  rw [hr, lane_eq_moments, enumBits_shift (depth + 3) 1 mask, moments_shift]

/-- Padding a mask adds no selected offsets. -/
theorem candidateCount_eq_enumBits_length (depth mask len : ℕ)
    (hm : mask < 2 ^ len) (hlen : len ≤ 2 ^ (depth + 3)) :
    candidateCount mask len = (RosserBitSieve.enumBits (depth + 3) 1 mask).length := by
  rw [enumBits_shift, List.length_map]
  rw [← candidateCount_pad mask len (2 ^ (depth + 3)) hm hlen]
  exact (enumBits_perm_filter (depth + 3) mask).length_eq.symm

theorem packedMoments_eq_fastMoments (depth mask : ℕ)
    (hm : mask < 2 ^ (2 ^ (depth + 3))) :
    packedMoments depth mask = fastMoments depth 1 mask := by
  rw [packedMoments_sound depth mask hm, fastMoments_sound]

#print axioms packedMoments_sound
#print axioms candidateCount_eq_enumBits_length

end RosserPackedMoments

-- Source: Solutions/RosserFastCompute.lean
/-! The fast numerical block verifier, parameterized by a certified moments
implementation. -/

namespace RosserFastCompute

open RosserScan RosserBitMoments RosserPackedBarrier
open RosserPrefixParams RosserLogCertificate

def strictMoments {α : Type} (s : Moments) (f : Moments → α) : α :=
  forceNat s.count fun c => forceNat s.first fun u => forceNat s.second fun t =>
    f ⟨c, u, t⟩

theorem strictMoments_eq {α : Type} (s : Moments) (f : Moments → α) :
    strictMoments s f = f s := by
  cases s with
  | mk c u t => simp only [strictMoments, RosserScan.forceNat_eq]

def depthFor (len : ℕ) : ℕ :=
  if len ≤ 8 then 0 else Nat.log2 ((len - 1) / 8) + 1

def stepWith (mom : ℕ → ℕ → Moments) (mask a b v : ℕ) : Option ℕ :=
  let len := b - a
  let depth := depthFor len
  strictMoments (mom depth mask) fun s =>
  let par := parameters a b v
  forceNat par.intercept fun intercept =>
  forceNat par.slope fun slope =>
    if par.valid && decide (0 < intercept ∧
      16384 * s.count < 2 ^ 31 ∧
      intercept + slope * (32 * ((len + 31) / 32 - 1)) < 2 ^ 31 ∧
      mask < 2 ^ len ∧ len ≤ 2 ^ (depth + 3) ∧
      s.first ≤ s.count * a ∧
      s.count * a ^ 2 - a * s.first + s.second ≤ a ^ 3) &&
      packedCheck mask len (intercept - 1) slope then
        some (stepFromMoments v a s)
    else none

theorem windowOffsets_eq_enumBits (depth mask len : ℕ) (hm : mask < 2 ^ len) :
    RosserBitSieve.windowOffsets (depth + 3) mask 0 len =
      RosserBitSieve.enumBits (depth + 3) 1 mask := by
  simp only [RosserBitSieve.windowOffsets, pow_zero, Nat.div_one,
    Nat.mod_eq_of_lt hm]
  rw [RosserBitMoments.enumBits_shift (depth + 3) 1 mask]
  apply List.map_congr_left
  intro d hd
  omega

theorem stepWith_sound (mom : ℕ → ℕ → Moments)
    (hmom : ∀ depth mask len, mask < 2 ^ len →
      len ≤ 2 ^ (depth + 3) →
      mom depth mask = RosserBitMoments.moments
        (RosserBitSieve.windowOffsets (depth + 3) mask 0 len))
    (mask a b v w : ℕ)
    (hcover : ∀ p, Nat.Prime p → a < p → p ≤ b →
      mask.testBit (p - (a + 1)) = true)
    (hv : ((v : ℝ) / scale) ≤ RosserMomentBridge.reciprocalProduct a)
    (h : stepWith mom mask a b v = some w) :
    ((w : ℝ) / scale ≤ RosserMomentBridge.reciprocalProduct b) ∧
      ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ b → RosserBlockCheck.Bound x := by
  let len := b - a
  let depth := depthFor len
  let s := mom depth mask
  let par := parameters a b v
  simp only [stepWith, strictMoments_eq, RosserScan.forceNat_eq] at h
  change (if par.valid && decide (0 < par.intercept ∧
      16384 * s.count < 2 ^ 31 ∧
      par.intercept + par.slope * (32 * ((len + 31) / 32 - 1)) < 2 ^ 31 ∧
      mask < 2 ^ len ∧ len ≤ 2 ^ (depth + 3) ∧
      s.first ≤ s.count * a ∧
      s.count * a ^ 2 - a * s.first + s.second ≤ a ^ 3) &&
      packedCheck mask len (par.intercept - 1) par.slope then
        some (stepFromMoments v a s)
    else none) = some w at h
  let ok := par.valid && decide (0 < par.intercept ∧
      16384 * s.count < 2 ^ 31 ∧
      par.intercept + par.slope * (32 * ((len + 31) / 32 - 1)) < 2 ^ 31 ∧
      mask < 2 ^ len ∧ len ≤ 2 ^ (depth + 3) ∧
      s.first ≤ s.count * a ∧
      s.count * a ^ 2 - a * s.first + s.second ≤ a ^ 3) &&
      packedCheck mask len (par.intercept - 1) par.slope
  change (if ok then some (stepFromMoments v a s) else none) = some w at h
  have hc : ok = true := by
    cases hok : ok with
    | false => simp only [hok, ite_false] at h; cases h
    | true => rfl
  simp only [hc, ite_true] at h
  have hw : stepFromMoments v a s = w := Option.some.inj h
  simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨hvalid, hn⟩, hcheck⟩
  obtain ⟨hI, hscount, hrhs0, hmask, hdepth, hfirst, hupper⟩ :=
    hn
  have hmomeq := hmom depth mask len hmask hdepth
  have hlen : len ≤ 2 ^ (depth + 3) := hdepth
  have hcnt : RosserPackedBarrier.candidateCount mask len = s.count := by
    rw [RosserPackedMoments.candidateCount_eq_enumBits_length depth mask len hmask hlen]
    change (RosserBitSieve.enumBits (depth + 3) 1 mask).length =
      (mom depth mask).count
    rw [hmomeq, windowOffsets_eq_enumBits depth mask len hmask]
    rfl
  have hscount' : 16384 * RosserPackedBarrier.candidateCount mask len < 2 ^ 31 := by
    rwa [hcnt]
  have hrhs : (par.intercept - 1) + par.slope *
      (32 * ((len + 31) / 32 - 1)) < 2 ^ 31 := by
    omega
  have hs := RosserFastStep.step_sound a b v mask (depth + 3) s
    hvalid hmask hdepth hcover hmomeq hfirst hupper hI hscount' hrhs hcheck hv
  simpa only [hw] using hs

def step (mask a b v : ℕ) : Option ℕ :=
  stepWith RosserPackedMoments.packedMoments mask a b v

theorem step_sound (mask a b v w : ℕ)
    (hcover : ∀ p, Nat.Prime p → a < p → p ≤ b →
      mask.testBit (p - (a + 1)) = true)
    (hv : ((v : ℝ) / scale) ≤ RosserMomentBridge.reciprocalProduct a)
    (h : step mask a b v = some w) :
    ((w : ℝ) / scale ≤ RosserMomentBridge.reciprocalProduct b) ∧
      ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ b → RosserBlockCheck.Bound x := by
  exact stepWith_sound RosserPackedMoments.packedMoments
    (by
      intro depth mask len hmask hlen
      apply (RosserPackedMoments.packedMoments_sound depth mask
        (hmask.trans_le (Nat.pow_le_pow_right (by omega) hlen))).trans
      rw [windowOffsets_eq_enumBits depth mask len hmask])
    mask a b v w hcover hv h

end RosserFastCompute

-- Source: Solutions/RosserMediumChain.lean
/-! Compose checked prefix blocks using cached sieve masks for segments of at most 2^20 integers. -/

namespace RosserMediumChain

/-- The shared periodic masks cover every segment of this maximum length. -/
def fixedLen : ℕ := 1048576

open RosserScan RosserLogCertificate RosserMomentBridge

structure Checkpoint where
  a : ℕ
  b : ℕ
  initial : ℕ
  final : ℕ

structure Group where
  base : ℕ
  top : ℕ
  initial : ℕ
  final : ℕ
  checkpoints : List Checkpoint

def checkPoints (mask base : ℕ) : List Checkpoint → Bool
  | [] => true
  | c :: cs =>
    (forceNat ((mask >>> (c.a - base)) &&& (2 ^ (c.b - c.a) - 1)) fun window =>
      RosserFastCompute.step window c.a c.b c.initial == some c.final) &&
        checkPoints mask base cs

def checkGroups (ds : List (ℕ × ℕ)) : List Group → Bool
  | [] => true
  | g :: gs =>
    (forceNat (RosserCachedSieve.mask ds g.base g.top) fun mask =>
      checkPoints mask g.base g.checkpoints) && checkGroups ds gs

theorem checkGroups_append (ds : List (ℕ × ℕ)) (xs ys : List Group) :
    checkGroups ds (xs ++ ys) = (checkGroups ds xs && checkGroups ds ys) := by
  induction xs with
  | nil => simp [checkGroups]
  | cons g gs ih =>
    simp only [List.cons_append, checkGroups, ih, Bool.and_assoc]

def allGroups (gs : List Group) : Bool :=
  RosserCachedSieve.withMasks fixedLen RosserSieveData.divisors fun ds =>
    checkGroups ds gs

theorem checkPoints_sound (mask base : ℕ) (cs : List Checkpoint)
    (h : checkPoints mask base cs = true) :
    ∀ c ∈ cs, RosserFastCompute.step
      (mask / 2 ^ (c.a - base) % 2 ^ (c.b - c.a))
      c.a c.b c.initial = some c.final := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [checkPoints, RosserScan.forceNat_eq, Nat.shiftRight_eq_div_pow,
      Nat.and_two_pow_sub_one_eq_mod, Bool.and_eq_true] at h
    obtain ⟨hc, hcs⟩ := h
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact beq_iff_eq.mp hc
    · exact ih hcs d hd

theorem checkGroups_sound (ds : List (ℕ × ℕ)) (gs : List Group)
    (h : checkGroups ds gs = true) :
    ∀ g ∈ gs, ∀ c ∈ g.checkpoints,
      RosserFastCompute.step
        (RosserCachedSieve.mask ds g.base g.top /
          2 ^ (c.a - g.base) % 2 ^ (c.b - c.a))
        c.a c.b c.initial = some c.final := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [checkGroups, RosserScan.forceNat_eq, Bool.and_eq_true] at h
    obtain ⟨hg, hgs⟩ := h
    intro g' hg' c hc
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact checkPoints_sound _ _ _ hg c hc
    · exact ih hgs g' hg' c hc

def Linked (a v top w : ℕ) : List Checkpoint → Prop
  | [] => a = top ∧ v = w
  | c :: cs =>
      c.a = a ∧ c.initial = v ∧ a < c.b ∧ c.b ≤ top ∧
        Linked c.b c.final top w cs

def LinkedGroups (a v top : ℕ) : List Group → Prop
  | [] => a = top
  | g :: gs =>
      g.base = a ∧ g.initial = v ∧ g.base < g.top ∧
        g.top - g.base ≤ fixedLen ∧
        Linked g.base g.initial g.top g.final g.checkpoints ∧
        LinkedGroups g.top g.final top gs

def linkedPoints (a v top w : ℕ) : List Checkpoint → Bool
  | [] => decide (a = top ∧ v = w)
  | c :: cs =>
      decide (c.a = a ∧ c.initial = v ∧ a < c.b ∧ c.b ≤ top) &&
        linkedPoints c.b c.final top w cs

def linkedGroups (a v top : ℕ) : List Group → Bool
  | [] => decide (a = top)
  | g :: gs =>
      decide (g.base = a ∧ g.initial = v ∧ g.base < g.top ∧
        g.top - g.base ≤ fixedLen) &&
        linkedPoints g.base g.initial g.top g.final g.checkpoints &&
        linkedGroups g.top g.final top gs

theorem linkedPoints_sound (a v top w : ℕ) (cs : List Checkpoint)
    (h : linkedPoints a v top w cs = true) : Linked a v top w cs := by
  induction cs generalizing a v with
  | nil => simpa only [linkedPoints, decide_eq_true_eq, Linked] using h
  | cons c cs ih =>
    simp only [linkedPoints, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨hc, hrest⟩
    exact ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2,
      ih c.b c.final hrest⟩

theorem linkedGroups_sound (a v top : ℕ) (gs : List Group)
    (h : linkedGroups a v top gs = true) : LinkedGroups a v top gs := by
  induction gs generalizing a v with
  | nil => simpa only [linkedGroups, decide_eq_true_eq, LinkedGroups] using h
  | cons g gs ih =>
    simp only [linkedGroups, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨⟨hg, hp⟩, hrest⟩
    exact ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2,
      linkedPoints_sound _ _ _ _ _ hp, ih g.top g.final hrest⟩

theorem linked_sound (mask base top a v w : ℕ) (cs : List Checkpoint)
    (hcover : RosserScan.Covers base top mask)
    (hbase : base ≤ a)
    (hv : ((v : ℝ) / scale) ≤ reciprocalProduct a)
    (hlinked : Linked a v top w cs)
    (hchecks : ∀ c ∈ cs, RosserFastCompute.step
      (mask / 2 ^ (c.a - base) % 2 ^ (c.b - c.a))
      c.a c.b c.initial = some c.final) :
    ((w : ℝ) / scale ≤ reciprocalProduct top) ∧
      ∀ x : ℝ, (a : ℝ) < x → x ≤ top → RosserBlockCheck.Bound x := by
  induction cs generalizing a v with
  | nil =>
    obtain ⟨rfl, rfl⟩ := hlinked
    refine ⟨hv, ?_⟩
    intro x hax hxt
    linarith
  | cons c cs ih =>
    obtain ⟨hca, hcv, hab, hbt, hrest⟩ := hlinked
    have hstep := hchecks c (by simp)
    have hcover' := RosserPrefixBridge.window_mask_covers base top mask
      c.a c.b hcover (by omega) hbt
    have hrec : ((c.initial : ℝ) / scale) ≤ reciprocalProduct c.a := by
      simpa only [hca, hcv] using hv
    have hs := RosserFastCompute.step_sound _ _ _ _ _ hcover' hrec hstep
    have htail : ∀ d ∈ cs, RosserFastCompute.step
        (mask / 2 ^ (d.a - base) % 2 ^ (d.b - d.a))
        d.a d.b d.initial = some d.final := by
      intro d hd
      exact hchecks d (List.mem_cons_of_mem _ hd)
    have ht := ih c.b c.final (by omega) hs.1 hrest htail
    refine ⟨ht.1, ?_⟩
    intro x hax hxt
    by_cases hxb : x ≤ c.b
    · exact hs.2 x (by exact_mod_cast (show a = c.a by omega) ▸ le_of_lt hax) hxb
    · exact ht.2 x (lt_of_not_ge hxb) hxt

def cachedPairs : List (ℕ × ℕ) :=
  RosserCachedSieve.pairs fixedLen RosserSieveData.divisors

theorem group_sound (g : Group)
    (hshape : g.base < g.top ∧ g.top - g.base ≤ fixedLen)
    (hlink : Linked g.base g.initial g.top g.final g.checkpoints)
    (hcheck : checkPoints
      (RosserCachedSieve.mask cachedPairs g.base g.top)
      g.base g.checkpoints = true)
    (hv : ((g.initial : ℝ) / scale) ≤ reciprocalProduct g.base) :
    ((g.final : ℝ) / scale ≤ reciprocalProduct g.top) ∧
      ∀ x : ℝ, (g.base : ℝ) < x → x ≤ g.top → RosserBlockCheck.Bound x := by
  let m := RosserCachedSieve.mask cachedPairs g.base g.top
  have hcover : RosserScan.Covers g.base g.top m := by
    intro p hp hbp hpt
    exact RosserCachedSieve.mask_prime fixedLen g.base g.top
      RosserSieveData.divisors RosserSieveData.divisors_ge_two
      hshape.1 hshape.2 p hp hbp hpt
  have hs := checkPoints_sound m g.base g.checkpoints hcheck
  exact linked_sound m g.base g.top g.base g.initial g.final
    g.checkpoints hcover (le_refl _) hv hlink hs

theorem groups_sound (gs : List Group) (a v top : ℕ)
    (hv : ((v : ℝ) / scale) ≤ reciprocalProduct a)
    (hlink : LinkedGroups a v top gs)
    (hcheck : checkGroups cachedPairs gs = true) :
    ∀ x : ℝ, (a : ℝ) < x → x ≤ top → RosserBlockCheck.Bound x := by
  induction gs generalizing a v with
  | nil =>
    intro x hax hxt
    change a = top at hlink
    subst top
    linarith
  | cons g gs ih =>
    obtain ⟨hga, hgv, hgt, hwidth, hpoints, hrest⟩ := hlink
    simp only [checkGroups, RosserScan.forceNat_eq, Bool.and_eq_true] at hcheck
    obtain ⟨hgc, hgs⟩ := hcheck
    have hv' : ((g.initial : ℝ) / scale) ≤ reciprocalProduct g.base := by
      simpa only [hga, hgv] using hv
    have hg := group_sound g ⟨hgt, hwidth⟩ hpoints hgc hv'
    have ht := ih g.top g.final hg.1 hrest hgs
    intro x hax hxt
    by_cases hxg : x ≤ g.top
    · apply hg.2 x
      · have : (a : ℝ) = g.base := by exact_mod_cast hga.symm
        linarith only [hax, this]
      · exact hxg
    · exact ht x (lt_of_not_ge hxg) hxt

theorem allGroups_sound (gs : List Group) (a v top : ℕ)
    (hv : ((v : ℝ) / scale) ≤ reciprocalProduct a)
    (hlink : LinkedGroups a v top gs)
    (hcheck : allGroups gs = true) :
    ∀ x : ℝ, (a : ℝ) < x → x ≤ top → RosserBlockCheck.Bound x := by
  simp only [allGroups, RosserCachedSieve.withMasks_eq] at hcheck
  exact groups_sound gs a v top hv hlink hcheck


theorem allGroups_append (xs ys : List Group) :
    allGroups (xs ++ ys) = (allGroups xs && allGroups ys) := by
  simp only [allGroups, RosserCachedSieve.withMasks_eq, checkGroups_append]

theorem allGroups_append_true {xs ys : List Group}
    (hx : allGroups xs = true) (hy : allGroups ys = true) :
    allGroups (xs ++ ys) = true := by
  rw [allGroups_append, hx, hy]
  rfl

#print axioms allGroups_sound

end RosserMediumChain

-- Source: Solutions/RosserMediumSqrtChain.lean
/-! A medium-segment verifier that stops the divisor list at the square-root
cutoff. Its prime-covering proof only uses that selected divisors come from the
original list; no equality with the unfiltered sieve is assumed. -/

namespace RosserMediumSqrtChain

open RosserScan RosserLogCertificate RosserMomentBridge

abbrev Checkpoint := RosserMediumChain.Checkpoint
abbrev Group := RosserMediumChain.Group
abbrev fixedLen := RosserMediumChain.fixedLen
abbrev checkPoints := RosserMediumChain.checkPoints
abbrev Linked := RosserMediumChain.Linked
abbrev LinkedGroups := RosserMediumChain.LinkedGroups
abbrev linkedGroups := RosserMediumChain.linkedGroups
abbrev linkedGroups_sound := RosserMediumChain.linkedGroups_sound

def select (top : ℕ) (ds : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  ds.takeWhile (fun dm => decide (dm.1 * dm.1 ≤ top))

def mask (ds : List (ℕ × ℕ)) (base top : ℕ) : ℕ :=
  RosserCachedSieve.mask (select top ds) base top

theorem select_pairs (len top : ℕ) (ds : List ℕ) :
    select top (RosserCachedSieve.pairs len ds) =
      RosserCachedSieve.pairs len
        (ds.takeWhile (fun d => decide (d * d ≤ top))) := by
  simp only [select, RosserCachedSieve.pairs, List.takeWhile_map,
    Function.comp_def]

theorem mask_prime (len base top : ℕ) (ds : List ℕ)
    (hds : ∀ d ∈ ds, 2 ≤ d) (hbase : base < top)
    (hlen : top - base ≤ len) :
    Covers base top (mask (RosserCachedSieve.pairs len ds) base top) := by
  unfold mask
  rw [select_pairs]
  apply RosserCachedSieve.mask_prime len base top _ _ hbase hlen
  intro d hd
  exact hds d ((List.takeWhile_subset _ ) hd)

def checkGroups (ds : List (ℕ × ℕ)) : List Group → Bool
  | [] => true
  | g :: gs =>
    (forceNat (mask ds g.base g.top) fun mask =>
      checkPoints mask g.base g.checkpoints) && checkGroups ds gs

theorem checkGroups_append (ds : List (ℕ × ℕ)) (xs ys : List Group) :
    checkGroups ds (xs ++ ys) = (checkGroups ds xs && checkGroups ds ys) := by
  induction xs with
  | nil => simp [checkGroups]
  | cons g gs ih =>
    simp only [List.cons_append, checkGroups, ih, Bool.and_assoc]

def allGroups (gs : List Group) : Bool :=
  RosserCachedSieve.withMasks fixedLen RosserSieveData.divisors fun ds =>
    checkGroups ds gs

def cachedPairs : List (ℕ × ℕ) :=
  RosserCachedSieve.pairs fixedLen RosserSieveData.divisors

theorem group_sound (g : Group)
    (hshape : g.base < g.top ∧ g.top - g.base ≤ fixedLen)
    (hlink : Linked g.base g.initial g.top g.final g.checkpoints)
    (hcheck : checkPoints (mask cachedPairs g.base g.top)
      g.base g.checkpoints = true)
    (hv : ((g.initial : ℝ) / scale) ≤ reciprocalProduct g.base) :
    ((g.final : ℝ) / scale ≤ reciprocalProduct g.top) ∧
      ∀ x : ℝ, (g.base : ℝ) < x → x ≤ g.top → RosserBlockCheck.Bound x := by
  have hcover : Covers g.base g.top (mask cachedPairs g.base g.top) :=
    mask_prime fixedLen g.base g.top RosserSieveData.divisors
      RosserSieveData.divisors_ge_two hshape.1 hshape.2
  exact RosserMediumChain.linked_sound _ _ _ _ _ _ _ hcover (le_refl _) hv hlink
    (RosserMediumChain.checkPoints_sound _ _ _ hcheck)

theorem groups_sound (gs : List Group) (a v top : ℕ)
    (hv : ((v : ℝ) / scale) ≤ reciprocalProduct a)
    (hlink : LinkedGroups a v top gs)
    (hcheck : checkGroups cachedPairs gs = true) :
    ∀ x : ℝ, (a : ℝ) < x → x ≤ top → RosserBlockCheck.Bound x := by
  induction gs generalizing a v with
  | nil =>
    intro x hax hxt
    change a = top at hlink
    subst top
    linarith
  | cons g gs ih =>
    obtain ⟨hga, hgv, hgt, hwidth, hpoints, hrest⟩ := hlink
    simp only [checkGroups, RosserScan.forceNat_eq, Bool.and_eq_true] at hcheck
    obtain ⟨hgc, hgs⟩ := hcheck
    have hv' : ((g.initial : ℝ) / scale) ≤ reciprocalProduct g.base := by
      simpa only [hga, hgv] using hv
    have hg := group_sound g ⟨hgt, hwidth⟩ hpoints hgc hv'
    have ht := ih g.top g.final hg.1 hrest hgs
    intro x hax hxt
    by_cases hxg : x ≤ g.top
    · apply hg.2 x
      · have : (a : ℝ) = g.base := by exact_mod_cast hga.symm
        linarith only [hax, this]
      · exact hxg
    · exact ht x (lt_of_not_ge hxg) hxt

theorem allGroups_sound (gs : List Group) (a v top : ℕ)
    (hv : ((v : ℝ) / scale) ≤ reciprocalProduct a)
    (hlink : LinkedGroups a v top gs)
    (hcheck : allGroups gs = true) :
    ∀ x : ℝ, (a : ℝ) < x → x ≤ top → RosserBlockCheck.Bound x := by
  simp only [allGroups, RosserCachedSieve.withMasks_eq] at hcheck
  exact groups_sound gs a v top hv hlink hcheck

theorem allGroups_append (xs ys : List Group) :
    allGroups (xs ++ ys) = (allGroups xs && allGroups ys) := by
  simp only [allGroups, RosserCachedSieve.withMasks_eq, checkGroups_append]

theorem allGroups_append_true {xs ys : List Group}
    (hx : allGroups xs = true) (hy : allGroups ys = true) :
    allGroups (xs ++ ys) = true := by
  rw [allGroups_append, hx, hy]
  rfl

#print axioms allGroups_sound

end RosserMediumSqrtChain


