-- Prove2me | Definitions.Def_dusart_theta_mesh_numeric
-- name    : dusart_theta_mesh_numeric
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T17:42:02.401988+00:00
-- url     : https://prove2.me/theorems/79746d2a-a8b5-4489-bc28-38ea12261d33
-- title:
--   Dusart finite mesh:
-- statement:
--   The  component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Lean.Elab.Tactic.Decide
set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option Elab.async false
set_option maxRecDepth 200000
namespace DusartNumeric
def forceNat {α : Type} (n : Nat) (f : Nat → α) : α := match n with
 | 0 => f 0
 | n+1 => f (n+1)
def periodicMask (d count : Nat) : Nat := (2^(d*count)-1)/(2^d-1)
def cdiv (a b : Nat) : Nat := (a+b-1)/b
local infixl:70 " ⌈÷ᵤ⌉ " => cdiv
def scale : Nat := 1000000
/-- Fuel-based binary logarithm: structural recursion, cheap in the kernel. -/
def log2f : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n < 2 then 0 else log2f f (n / 2) + 1
def log2k (n : Nat) : Nat := log2f 64 n
def logTermUp (a d i : Nat) : Nat :=
  (scale * 2 * a ^ (2 * i + 1)) ⌈÷ᵤ⌉ ((2 * i + 1) * d ^ (2 * i + 1))
def logSeriesUp (a d : Nat) : Nat := ((List.range 8).map (logTermUp a d)).foldr Nat.add 0
def logUpNum (n : Nat) : Nat :=
  let k := log2k n
  let q := 2 ^ k
  let a := n - q
  let d := n + q
  (k * 6931471808) ⌈÷ᵤ⌉ 10000 + logSeriesUp a d +
    (scale * 2 * a ^ 17) ⌈÷ᵤ⌉ (d ^ 15 * (d ^ 2 - a ^ 2))
def countBytes (mask stripe : Nat) : Nat → Nat → Nat
  | 0, total => total
  | j + 1, total =>
    forceNat ((mask >>> j) &&& stripe) fun bit =>
      forceNat (total + bit) (countBytes mask stripe j)
def countCombine (bits half count : Nat) : Nat :=
  let stripe := periodicMask (2 * half) (bits / (2 * half)) * (2 ^ half - 1)
  forceNat stripe fun stripe => (count &&& stripe) + ((count >>> half) &&& stripe)
def countReduce (bits : Nat) : Nat → Nat → Nat → Nat
  | 0, _, total => total
  | fuel + 1, half, total =>
    forceNat (countCombine bits half total) (countReduce bits fuel (2 * half))
def fastCount (depth mask : Nat) : Nat :=
  let bits := 2 ^ (depth + 3)
  forceNat (periodicMask 8 (bits / 8)) fun stripe =>
    forceNat (countBytes mask stripe 8 0) (countReduce bits depth 8)
def bitCount (depth mask : Nat) : Nat :=
  forceNat mask fun value => fastCount depth value
def mask (ds : List (Nat × Nat)) (base top : Nat) : Nat :=
  let len := top - base
  let composite := ds.foldl (fun acc dm =>
    if dm.1 ≤ base then
      acc ||| (dm.2 * 2 ^ ((dm.1 - (base + 1) % dm.1) % dm.1))
    else acc) 0
  (2 ^ len - 1) ^^^ (composite % 2 ^ len)
def word : Nat → Nat → Nat → Nat → Nat → Bool
 | 0,_,base,cand,h => Nat.beq h 0 && Nat.beq (Nat.land base cand) base
 | fuel+1,a,base,cand,h => if h=0 then Nat.beq (Nat.land base cand) base else
   Nat.beq (Nat.mod (Nat.add (Nat.add a 1) (Nat.mod h 64))
     (Nat.add 2 (Nat.mod (Nat.div h 64) 131072))) 0 &&
   forceNat (Nat.lor cand (Nat.shiftLeft 1 (Nat.mod h 64))) fun cn =>
   word fuel a base cn (Nat.div h 8388608)
def payload (h : Nat) : Nat := (h/128)%2^(23*(h%128))
def rest (h : Nat) : Nat := h/2^(7+23*(h%128))
def inner : Nat → Nat → Nat → Nat → Nat → Bool
 | 0,_,_,_,_ => true
 | n+1,a,base,cand,h =>
   forceNat (base%2^64) fun bw =>
   forceNat (cand%2^64) fun cw =>
   forceNat (payload h) fun hw =>
   word 64 a bw cw hw &&
   forceNat (base/2^64) fun bn =>
   forceNat (cand/2^64) fun cn =>
   forceNat (rest h) fun hn =>
   forceNat (a+64) fun an => inner n an bn cn hn
def check : Nat → Nat → Nat → Nat → List Nat → Bool
 | 0,_,_,_,_ => true
 | _+1,_,_,_,[] => false
 | n+1,a,base,cand,h::hs =>
   forceNat (base%2^2048) fun bw =>
   forceNat (cand%2^2048) fun cw =>
   inner 32 a bw cw h &&
   forceNat (base/2^2048) fun bn =>
   forceNat (cand/2^2048) fun cn =>
   forceNat (a+2048) fun an => check n an bn cn hs
def one (groups len depth a u v : Nat) (table : List (Nat×Nat)) (dat : Nat×List Nat) : Bool :=
 check groups a (mask table a (a+len)) dat.1 dat.2 &&
 decide (dat.1<2^len ∧ u+bitCount depth dat.1*logUpNum (a+len)=v ∧
 10000*v≤1000000*(10001*a+1000000000))
def validCheck (len : Nat) (ps : List (Nat×Nat)) : Bool :=
 ps.all (fun dm => decide (2≤dm.1 ∧ dm.2=periodicMask dm.1 ((len+dm.1-1)/dm.1)))
end DusartNumeric
set_option maxRecDepth 200000
set_option maxHeartbeats 0
namespace DusartNumeric
def baseDs : List Nat := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719]
namespace Base8192
def table : List (Nat×Nat) := baseDs.map (fun d => (d,periodicMask d ((8192+d-1)/d)))
theorem valid : validCheck 8192 table=true := by decide +kernel
end Base8192
namespace Base16384
def table : List (Nat×Nat) := baseDs.map (fun d => (d,periodicMask d ((16384+d-1)/d)))
theorem valid : validCheck 16384 table=true := by decide +kernel
end Base16384
namespace Base32768
def table : List (Nat×Nat) := baseDs.map (fun d => (d,periodicMask d ((32768+d-1)/d)))
theorem valid : validCheck 32768 table=true := by decide +kernel
end Base32768
namespace Base65536
def table : List (Nat×Nat) := baseDs.map (fun d => (d,periodicMask d ((65536+d-1)/d)))
theorem valid : validCheck 65536 table=true := by decide +kernel
end Base65536
end DusartNumeric
namespace DusartNumeric
def GenericSpec (a b u v : Nat) : Prop :=
 ∀ (S : Nat → Nat → Nat → Nat → Prop),
 (∀ (groups len depth a u v : Nat) (table : List (Nat×Nat)) (dat : Nat×List Nat),
   validCheck len table=true → 0<len → 131073≤a → a+len<2^64 →
   len≤2048*groups → len≤2^(depth+3) → one groups len depth a u v table dat=true →
   S a (a+len) u v) →
 (∀ {a b c u v w : Nat}, S a b u v → S b c v w → S a c u w) → S a b u v
end DusartNumeric


