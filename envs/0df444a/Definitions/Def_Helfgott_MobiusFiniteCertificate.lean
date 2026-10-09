-- Prove2me | Definitions.Def_Helfgott_MobiusFiniteCertificate
-- name    : Helfgott_MobiusFiniteCertificate
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-08T20:50:25.193337+00:00
-- url     : https://prove2.me/theorems/4b29c7fb-d2db-4d75-987a-58cc8de7d3f4
-- title:
--   Packed arithmetic certificates for finite Mobius sums and integral bounds
-- statement:
--   A finite Möbius certificate stores candidate values $g(n)\in\{-1,0,1\}$ and prime-factor witnesses in blocks of 32. Its arithmetic checks enforce the initial values, certify primes by trial division through 1100, and enforce the square-factor or multiplicative recurrence. A second table stores candidate prefix sums $M(n)$ and integer upper bounds, at a positive scale $Q$, for $\sum_{1\le n<B}|M(n)|/n$. The Boolean checkers and packed data types are defined here. Their soundness and every concrete numerical certificate are separate proof obligations.
-- source:
--   Original finite arithmetic certificate interface toward O. Ramare, From explicit estimates for primes to explicit estimates for the Mobius function, Acta Arithmetica 157 (2013), section 9, Lemma 9.1. https://www.impan.pl/shop/en/publication/transaction/download/product/82991. Uses Mathlib Mobius conventions; supports the finite initial-integral input in the Helfgott minor-arc work. Written by Codex.

import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

set_option autoImplicit false

namespace Helfgott

def mobiusSmallPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097]


def mobiusSmallPrimeCheck (n : ℕ) : Bool :=
  decide (2 ≤ n) && mobiusSmallPrimes.all (fun p =>
    if p * p ≤ n then !(n % p == 0) else true)


def mobiusLocalCheck (g : ℕ → ℤ) (n p : ℕ) : Bool :=
  if n = 0 then g n == 0 else if n = 1 then g n == 1 else
    if p = 0 then mobiusSmallPrimeCheck n && (g n == -1) else
      decide (p ∈ mobiusSmallPrimes) && decide (p < n) && (n % p == 0) &&
        (g n == if (n / p) % p == 0 then 0 else -g (n / p))


inductive MobiusCertTree where
  | leaf (muDigits factorDigits : ℕ)
  | branch (left right : MobiusCertTree)

def mobiusTreeCode : ℕ → MobiusCertTree → ℕ → ℕ
  | 0, .leaf muDigits _, n => (muDigits / 3 ^ (n % 32)) % 3
  | d + 1, .branch l r, n =>
      let span := 32 * 2 ^ d
      if n < span then mobiusTreeCode d l n else mobiusTreeCode d r (n - span)
  | _, _, _ => 0

def mobiusTreeValue (d : ℕ) (tree : MobiusCertTree) (n : ℕ) : ℤ :=
  match mobiusTreeCode d tree n with
  | 0 => 0
  | 1 => 1
  | _ => -1

def mobiusLeafCheck (g : ℕ → ℤ) (B offset factorDigits : ℕ) : Bool :=
  (List.range 32).all (fun k =>
    if offset + k < B then mobiusLocalCheck g (offset + k) ((factorDigits / 2048 ^ k) % 2048)
      else true)

def mobiusTreeCheck (g : ℕ → ℤ) (B : ℕ) : ℕ → ℕ → MobiusCertTree → Bool
  | d, offset, tree =>
    if B ≤ offset then true else
    match d, tree with
    | 0, .leaf _ factorDigits => mobiusLeafCheck g B offset factorDigits
    | d + 1, .branch l r =>
        mobiusTreeCheck g B d offset l && mobiusTreeCheck g B d (offset + 32 * 2 ^ d) r
    | _, _ => false

end Helfgott


set_option autoImplicit false

namespace Helfgott

inductive MobiusHarmonicTree where
  | leaf (prefixDigits upper : ℕ)
  | branch (upper : ℕ) (left right : MobiusHarmonicTree)

def mobiusHarmonicUpper : MobiusHarmonicTree → ℕ
  | .leaf _ upper => upper
  | .branch upper _ _ => upper

def mobiusPrefixCode : ℕ → MobiusHarmonicTree → ℕ → ℕ
  | 0, .leaf digits _, n => (digits / 2048 ^ (n % 32)) % 2048
  | d + 1, .branch _ l r, n =>
      let span := 32 * 2 ^ d
      if n < span then mobiusPrefixCode d l n else mobiusPrefixCode d r (n - span)
  | _, _, _ => 1024

def mobiusPrefixValue (d : ℕ) (tree : MobiusHarmonicTree) (n : ℕ) : ℤ :=
  (mobiusPrefixCode d tree n : ℤ) - 1024

def mobiusHarmonicCeil (Q n : ℕ) (s : ℤ) : ℕ :=
  if n = 0 then 0 else (s.natAbs * Q + n - 1) / n

def mobiusPrefixLocalCheck (g M : ℕ → ℤ) (n : ℕ) : Bool :=
  if n = 0 then M n == g n else M n == M (n - 1) + g n

def mobiusHarmonicLeafCheck (g M : ℕ → ℤ) (Q B offset upper : ℕ) : Bool :=
  (List.range 32).all (fun k =>
      if offset + k < B then mobiusPrefixLocalCheck g M (offset + k) else true) &&
    (((List.range 32).map (fun k =>
      if offset + k < B then mobiusHarmonicCeil Q (offset + k) (M (offset + k))
      else 0)).sum == upper)

def mobiusHarmonicTreeCheck (g M : ℕ → ℤ) (Q B : ℕ) :
    ℕ → ℕ → MobiusHarmonicTree → Bool
  | d, offset, tree =>
    if B ≤ offset then mobiusHarmonicUpper tree == 0 else
    match d, tree with
    | 0, .leaf _ upper => mobiusHarmonicLeafCheck g M Q B offset upper
    | d + 1, .branch upper l r =>
        mobiusHarmonicTreeCheck g M Q B d offset l &&
        mobiusHarmonicTreeCheck g M Q B d (offset + 32 * 2 ^ d) r &&
        (upper == mobiusHarmonicUpper l + mobiusHarmonicUpper r)
    | _, _ => false

end Helfgott


