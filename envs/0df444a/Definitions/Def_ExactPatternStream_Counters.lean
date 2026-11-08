-- Prove2me | Definitions.Def_ExactPatternStream_Counters
-- name    : ExactPatternStream_Counters
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:02:17.535293+00:00
-- url     : https://prove2.me/theorems/6e4cb6fd-08e3-4157-a059-42f66f5444fb
-- title:
--   §7.2 and the proof of Lemma 7.5 — precision-$k$ counters, $\mathrm{round}_k$, $\mathrm{val}$, $\mathrm{Sum}_k$
-- statement:
--   A precision-$k$ counter is a pair $z=(M,s)$ of nonnegative integers with $M<2^{k+1}$ and $s=0$ whenever $M<2^k$; its value is $\mathrm{val}(z)=M2^s$. Rounding is $\mathrm{round}_k(0)=(0,0)$ and $\mathrm{round}_k(x)=(\lfloor x/2^s\rfloor,s)$, $s=\max\{0,\lfloor\log_2x\rfloor-k\}$. $\mathrm{Sum}_k$ pads with zeros to the next power of two and merges equal-height counters $u,v$ into $\mathrm{round}_k(\mathrm{val}(u)+\mathrm{val}(v))$.
--
--   These counters track node weights in $O(\log\log m)$ bits.
--
--   **Formalization Note** `Nat.log 2 x` is $\lfloor\log_2x\rfloor$ and truncated subtraction is the $\max$. `sumK` merges level by level, the same tree as the left-to-right binary merge stack of the proof.
-- source:
--   Gawrychowski, Janczewski, Jin, Nelson, An Improved Streaming Algorithm for Exact Pattern Matching (preprint, STOC 2027 submission, sha256 351218cb…), §7.2, pp.19–20 (PDF 20–21), proof of Lemma 7.5

import Mathlib

namespace ExactPatternStream

/-! # Approximate counting

Gawrychowski, Janczewski, Jin, Nelson (preprint, sha256 351218cb…), §7.2, pp.19–20 (PDF 20–21), and the
proof of Lemma 7.5.

**Formalization Note.** A counter is a pair `(M, s)`. `Nat.log 2 x = ⌊log₂ x⌋`, and the natural-number
subtraction is `max{0, ⌊log₂ x⌋ - k}`. `Sum_k` is defined as in the proof of Lemma 7.5: pad with zero
counters to the next power of two, then merge adjacent counters into `round_k(val u + val v)`, one height at
a time. A binary merge stack computes the same tree of merges left to right. -/

/-- `z = (M, s)` is a precision-`k` counter: `M < 2^{k+1}`, and `s = 0` whenever `M < 2^k`. -/
def IsCounter (k : ℕ) (z : ℕ × ℕ) : Prop := z.1 < 2 ^ (k + 1) ∧ (z.1 < 2 ^ k → z.2 = 0)

/-- `val(z) = M 2^s`. -/
def val (z : ℕ × ℕ) : ℕ := z.1 * 2 ^ z.2

/-- `round_k(0) = (0, 0)` and `round_k(x) = (⌊x/2^s⌋, s)`, `s = max{0, ⌊log₂ x⌋ - k}`, for `x > 0`. -/
def roundK (k x : ℕ) : ℕ × ℕ :=
  if x = 0 then (0, 0) else (x / 2 ^ (Nat.log 2 x - k), Nat.log 2 x - k)

/-- Merge adjacent counters into `round_k(val u + val v)`. -/
def mergePairs (k : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | u :: v :: rest => roundK k (val u + val v) :: mergePairs k rest
  | zs => zs

/-- `Sum_k(z_1, …, z_r)`: `⌈log₂ r⌉` rounds of merging after padding with zeros to length `2^{⌈log₂ r⌉}`. -/
def sumK (k : ℕ) (zs : List (ℕ × ℕ)) : ℕ × ℕ :=
  let t := Nat.clog 2 zs.length
  let padded := zs ++ List.replicate (2 ^ t - zs.length) (0, 0)
  ((mergePairs k)^[t] padded).headD (0, 0)

end ExactPatternStream


