-- Prove2me | Definitions.Def_MIPRE_Foundations_Halting_Absorb
-- name    : MIPRE_Foundations_Halting_Absorb
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:48:06.8705+00:00
-- url     : https://prove2.me/theorems/09534cd3-5434-44e5-a88a-e53aea78ae4c
-- title:
--   Absorbing polynomially bounded costs into $m^n$ and polynomials in $\log n$ into $n$
-- statement:
--   This bundle holds the two absorption lemmas that the boundedness accounting of the compressor's output (`MIPRE.Foundations.Halting.CompressorCost`) and of the paper-route verifier (`MIPRE.Foundations.Halting.Paper.Cost`) rest on, with two auxiliary facts. A function $F : \mathbb{N} \to \mathbb{N}$ is *polynomially bounded* (`MIPRE.Cost.PolyBounded F`) when $F(n) \le P(n)$ for all $n$, for some polynomial $P \in \mathbb{N}[X]$; $\mathrm{size}\,n$ is Mathlib's `Nat.size`, the number of binary digits of $n$.
--
--   `MIPRE.Cost.size_le_log_add_one`: $\mathrm{size}\,n \le \log_2 n + 1$ for every $n$ (with `Nat.log 2`).
--
--   `MIPRE.Cost.PolyBounded.two_pow_size`: for all $K, D$, the function $n \mapsto 2^{K + D\cdot \mathrm{size}\,n}$ is polynomially bounded.
--
--   `MIPRE.Cost.PolyBounded.absorb` (absorption into $m^n$): if $F$ is polynomially bounded, there is a threshold $n_0$ such that for all $n \ge n_0$, all $m \ge 2$ and all $y \ge 1$,
--   $$F\big((m + n + 1)\,y\big) \le m^n \cdot y^n .$$
--
--   `MIPRE.Cost.PolyBounded.absorb_log`: if $g$ is polynomially bounded and $a, b \in \mathbb{N}$, there is $n_0$ such that $2\,g(a + b\cdot\mathrm{size}\,n) \le n$ for all $n \ge n_0$.
--
--   The first absorption is how a running time of the form $\mathrm{poly}(\text{index}, \text{level}, \text{input size})$ is put under the $m^n (|d|+1)^n$ that `Verifier.IsBounded n` asks for at index $m$: each atom is replaced by the largest, $(m + n + 1)y$. The second is how a description of size polynomial in $\log n$ fits in the half of $n$ that the slack of the compressibility criterion leaves. Both are coarser forms of the parameter inequality of blueprint `lem:lambda-bound`.
--
--   **Formalization Note**. The bundle contains no definition; `PolyBounded` is the predicate `∃ P : Polynomial ℕ, ∀ n, f n ≤ P.eval n` of `MIPRE.Foundations.Halting.PolyBounded`. The thresholds are existential and depend on the polynomial alone (`absorb`), respectively on `g`, `a`, `b` (`absorb_log`); the statements are `∃ n₀, ∀ n, n₀ ≤ n → ∀ m, 2 ≤ m → ∀ y, 1 ≤ y → F ((m + n + 1) * y) ≤ m ^ n * y ^ n` and `∃ n₀, ∀ n, n₀ ≤ n → 2 * g (a + b * Nat.size n) ≤ n`. Both are stated for arbitrary `F`, `g : ℕ → ℕ`, not for polynomials, so a cost assembled from several polynomially bounded pieces qualifies without being written as one polynomial.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Absorb.lean; blueprint lem:lambda

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Absorb.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_PolyBounded
import Definitions.Def_MIPRE_Foundations_Halting_LambdaBound

/-!
# Absorbing polynomial costs into `n ^ λ`

The two arithmetic facts the accounting of the compressor's output rests on. Its verifier at
level `n` has to be `n`-bounded (`Verifier.IsBounded n`): running times at every index `m ≥ 2`
at most `m ^ n · (|d| + 1) ^ n`, and a description of size at most `n`. What the construction
supplies is a running time polynomial in the index, the level and the input size, and a
description of size polynomial in `log n` plus the half of `n` the criterion's slack leaves.
Both are absorbed once `n` is past a threshold depending only on the polynomials:

* `PolyBounded.absorb`: for `F` polynomially bounded, `F ((m + n + 1) · y) ≤ m ^ n · y ^ n` for
  all `m ≥ 2`, `y ≥ 1` and `n` past a threshold. The argument `(m + n + 1) · y` is what every
  cost is bounded by once each of its atoms — the index, the level, the input size — is replaced
  by the largest.
* `PolyBounded.absorb_log`: for `g` polynomially bounded, `2 · g (a + b · size n) ≤ n` for `n`
  past a threshold: a polynomial in the length of `n` is eventually half of `n`.

Both are the parameter inequality of `lem:lambda-bound` in a coarser form; `log_lt_div` from its
proof is the step with content.
-/

namespace MIPRE.Cost

open Polynomial

/-- `size n ≤ log₂ n + 1`. -/
theorem size_le_log_add_one (n : ℕ) : Nat.size n ≤ Nat.log 2 n + 1 :=
  Nat.size_le.2 (Nat.lt_pow_succ_log_self one_lt_two n)

/-- `2 ^ (K + D · size n)` is polynomially bounded in `n`. -/
theorem PolyBounded.two_pow_size (K D : ℕ) : PolyBounded fun n => 2 ^ (K + D * Nat.size n) := by
  refine ((PolyBounded.const (2 ^ K)).mul
    (((PolyBounded.id.const_mul 2).add_const 1).pow D)).mono fun n => ?_
  rw [pow_add, pow_mul']
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (two_pow_size_le n) D)

/-- **Absorption into `m ^ n`.** A polynomially bounded function of `(m + n + 1) · y` is below
`m ^ n · y ^ n` for every index `m ≥ 2` and every `y ≥ 1`, once the level `n` is past a threshold
depending on the polynomial alone. -/
theorem PolyBounded.absorb {F : ℕ → ℕ} (hF : PolyBounded F) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∀ m, 2 ≤ m → ∀ y, 1 ≤ y → F ((m + n + 1) * y) ≤ m ^ n * y ^ n := by
  obtain ⟨P, hP⟩ := hF
  set A := ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i with hA
  set k := P.natDegree with hk
  -- the threshold: past it, `A + k + k · size n ≤ n`
  set C := k + 1 with hC
  refine ⟨max (4 * C * (8 * C + 4)) (2 * (A + 2 * k)), fun n hn m hm y hy => ?_⟩
  have hn1 : 4 * C * (8 * C + 4) ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : 2 * (A + 2 * k) ≤ n := le_trans (le_max_right _ _) hn
  have hexp : A + k + k * Nat.size n ≤ n := by
    have hlog := Halting.log_lt_div (C := C) (by omega) hn1
    have hsz := size_le_log_add_one n
    have hdiv : 4 * (C * (n / (4 * C))) ≤ n := by
      have := Nat.mul_div_le n (4 * C); rw [Nat.mul_assoc] at this; exact this
    have h1 : k * Nat.size n ≤ k * (n / (4 * C)) + k :=
      by nlinarith [Nat.mul_le_mul_left k hsz]
    have h2 : k * (n / (4 * C)) ≤ C * (n / (4 * C)) := Nat.mul_le_mul_right _ (by omega)
    omega
  -- the bound
  have hz : 1 ≤ (m + n + 1) * y := Nat.one_le_iff_ne_zero.2 (by positivity)
  have h1 : F ((m + n + 1) * y) ≤ A * ((m + n + 1) * y) ^ k :=
    (hP _).trans (polynomial_eval_le_sum_coeff_mul_pow P hz)
  have h2 : m + n + 1 ≤ m * (n + 1) := by nlinarith
  have h3 : n + 1 ≤ 2 ^ Nat.size n := Nat.lt_size_self n
  have h4 : (m + n + 1) ^ k ≤ m ^ k * (2 ^ Nat.size n) ^ k := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (h2.trans (Nat.mul_le_mul_left _ h3)) k
  have h5 : A ≤ 2 ^ A := Nat.lt_two_pow_self.le
  have h6 : (2 : ℕ) ^ A ≤ m ^ A := Nat.pow_le_pow_left hm A
  have h7 : (2 ^ Nat.size n) ^ k ≤ m ^ (Nat.size n * k) := by
    rw [← pow_mul]; exact Nat.pow_le_pow_left hm _
  have h8 : y ^ k ≤ y ^ n := Nat.pow_le_pow_right hy (by omega)
  calc F ((m + n + 1) * y) ≤ A * ((m + n + 1) * y) ^ k := h1
    _ = A * (m + n + 1) ^ k * y ^ k := by rw [mul_pow, mul_assoc]
    _ ≤ m ^ A * (m ^ k * m ^ (Nat.size n * k)) * y ^ n := by
        gcongr
        · exact h5.trans h6
        · exact h4.trans (Nat.mul_le_mul_left _ h7)
    _ = m ^ (A + k + Nat.size n * k) * y ^ n := by rw [← pow_add, ← pow_add, Nat.add_assoc]
    _ ≤ m ^ n * y ^ n := by
        gcongr
        · omega
        · rw [Nat.mul_comm] at hexp; exact hexp

/-- **A polynomial in the length of `n` is eventually half of `n`.** -/
theorem PolyBounded.absorb_log {g : ℕ → ℕ} (hg : PolyBounded g) (a b : ℕ) :
    ∃ n₀, ∀ n, n₀ ≤ n → 2 * g (a + b * Nat.size n) ≤ n := by
  have hf : PolyBounded fun s => 4 * g (a + b * s) :=
    (hg.comp (((PolyBounded.id.const_mul b).add_const a).mono fun s => by omega)).const_mul 4
  obtain ⟨s₀, hs₀⟩ := hf.exists_le_two_pow
  refine ⟨2 ^ s₀, fun n hn => ?_⟩
  have h1 : s₀ ≤ Nat.size n := (Nat.lt_size.2 hn).le.trans (by omega)
  have h2 := hs₀ (Nat.size n) h1
  have h3 := two_pow_size_le n
  omega

end MIPRE.Cost


