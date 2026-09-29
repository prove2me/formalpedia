-- Prove2me | Definitions.Def_gilbreath_triangle
-- name    : gilbreath_triangle
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T16:42:39.193239+00:00
-- url     : https://prove2.me/theorems/54d54393-a9a5-4c00-b9f5-108b4f94026c
-- title:
--   The Gilbreath triangle of iterated absolute differences
-- statement:
--   Let $p_0 = 2 < p_1 = 3 < p_2 = 5 < \dots$ be the increasing enumeration of the primes, indexed from $0$. For a sequence $a : \mathbb{N} \to \mathbb{N}$ let $(\Delta a)(n) = |a(n+1) - a(n)|$ be its sequence of absolute differences of consecutive terms, and let $\Delta^k a$ be the $k$-fold iterate of $\Delta$, with $\Delta^0 a = a$.
--
--   The **rows of the Gilbreath triangle** are
--
--   $$ d^k = \Delta^k p, \qquad\text{i.e.}\qquad d^0(n) = p_n, \qquad d^{k+1}(n) = \bigl| d^k(n+1) - d^k(n) \bigr|. $$
--
--   Row $0$ is the sequence of primes, row $1$ is the sequence of prime gaps, and each later row is the sequence of absolute differences of the row above it. Differences are formed in $\mathbb{Z}$ and then taken in absolute value, so no truncated natural subtraction occurs. Alongside the three definitions the file records the structural identities $\Delta^0 a = a$, $\Delta^{k+1} a = \Delta(\Delta^k a)$, $d^0(n) = p_n$, $d^{k+1} = \Delta d^k$, $\Delta^{k+1} a = \Delta^k(\Delta a)$, and $\Delta^j d^k = d^{k+j}$.
-- source:
--   Gilbreath's conjecture. N. L. Gilbreath (1958), as reported in R. B. Killgrove and K. E. Ralston, On a conjecture concerning the primes, MTAC 13 (1959), 121-122, https://doi.org/10.1090/S0025-5718-1959-0105398-3; A. M. Odlyzko, Iterated absolute values of differences of consecutive primes, Math. Comp. 61 (1993), 373-380, https://doi.org/10.1090/S0025-5718-1993-1192979-9; https://en.wikipedia.org/wiki/Gilbreath%27s_conjecture

import Mathlib

namespace Gilbreath

/-- One step of the Gilbreath triangle: the sequence of absolute differences of
consecutive terms of `a`, i.e. `absDiff a n = |a (n + 1) - a n|`. -/
def absDiff (a : ℕ → ℕ) : ℕ → ℕ := fun n => Int.natAbs ((a (n + 1) : ℤ) - (a n : ℤ))

/-- `iterAbsDiff a k` is the `k`-th iterated absolute-difference row of `a`:
row `0` is `a` itself and each subsequent row is `absDiff` of the previous one. -/
def iterAbsDiff (a : ℕ → ℕ) : ℕ → (ℕ → ℕ)
  | 0 => a
  | k + 1 => absDiff (iterAbsDiff a k)

/-- Row `k` of Gilbreath's triangle. Row `0` is the increasing sequence of all
primes, `d 0 n = Nat.nth Nat.Prime n` (so `d 0 0 = 2`, `d 0 1 = 3`, ...), and
row `k + 1` is the sequence of absolute differences of consecutive entries of
row `k`. -/
noncomputable def d (k : ℕ) : ℕ → ℕ := iterAbsDiff (fun n => Nat.nth Nat.Prime n) k

@[simp] theorem iterAbsDiff_zero (a : ℕ → ℕ) : iterAbsDiff a 0 = a := rfl

@[simp] theorem iterAbsDiff_succ (a : ℕ → ℕ) (k : ℕ) :
    iterAbsDiff a (k + 1) = absDiff (iterAbsDiff a k) := rfl

@[simp] theorem d_zero_apply (n : ℕ) : d 0 n = Nat.nth Nat.Prime n := rfl

@[simp] theorem d_succ (k : ℕ) : d (k + 1) = absDiff (d k) := rfl

theorem d_succ_apply (k n : ℕ) : d (k + 1) n = Int.natAbs ((d k (n + 1) : ℤ) - (d k n : ℤ)) :=
  rfl

/-- Peeling one difference off the front instead of the back. -/
theorem iterAbsDiff_succ' (a : ℕ → ℕ) (k : ℕ) :
    iterAbsDiff a (k + 1) = iterAbsDiff (absDiff a) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterAbsDiff_succ (k := k + 1), ih, iterAbsDiff_succ]

/-- Iterating the difference operator starting from row `k` lands on row `k + j`. -/
theorem iterAbsDiff_d (k j : ℕ) : iterAbsDiff (d k) j = d (k + j) := by
  induction j with
  | zero => simp
  | succ j ih => rw [iterAbsDiff_succ, ih, ← Nat.add_assoc, d_succ]

end Gilbreath


