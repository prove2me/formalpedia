-- Prove2me | Definitions.Def_NumberTheory_DedekindSum
-- name    : NumberTheory_DedekindSum
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/cbe82989-1be4-5e90-8796-622b4d67f6c4
-- title:
--   Dedekind sums and the rational sawtooth function
-- statement:
--   Two root-level definitions over $\mathbb{Q}$ are made here. First, [`dedekindSaw : ℚ → ℚ`](../def/NumberTheory_DedekindSum.html#L11) is the sawtooth function $((x))$: it is $0$ when `Int.fract x = 0`, that is when $x$ is an integer, and $\operatorname{fract}(x) - \tfrac12 = x - \lfloor x\rfloor - \tfrac12$ otherwise. The accompanying lemmas record the basic properties in this spelling: the two unfolding rules according to whether the fractional part vanishes; vanishing at integer and natural-number arguments and in particular at $0$ and $1$; vanishing at $1/2$; invariance under translation by an integer or a natural number, on either side; oddness, $((-x)) = -((x))$; the strict bound $|((x))| < \tfrac12$ (note that this holds also at integers, where the value is $0$); and the evaluation $((r/k)) = r/k - \tfrac12$ for natural numbers $0 < r < k$.
--
--   Second, [`dedekindSum h k`](../def/NumberTheory_DedekindSum.html#L73) is defined for $h \in \mathbb{Z}$ and $k \in \mathbb{N}$ as the finite sum
--   $$s(h,k) = \sum_{r=0}^{k-1} \left(\!\left(\frac{r}{k}\right)\!\right)\left(\!\left(\frac{hr}{k}\right)\!\right),$$
--   the index $r$ running over `Finset.range k`. No coprimality condition on $h$ and $k$ is built into the definition, the first argument is an arbitrary integer, and $k = 0$ gives the empty sum. The lemmas proved here are the elementary ones: $s(h,0) = 0$, $s(h,1) = 0$ and $s(0,k) = 0$; oddness in the first argument, $s(-h,k) = -s(h,k)$; periodicity $s(h + mk, k) = s(h,k)$ for every $m \in \mathbb{Z}$; and the normal form
--   $$s(h,k) = \sum_{r=1}^{k-1}\left(\frac{r}{k} - \frac12\right)\left(\!\left(\frac{hr}{k}\right)\!\right),$$
--   in which the vanishing $r = 0$ term has been dropped and the first sawtooth factor evaluated. Everything is purely algebraic over $\mathbb{Q}$; no analysis enters.
--
--   **Relation to Mathlib.** Mathlib has no sawtooth function or Dedekind sums; these are the project's own definitions, phrased in terms of Mathlib's `Int.fract` on $\mathbb{Q}$.
--
--   **Where it is used.** This module provides the definitions on which the further properties of Dedekind sums proved in the modules importing it rest — the reciprocity law for coprime positive arguments, the integrality of $6k\,s(h,k)$, the closed form for $s(1,k)$, and invariance under replacing $h$ by an inverse modulo $k$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberTheory_DedekindSum.lean

import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

def dedekindSaw (x : ℚ) : ℚ :=
  if Int.fract x = 0 then 0 else Int.fract x - 1 / 2

theorem dedekindSaw_of_fract_eq_zero {x : ℚ} (h : Int.fract x = 0) : dedekindSaw x = 0 :=
  if_pos h

theorem dedekindSaw_of_fract_ne_zero {x : ℚ} (h : Int.fract x ≠ 0) :
    dedekindSaw x = Int.fract x - 1 / 2 :=
  if_neg h

theorem dedekindSaw_intCast (n : ℤ) : dedekindSaw (n : ℚ) = 0 :=
  dedekindSaw_of_fract_eq_zero (Int.fract_intCast n)

theorem dedekindSaw_natCast (n : ℕ) : dedekindSaw (n : ℚ) = 0 := by
  rw [← Int.cast_natCast]; exact dedekindSaw_intCast (n : ℤ)

theorem dedekindSaw_zero : dedekindSaw 0 = 0 := by
  rw [← Int.cast_zero]; exact dedekindSaw_intCast 0

theorem dedekindSaw_one : dedekindSaw 1 = 0 := by
  rw [← Int.cast_one]; exact dedekindSaw_intCast 1

theorem dedekindSaw_add_intCast (x : ℚ) (n : ℤ) : dedekindSaw (x + n) = dedekindSaw x := by
  unfold dedekindSaw
  rw [Int.fract_add_intCast]

theorem dedekindSaw_intCast_add (n : ℤ) (x : ℚ) : dedekindSaw ((n : ℚ) + x) = dedekindSaw x := by
  rw [add_comm, dedekindSaw_add_intCast]

theorem dedekindSaw_add_natCast (x : ℚ) (n : ℕ) : dedekindSaw (x + n) = dedekindSaw x := by
  rw [← Int.cast_natCast]; exact dedekindSaw_add_intCast x (n : ℤ)

theorem dedekindSaw_neg (x : ℚ) : dedekindSaw (-x) = -dedekindSaw x := by
  unfold dedekindSaw
  by_cases h : Int.fract x = 0
  · rw [if_pos h, if_pos (Int.fract_neg_eq_zero.2 h), neg_zero]
  · rw [if_neg h, if_neg fun h' => h (Int.fract_neg_eq_zero.1 h'), Int.fract_neg h]
    ring

theorem abs_dedekindSaw_lt_half (x : ℚ) : |dedekindSaw x| < 1 / 2 := by
  unfold dedekindSaw
  by_cases h : Int.fract x = 0
  · rw [if_pos h, abs_zero]
    exact one_half_pos
  · have h0 : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm h)
    have h1 : Int.fract x < 1 := Int.fract_lt_one x
    rw [if_neg h, abs_lt]
    constructor <;> linarith

theorem dedekindSaw_half : dedekindSaw (1 / 2) = 0 := by
  have hfr : Int.fract (1 / 2 : ℚ) = 1 / 2 :=
    Int.fract_eq_self.2 ⟨one_half_pos.le, one_half_lt_one⟩
  rw [dedekindSaw_of_fract_ne_zero (by rw [hfr]; exact one_half_pos.ne'), hfr, sub_self]

theorem dedekindSaw_natCast_div {r k : ℕ} (h0 : 0 < r) (hrk : r < k) :
    dedekindSaw ((r : ℚ) / k) = (r : ℚ) / k - 1 / 2 := by
  have hk : (0 : ℚ) < k := by exact_mod_cast h0.trans hrk
  have hpos : (0 : ℚ) < (r : ℚ) / k := div_pos (by exact_mod_cast h0) hk
  have hlt : (r : ℚ) / k < 1 := (div_lt_one hk).2 (by exact_mod_cast hrk)
  have hfr : Int.fract ((r : ℚ) / k) = (r : ℚ) / k := Int.fract_eq_self.2 ⟨hpos.le, hlt⟩
  rw [dedekindSaw_of_fract_ne_zero (by rw [hfr]; exact hpos.ne'), hfr]

def dedekindSum (h : ℤ) (k : ℕ) : ℚ :=
  ∑ r ∈ Finset.range k, dedekindSaw ((r : ℚ) / k) * dedekindSaw ((h : ℚ) * r / k)

theorem dedekindSum_zero_right (h : ℤ) : dedekindSum h 0 = 0 := by
  simp [dedekindSum]

theorem dedekindSum_one_right (h : ℤ) : dedekindSum h 1 = 0 := by
  simp [dedekindSum, dedekindSaw_zero]

theorem dedekindSum_zero_left (k : ℕ) : dedekindSum 0 k = 0 := by
  simp [dedekindSum, dedekindSaw_zero]

theorem dedekindSum_neg (h : ℤ) (k : ℕ) : dedekindSum (-h) k = -dedekindSum h k := by
  unfold dedekindSum
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Int.cast_neg, neg_mul, neg_div, dedekindSaw_neg]
  ring

theorem dedekindSum_add_mul (h m : ℤ) (k : ℕ) : dedekindSum (h + m * k) k = dedekindSum h k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [dedekindSum_zero_right, dedekindSum_zero_right]
  unfold dedekindSum
  refine Finset.sum_congr rfl fun r _ => ?_
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have key : ((h + m * k : ℤ) : ℚ) * r / k = (h : ℚ) * r / k + ((m * r : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [key, dedekindSaw_add_intCast]

theorem dedekindSum_eq_sum_Ico (h : ℤ) (k : ℕ) :
    dedekindSum h k =
      ∑ r ∈ Finset.Ico 1 k, ((r : ℚ) / k - 1 / 2) * dedekindSaw ((h : ℚ) * r / k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [dedekindSum_zero_right]
    simp
  unfold dedekindSum
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hk, zero_add]
  simp only [Nat.cast_zero, zero_div, dedekindSaw_zero, zero_mul, zero_add]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hr
  rw [dedekindSaw_natCast_div h1 h2]


