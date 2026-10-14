-- Prove2me | Definitions.Def_BooneHigman_TMonoid
-- name    : BooneHigman_TMonoid
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-14T09:16:16.637832+00:00
-- url     : https://prove2.me/theorems/415d3056-7652-43e7-95c3-810a5780c900
-- title:
--   The monoid $T = (K \setminus \{\Omega\}) \times P \sqcup \{0_T\}$
-- statement:
--   For a monoid $K$ with a zero element $\Omega
--   eq 1_K$ (modeled by `[MonoidWithZero K] [Nontrivial K]`, taking $\Omega := 0$), the monoid `TElem K` representing $T = (K \setminus \{\Omega\}) 	imes P \sqcup \{0_T\}$, where $P$ is the monoid of Lemma 6.1 (`PElem`, `Definitions.Def_BooneHigman_PMonoid`). The absorbing element `0_T` is the `zero` constructor; nonzero pairs multiply coordinatewise, except that a product whose $K$-coordinate is $\Omega$ collapses to `0_T`. Its identity is $(1_K, 1_P)$. This is exactly the monoid $T$ used in the statement of Theorem 6.2.
-- source:
--   OpenAI, "Finite algebraic envelopes and the Boone-Higman conjecture", OpenAI Math Release, 2026-09-23, Section 6.1, the paragraph immediately preceding Theorem 6.2 ('For a monoid K with zero Omega != 1_K, write T = (K \ {Omega}) x P + {0_T}...').

import Mathlib
import Definitions.Def_BooneHigman_PMonoid


/-!
The monoid `T = (K \ {Ω}) × P ⊔ {0_T}` from OpenAI's "Finite algebraic envelopes and the
Boone-Higman conjecture" preprint, Section 6.1 (just before Theorem 6.2), for a monoid `K`
with zero `Ω ≠ 1_K` (realized here as `[MonoidWithZero K] [Nontrivial K]`, so `Ω := (0 : K)`)
and the monoid `P` of partial affine maps (`PElem`, Lemma 6.1). Nonzero pairs multiply
coordinatewise, except that a product whose `K`-coordinate is `Ω` is replaced by `0_T`.
-/

namespace OAI
namespace FiniteAlgebraicEnvelopes

/-- `T = (K \ {0}) × P ⊔ {0_T}`, for a monoid `K` with zero. -/
inductive TElem (K : Type*) [MonoidWithZero K] where
  | pair (k : K) (hk : k ≠ 0) (p : PElem)
  | zero

namespace TElem

variable {K : Type*} [MonoidWithZero K] [DecidableEq K]

noncomputable def mul : TElem K → TElem K → TElem K
  | zero, _ => zero
  | _, zero => zero
  | pair k1 _ p1, pair k2 _ p2 =>
      if h : k1 * k2 = 0 then zero else pair (k1 * k2) h (p1 * p2)

noncomputable instance : Mul (TElem K) := ⟨mul⟩

theorem mul_zero_left (y : TElem K) : (zero : TElem K) * y = zero := rfl

theorem mul_zero_right (x : TElem K) : x * (zero : TElem K) = zero := by
  cases x <;> rfl

theorem pair_mul_pair (k1 k2 : K) (h1 : k1 ≠ 0) (h2 : k2 ≠ 0) (p1 p2 : PElem) :
    pair k1 h1 p1 * pair k2 h2 p2 =
      if h : k1 * k2 = 0 then zero else pair (k1 * k2) h (p1 * p2) := rfl

variable [Nontrivial K]

noncomputable instance : One (TElem K) := ⟨pair 1 one_ne_zero 1⟩

theorem one_def : (1 : TElem K) = pair 1 one_ne_zero 1 := rfl

theorem one_mul (x : TElem K) : 1 * x = x := by
  cases x with
  | zero => rfl
  | pair k hk p =>
    rw [one_def, pair_mul_pair]
    split_ifs with h
    · rw [_root_.one_mul] at h; exact absurd h hk
    · congr 1 <;> simp

theorem mul_one (x : TElem K) : x * 1 = x := by
  cases x with
  | zero => rfl
  | pair k hk p =>
    rw [one_def, pair_mul_pair]
    split_ifs with h
    · rw [_root_.mul_one] at h; exact absurd h hk
    · congr 1 <;> simp

theorem mul_assoc (x y z : TElem K) : x * y * z = x * (y * z) := by
  cases x with
  | zero => simp [mul_zero_left]
  | pair k1 h1 p1 =>
  cases y with
  | zero => simp [mul_zero_left, mul_zero_right]
  | pair k2 h2 p2 =>
  cases z with
  | zero => simp [mul_zero_right]
  | pair k3 h3 p3 =>
    have hassoc : k1 * k2 * k3 = k1 * (k2 * k3) := _root_.mul_assoc k1 k2 k3
    rw [pair_mul_pair k1 k2 h1 h2 p1 p2]
    by_cases h12 : k1 * k2 = 0
    · rw [dif_pos h12, mul_zero_left]
      have h123 : k1 * (k2 * k3) = 0 := by rw [← hassoc, h12, zero_mul]
      by_cases h23 : k2 * k3 = 0
      · rw [pair_mul_pair k2 k3 h2 h3 p2 p3, dif_pos h23, mul_zero_right]
      · rw [pair_mul_pair k2 k3 h2 h3 p2 p3, dif_neg h23,
          pair_mul_pair k1 (k2 * k3) h1 h23 p1 (p2 * p3), dif_pos h123]
    · rw [dif_neg h12]
      by_cases h23 : k2 * k3 = 0
      · have h12_3 : k1 * k2 * k3 = 0 := by rw [hassoc, h23, mul_zero]
        rw [pair_mul_pair (k1 * k2) k3 h12 h3 (p1 * p2) p3, dif_pos h12_3,
          pair_mul_pair k2 k3 h2 h3 p2 p3, dif_pos h23, mul_zero_right]
      · by_cases h123 : k1 * k2 * k3 = 0
        · rw [pair_mul_pair (k1 * k2) k3 h12 h3 (p1 * p2) p3, dif_pos h123,
            pair_mul_pair k2 k3 h2 h3 p2 p3, dif_neg h23,
            pair_mul_pair k1 (k2 * k3) h1 h23 p1 (p2 * p3), dif_pos (hassoc ▸ h123)]
        · rw [pair_mul_pair (k1 * k2) k3 h12 h3 (p1 * p2) p3, dif_neg h123,
            pair_mul_pair k2 k3 h2 h3 p2 p3, dif_neg h23,
            pair_mul_pair k1 (k2 * k3) h1 h23 p1 (p2 * p3), dif_neg (hassoc ▸ h123)]
          congr 1
          exact PElem.mul_assoc p1 p2 p3

noncomputable instance : Monoid (TElem K) where
  mul := (· * ·)
  one := 1
  mul_assoc := mul_assoc
  one_mul := one_mul
  mul_one := mul_one

end TElem
end FiniteAlgebraicEnvelopes
end OAI


