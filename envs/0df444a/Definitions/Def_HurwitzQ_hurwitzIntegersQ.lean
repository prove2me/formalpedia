-- Prove2me | Definitions.Def_HurwitzQ_hurwitzIntegersQ
-- name    : HurwitzQ_hurwitzIntegersQ
-- status  : Definition
-- author  : @jawneeboy
-- created : 2026-09-18T17:59:36.934837+00:00
-- url     : https://prove2.me/theorems/80a1a5d7-fec5-436b-b0df-f3973d2cee8e
-- title:
--   Hurwitz integers over the rationals
-- statement:
--   Let $\mathcal{H}$ be the Hurwitz subring of the rational quaternions: the four coordinates of an element are either all in $\mathbb{Z}$ or all in $\mathbb{Z}+\frac12$. In coordinates, $$\mathcal{H}=\mathbb{Z}^4\cup(\mathbb{Z}+\tfrac12)^4.$$ The formalization equips this set with its subring structure.
-- source:
--   Standard definition: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003, §5.1, The Hurwitz Integral Quaternions. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345

import Mathlib.Algebra.Quaternion
import Mathlib.Tactic.Ring

/-!
# Hurwitz integers over the rationals

The Hurwitz ring $\mathcal{H}$ consists of quaternions $a+bi+cj+dk$ with
either $a,b,c,d\in\mathbb{Z}$ or $a,b,c,d\in\mathbb{Z}+\frac12$.
It is realized here as a subring of the rational quaternions.

The coordinate predicates expose the two membership branches. The subring
structure supplies the ring operations and their closure properties. Subsequent
files establish the generator characterization, conjugation closure, integrality
of the squared norm, and comparison with the real model.

Reference: John H. Conway and Derek A. Smith, *On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry*, A K Peters, 2003, §5.1, "The Hurwitz Integral Quaternions".
-/

open Quaternion

namespace HurwitzQ

/-- The predicate: all four coordinates of `q : ℍ[ℚ]` are integers. -/
def allIntCoordsQ (q : ℍ[ℚ]) : Prop :=
  ∃ a b c d : ℤ, q.re = ↑a ∧ q.imI = ↑b ∧ q.imJ = ↑c ∧ q.imK = ↑d

/-- The predicate: all four coordinates of `q : ℍ[ℚ]` lie in `ℤ + 1/2`. -/
def allHalfIntCoordsQ (q : ℍ[ℚ]) : Prop :=
  ∃ a b c d : ℤ, q.re = ↑a + 1/2 ∧ q.imI = ↑b + 1/2 ∧ q.imJ = ↑c + 1/2 ∧ q.imK = ↑d + 1/2

/-- The Hurwitz integers as a subring of `ℍ[ℚ]`: the quaternions `a + b*i + c*j + d*k`
whose coordinates either all lie in `ℤ` or all lie in `ℤ + 1/2`. -/
def hurwitzIntegersQ : Subring ℍ[ℚ] where
  carrier := { q | allIntCoordsQ q ∨ allHalfIntCoordsQ q }
  one_mem' := .inl ⟨1, 0, 0, 0, by simp⟩
  zero_mem' := .inl ⟨0, 0, 0, 0, by simp⟩
  add_mem' := by
    rintro q p (⟨a, b, c, d, hqa, hqi, hqj, hqk⟩ | ⟨a, b, c, d, hqa, hqi, hqj, hqk⟩)
      (⟨a', b', c', d', hpa, hpi, hpj, hpk⟩ | ⟨a', b', c', d', hpa, hpi, hpj, hpk⟩)
    · refine .inl ⟨a + a', b + b', c + c', d + d', ?_, ?_, ?_, ?_⟩ <;>
        simp only [re_add, imI_add, imJ_add, imK_add, hqa, hqi, hqj, hqk, hpa, hpi, hpj, hpk] <;>
        push_cast <;> ring
    · refine .inr ⟨a + a', b + b', c + c', d + d', ?_, ?_, ?_, ?_⟩ <;>
        simp only [re_add, imI_add, imJ_add, imK_add, hqa, hqi, hqj, hqk, hpa, hpi, hpj, hpk] <;>
        push_cast <;> ring
    · refine .inr ⟨a + a', b + b', c + c', d + d', ?_, ?_, ?_, ?_⟩ <;>
        simp only [re_add, imI_add, imJ_add, imK_add, hqa, hqi, hqj, hqk, hpa, hpi, hpj, hpk] <;>
        push_cast <;> ring
    · refine .inl ⟨a + a' + 1, b + b' + 1, c + c' + 1, d + d' + 1, ?_, ?_, ?_, ?_⟩ <;>
        simp only [re_add, imI_add, imJ_add, imK_add, hqa, hqi, hqj, hqk, hpa, hpi, hpj, hpk] <;>
        push_cast <;> ring
  neg_mem' := by
    rintro q (⟨a, b, c, d, hqa, hqi, hqj, hqk⟩ | ⟨a, b, c, d, hqa, hqi, hqj, hqk⟩)
    · refine .inl ⟨-a, -b, -c, -d, ?_, ?_, ?_, ?_⟩ <;>
        simp only [re_neg, imI_neg, imJ_neg, imK_neg, hqa, hqi, hqj, hqk] <;>
        push_cast <;> ring
    · refine .inr ⟨-a - 1, -b - 1, -c - 1, -d - 1, ?_, ?_, ?_, ?_⟩ <;>
        simp only [re_neg, imI_neg, imJ_neg, imK_neg, hqa, hqi, hqj, hqk] <;>
        push_cast <;> ring
  mul_mem' := by
    rintro q p (⟨a, b, c, d, hqa, hqi, hqj, hqk⟩ | ⟨a, b, c, d, hqa, hqi, hqj, hqk⟩)
      (⟨a', b', c', d', hpa, hpi, hpj, hpk⟩ | ⟨a', b', c', d', hpa, hpi, hpj, hpk⟩)
    · -- integer × integer: the Lipschitz-integer computation.
      refine .inl ⟨a * a' - b * b' - c * c' - d * d', a * b' + b * a' + c * d' - d * c',
        a * c' - b * d' + c * a' + d * b', a * d' + b * c' - c * b' + d * a', ?_, ?_, ?_, ?_⟩ <;>
        simp only [re_mul, imI_mul, imJ_mul, imK_mul, hqa, hqi, hqj, hqk, hpa, hpi, hpj, hpk] <;>
        push_cast <;> ring
    · -- integer × half-integer: parity of `a + b + c + d` decides the branch.
      rcases Int.even_or_odd (a + b + c + d) with ⟨k, hk⟩ | ⟨k, hk⟩
      · have ha : (a : ℚ) = 2 * k - b - c - d := by exact_mod_cast (by omega)
        refine .inl ⟨a * a' - b * b' - c * c' - d * d' + k - b - c - d,
          a * b' + b * a' + c * d' - d * c' + k - d,
          a * c' - b * d' + c * a' + d * b' + k - b,
          a * d' + b * c' - c * b' + d * a' + k - c, ?_, ?_, ?_, ?_⟩ <;>
          simp only [re_mul, imI_mul, imJ_mul, imK_mul, hqa, hqi, hqj, hqk, hpa, hpi, hpj, hpk] <;>
          push_cast <;> rw [ha] <;> ring
      · have ha : (a : ℚ) = 2 * k + 1 - b - c - d := by exact_mod_cast (by omega)
        refine .inr ⟨a * a' - b * b' - c * c' - d * d' + k - b - c - d,
          a * b' + b * a' + c * d' - d * c' + k - d,
          a * c' - b * d' + c * a' + d * b' + k - b,
          a * d' + b * c' - c * b' + d * a' + k - c, ?_, ?_, ?_, ?_⟩ <;>
          simp only [re_mul, imI_mul, imJ_mul, imK_mul, hqa, hqi, hqj, hqk, hpa, hpi, hpj, hpk] <;>
          push_cast <;> rw [ha] <;> ring
    · -- half-integer × integer: parity of `a' + b' + c' + d'` decides the branch.
      rcases Int.even_or_odd (a' + b' + c' + d') with ⟨k, hk⟩ | ⟨k, hk⟩
      · have ha : (a' : ℚ) = 2 * k - b' - c' - d' := by exact_mod_cast (by omega)
        refine .inl ⟨a * a' - b * b' - c * c' - d * d' + k - b' - c' - d',
          a * b' + b * a' + c * d' - d * c' + k - c',
          a * c' - b * d' + c * a' + d * b' + k - d',
          a * d' + b * c' - c * b' + d * a' + k - b', ?_, ?_, ?_, ?_⟩ <;>
          simp only [re_mul, imI_mul, imJ_mul, imK_mul, hqa, hqi, hqj, hqk, hpa, hpi, hpj, hpk] <;>
          push_cast <;> rw [ha] <;> ring
      · have ha : (a' : ℚ) = 2 * k + 1 - b' - c' - d' := by exact_mod_cast (by omega)
        refine .inr ⟨a * a' - b * b' - c * c' - d * d' + k - b' - c' - d',
          a * b' + b * a' + c * d' - d * c' + k - c',
          a * c' - b * d' + c * a' + d * b' + k - d',
          a * d' + b * c' - c * b' + d * a' + k - b', ?_, ?_, ?_, ?_⟩ <;>
          simp only [re_mul, imI_mul, imJ_mul, imK_mul, hqa, hqi, hqj, hqk, hpa, hpi, hpj, hpk] <;>
          push_cast <;> rw [ha] <;> ring
    · -- half-integer × half-integer: parity of the sum of all eight integer parts.
      rcases Int.even_or_odd (a + b + c + d + a' + b' + c' + d') with ⟨k, hk⟩ | ⟨k, hk⟩
      · -- even total: the four quarter terms leave every coordinate in `ℤ + 1/2`.
        have ha : (a : ℚ) = 2 * k - b - c - d - a' - b' - c' - d' := by
          exact_mod_cast (by omega)
        refine .inr ⟨a * a' - b * b' - c * c' - d * d' + k - b - b' - c - c' - d - d' - 1,
          a * b' + b * a' + c * d' - d * c' + k - d - c',
          a * c' - b * d' + c * a' + d * b' + k - b - d',
          a * d' + b * c' - c * b' + d * a' + k - c - b', ?_, ?_, ?_, ?_⟩ <;>
          simp only [re_mul, imI_mul, imJ_mul, imK_mul, hqa, hqi, hqj, hqk, hpa, hpi, hpj, hpk] <;>
          push_cast <;> rw [ha] <;> ring
      · -- odd total: the quarter terms cancel and every coordinate is an integer.
        have ha : (a : ℚ) = 2 * k + 1 - b - c - d - a' - b' - c' - d' := by
          exact_mod_cast (by omega)
        refine .inl ⟨a * a' - b * b' - c * c' - d * d' + k - b - b' - c - c' - d - d',
          a * b' + b * a' + c * d' - d * c' + k + 1 - d - c',
          a * c' - b * d' + c * a' + d * b' + k + 1 - b - d',
          a * d' + b * c' - c * b' + d * a' + k + 1 - c - b', ?_, ?_, ?_, ?_⟩ <;>
          simp only [re_mul, imI_mul, imJ_mul, imK_mul, hqa, hqi, hqj, hqk, hpa, hpi, hpj, hpk] <;>
          push_cast <;> rw [ha] <;> ring

end HurwitzQ


