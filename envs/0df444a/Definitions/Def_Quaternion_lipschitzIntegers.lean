-- Prove2me | Definitions.Def_Quaternion_lipschitzIntegers
-- name    : Quaternion_lipschitzIntegers
-- status  : Definition
-- author  : @jawneeboy
-- created : 2026-09-18T17:58:54.656589+00:00
-- url     : https://prove2.me/theorems/0d67e170-c779-4d9b-9b51-f593ec164cdc
-- title:
--   Lipschitz integers over the reals
-- statement:
--   The Lipschitz integers form the real-quaternion subring $$\mathcal{L}=\{a+bi+cj+dk:a,b,c,d\in\mathbb{Z}\}=\mathbb{Z}[i,j,k].$$ This is the integral-coordinate model used alongside the Hurwitz ring.
-- source:
--   Standard definition: John H. Conway and Derek A. Smith, On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry, A K Peters, 2003, §5.1, The Hurwitz Integral Quaternions. https://www.routledge.com/On-Quaternions-and-Octonions/Conway-Smith/p/book/9781568811345

import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Lipschitz integers

The Lipschitz ring $\mathcal{L}=\mathbb{Z}[i,j,k]$ consists of quaternions
$a+bi+cj+dk$ with $a,b,c,d\in\mathbb{Z}$. This file realizes it as a
subring of the real quaternions. It supplies the integral-coordinate model
used in the Hurwitz membership examples.

Reference: John H. Conway and Derek A. Smith, *On Quaternions and Octonions: Their Geometry, Arithmetic, and Symmetry*, A K Peters, 2003, §5.1, "The Hurwitz Integral Quaternions".
-/

open Quaternion

/-- The Lipschitz integers are the quaternions `a + b*i + c*j + d*k` whose
four coordinates `a, b, c, d` are integers, as a subring of `ℍ[ℝ]`. -/
def lipschitzIntegers : Subring ℍ[ℝ] where
  carrier := { q | ∃ a b c d : ℤ, q.re = ↑a ∧ q.imI = ↑b ∧ q.imJ = ↑c ∧ q.imK = ↑d }
  one_mem' := ⟨1, 0, 0, 0, by simp⟩
  zero_mem' := ⟨0, 0, 0, 0, by simp⟩
  mul_mem' := by
    rintro q p ⟨a, b, c, d, hqa, hqi, hqj, hqk⟩ ⟨a', b', c', d', hpa, hpi, hpj, hpk⟩
    refine ⟨a * a' - b * b' - c * c' - d * d', a * b' + b * a' + c * d' - d * c',
      a * c' - b * d' + c * a' + d * b', a * d' + b * c' - c * b' + d * a', ?_, ?_, ?_, ?_⟩ <;>
      simp only [re_mul, imI_mul, imJ_mul, imK_mul, hqa, hqi, hqj, hqk, hpa, hpi, hpj, hpk] <;>
      push_cast <;> ring
  add_mem' := by
    rintro q p ⟨a, b, c, d, hqa, hqi, hqj, hqk⟩ ⟨a', b', c', d', hpa, hpi, hpj, hpk⟩
    refine ⟨a + a', b + b', c + c', d + d', ?_, ?_, ?_, ?_⟩ <;>
      simp only [show (q + p).re = q.re + p.re from rfl, show (q + p).imI = q.imI + p.imI from rfl,
        show (q + p).imJ = q.imJ + p.imJ from rfl, show (q + p).imK = q.imK + p.imK from rfl,
        hqa, hqi, hqj, hqk, hpa, hpi, hpj, hpk] <;>
      push_cast <;> ring
  neg_mem' := by
    rintro q ⟨a, b, c, d, hqa, hqi, hqj, hqk⟩
    refine ⟨-a, -b, -c, -d, ?_, ?_, ?_, ?_⟩ <;>
      simp only [show (-q).re = -q.re from rfl, show (-q).imI = -q.imI from rfl,
        show (-q).imJ = -q.imJ from rfl, show (-q).imK = -q.imK from rfl,
        hqa, hqi, hqj, hqk] <;>
      push_cast <;> ring


