-- Prove2me | Definitions.Def_D1Bound5_UnitPairPellClassification_Definitions
-- name    : D1Bound5_UnitPairPellClassification_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:10:37.928602+00:00
-- url     : https://prove2.me/theorems/d5992b10-044d-4600-af48-b8acaceb7fa3
-- title:
--   Unit Pair Pell Classification
-- statement:
--   Exact Pell description in the integer square-root basis. The variables u,v are signed integers; v is nonzero in both alternatives. The named objects in this bundle include `QuadInt.integerBasisToHalf`. The accompanying auxiliary certificates are included with their original proofs.
-- source:
--   D1Bound5/UnitPairPellClassification.lean, lines 8-12, SHA-256 e341ce21d7fb1df24b87b482804148ffb2b4b0b3efe42d9b54d600c5e4d52faa; D1Bound5/UnitPairPellClassification.lean, lines 16-106, SHA-256 e341ce21d7fb1df24b87b482804148ffb2b4b0b3efe42d9b54d600c5e4d52faa; D1Bound5/UnitPairPellClassification.lean, lines 108-115, SHA-256 e341ce21d7fb1df24b87b482804148ffb2b4b0b3efe42d9b54d600c5e4d52faa; D1Bound5/UnitPairPellClassification.lean, lines 117-124, SHA-256 e341ce21d7fb1df24b87b482804148ffb2b4b0b3efe42d9b54d600c5e4d52faa; D1Bound5/UnitPairPellClassification.lean, lines 126-149, SHA-256 e341ce21d7fb1df24b87b482804148ffb2b4b0b3efe42d9b54d600c5e4d52faa; D1Bound5/UnitPairPellClassification.lean, lines 151-179, SHA-256 e341ce21d7fb1df24b87b482804148ffb2b4b0b3efe42d9b54d600c5e4d52faa; D1Bound5/UnitPairPellClassification.lean, lines 181-202, SHA-256 e341ce21d7fb1df24b87b482804148ffb2b4b0b3efe42d9b54d600c5e4d52faa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_UnitPairAxes_Definitions

section
open scoped QuadraticAlgebra

namespace D1Bound5

private theorem integer_square_ne_two (x : ℤ) : x^2 ≠ 2 := by
  intro h
  have hlo : -1 ≤ x := by nlinarith [sq_nonneg (x+2)]
  have hhi : x ≤ 1 := by nlinarith [sq_nonneg (x-2)]
  interval_cases x <;> norm_num at h

namespace QuadInt

/-- Exact Pell description in the integer square-root basis. The variables
u,v are signed integers; v is nonzero in both alternatives. -/
theorem unit_pair_integer_basis_pell {d : ℤ} (hd : 0 < d)
    (z r s : QuadInt 0 d) (hz : z ≠ 0)
    (hr : r*r = z+1) (hs : s*s = 1-z) :
    (∃ u v : ℤ, v ≠ 0 ∧ u^2-d*v^2 = 2 ∧
      (z = ((d*v^2+1 : ℤ) : QuadInt 0 d) ∨
       z = -((d*v^2+1 : ℤ) : QuadInt 0 d))) ∨
    (∃ u v : ℤ, v ≠ 0 ∧ u^2-d*v^2 = 1 ∧ z = ⟨0,2*u*v⟩) := by
  have hrr : r.re^2-d*r.im^2 = z.re+1 := by
    have h := congrArg QuadraticAlgebra.re hr
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.re_add,
      QuadraticAlgebra.re_one] at h
    nlinarith only [h]
  have hri : 2*r.re*r.im = z.im := by
    have h := congrArg QuadraticAlgebra.im hr
    simp only [QuadraticAlgebra.im_mul,QuadraticAlgebra.im_add,
      QuadraticAlgebra.im_one] at h
    nlinarith only [h]
  have hsr : s.re^2-d*s.im^2 = 1-z.re := by
    have h := congrArg QuadraticAlgebra.re hs
    simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.re_sub,
      QuadraticAlgebra.re_one] at h
    nlinarith only [h]
  have hsi : 2*s.re*s.im = -z.im := by
    have h := congrArg QuadraticAlgebra.im hs
    simp only [QuadraticAlgebra.im_mul,QuadraticAlgebra.im_sub,
      QuadraticAlgebra.im_one] at h
    nlinarith only [h]
  have hd' : 0 < discriminant 0 d := by simpa [discriminant] using mul_pos (by decide : (0:ℤ)<4) hd
  rcases unit_pair_extension_axes hd' z r s hr hs with hreal | himag
  · have hrp : r.re*r.im = 0 := by nlinarith only [hri,hreal]
    have hsp : s.re*s.im = 0 := by nlinarith only [hsi,hreal]
    rcases mul_eq_zero.mp hrp with hrr0 | hri0
    · rcases mul_eq_zero.mp hsp with hsr0 | hsi0
      · have hnonneg := mul_nonneg hd.le (add_nonneg (sq_nonneg r.im) (sq_nonneg s.im))
        rw [hrr0] at hrr
        rw [hsr0] at hsr
        nlinarith only [hrr,hsr,hnonneg]
      · have hPell : s.re^2-d*r.im^2 = 2 := by
          rw [hrr0] at hrr
          rw [hsi0] at hsr
          nlinarith only [hrr,hsr]
        have hv : r.im ≠ 0 := by
          intro hzero
          rw [hzero] at hPell
          exact integer_square_ne_two s.re (by nlinarith only [hPell])
        left
        refine ⟨s.re,r.im,hv,hPell,Or.inr ?_⟩
        apply QuadraticAlgebra.ext
        · simp only [QuadraticAlgebra.re_neg, QuadraticAlgebra.re_intCast, Int.cast_id]
          rw [hrr0] at hrr
          nlinarith only [hrr]
        · simpa only [QuadraticAlgebra.im_neg, QuadraticAlgebra.im_intCast,neg_zero] using hreal
    · rcases mul_eq_zero.mp hsp with hsr0 | hsi0
      · have hPell : r.re^2-d*s.im^2 = 2 := by
          rw [hri0] at hrr
          rw [hsr0] at hsr
          nlinarith only [hrr,hsr]
        have hv : s.im ≠ 0 := by
          intro hzero
          rw [hzero] at hPell
          exact integer_square_ne_two r.re (by nlinarith only [hPell])
        left
        refine ⟨r.re,s.im,hv,hPell,Or.inl ?_⟩
        apply QuadraticAlgebra.ext
        · simp only [QuadraticAlgebra.re_intCast, Int.cast_id]
          rw [hsr0] at hsr
          nlinarith only [hsr]
        · simpa only [QuadraticAlgebra.im_intCast] using hreal
      · rw [hri0] at hrr
        rw [hsi0] at hsr
        have hsum : r.re^2+s.re^2 = 2 := by nlinarith only [hrr,hsr]
        have hrne := integer_square_ne_two r.re
        have hsne := integer_square_ne_two s.re
        have hrone : r.re^2 = 1 := by
          have hr0 := sq_nonneg r.re
          have hs0 := sq_nonneg s.re
          omega
        have hzre : z.re = 0 := by nlinarith only [hrr,hrone]
        exact (hz (QuadraticAlgebra.ext hzre hreal)).elim
  · have hzre : z.re = 0 := by nlinarith only [himag]
    have hv : r.im ≠ 0 := by
      intro hzero
      have hzimm : z.im = 0 := by
        rw [hzero, mul_zero] at hri
        exact hri.symm
      exact hz (QuadraticAlgebra.ext hzre hzimm)
    right
    refine ⟨r.re,r.im,hv,by nlinarith only [hrr,hzre],?_⟩
    exact QuadraticAlgebra.ext hzre hri.symm

/-- The square-root basis embeds in the half-integral basis via
sqrt(-d)=2omega-1, with d=4nu-1. -/
def integerBasisToHalf (nu : ℤ) : QuadInt 0 (4*nu-1) →+* QuadInt 1 nu where
  toFun z := ⟨z.re-z.im,2*z.im⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' z w := by ext <;> simp <;> ring
  map_mul' z w := by ext <;> simp <;> ring

theorem integerBasisToHalf_injective (nu : ℤ) :
    Function.Injective (integerBasisToHalf nu) := by
  intro x y h
  have hr := congrArg QuadraticAlgebra.re h
  have hi := congrArg QuadraticAlgebra.im h
  change x.re-x.im = y.re-y.im at hr
  change 2*x.im = 2*y.im at hi
  apply QuadraticAlgebra.ext <;> omega

/-- A half-integral root of either unit-pair radicand in fact has even
second coordinate. This is derived from the proved axes dichotomy. -/
theorem unit_pair_half_root_even {nu : ℤ}
    (hd : 0 < discriminant 1 nu) (z r s : QuadInt 1 nu)
    (hr : r*r = z+1) (hs : s*s = 1-z) : ∃ v : ℤ, r.im = 2*v := by
  have hrr := congrArg QuadraticAlgebra.re hr
  have hri := congrArg QuadraticAlgebra.im hr
  simp only [QuadraticAlgebra.re_mul,QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_add,QuadraticAlgebra.im_add,
    QuadraticAlgebra.re_one,QuadraticAlgebra.im_one] at hrr hri
  rcases unit_pair_extension_axes hd z r s hr hs with hreal | himag
  · have hp : r.im*(2*r.re+r.im) = 0 := by linear_combination hri+hreal
    rcases mul_eq_zero.mp hp with hzero | htrace
    · exact ⟨0,by simpa using hzero⟩
    · exact ⟨-r.re,by linarith only [htrace]⟩
  · have htrace : 2*r.re^2+2*r.re*r.im+(1-2*nu)*r.im^2 = 2 := by
      linear_combination 2*hrr+hri+himag
    have hmod := congrArg (fun a : ℤ => a % 2) htrace
    have hcases : r.im % 2 = 0 ∨ r.im % 2 = 1 := by omega
    have heven : r.im % 2 = 0 := by
      rcases hcases with h | h
      · exact h
      · norm_num [pow_two,Int.add_emod,Int.sub_emod,Int.mul_emod,h] at hmod
    exact ⟨r.im/2,by omega⟩

theorem unit_pair_half_root_lift {nu : ℤ}
    (hd : 0 < discriminant 1 nu) (z r s : QuadInt 1 nu)
    (hr : r*r = z+1) (hs : s*s = 1-z) :
    ∃ R S Z : QuadInt 0 (4*nu-1),
      integerBasisToHalf nu R = r ∧ integerBasisToHalf nu S = s ∧
      integerBasisToHalf nu Z = z ∧ R*R = Z+1 ∧ S*S = 1-Z := by
  obtain ⟨v,hv⟩ := unit_pair_half_root_even hd z r s hr hs
  have hs' : s*s = (-z)+1 := by linear_combination hs
  have hr' : r*r = 1-(-z) := by linear_combination hr
  obtain ⟨w,hw⟩ := unit_pair_half_root_even hd (-z) s r hs' hr'
  let R : QuadInt 0 (4*nu-1) := ⟨r.re+v,v⟩
  let S : QuadInt 0 (4*nu-1) := ⟨s.re+w,w⟩
  let Z := R*R-1
  have hR : integerBasisToHalf nu R = r := by
    apply QuadraticAlgebra.ext
    · change r.re+v-v = r.re
      ring
    · exact hv.symm
  have hS : integerBasisToHalf nu S = s := by
    apply QuadraticAlgebra.ext
    · change s.re+w-w = s.re
      ring
    · exact hw.symm
  have hZ : integerBasisToHalf nu Z = z := by
    simp only [Z,map_sub,map_mul,map_one,hR]
    linear_combination hr
  refine ⟨R,S,Z,hR,hS,hZ,by dsimp [Z]; ring,?_⟩
  apply integerBasisToHalf_injective nu
  simpa only [map_mul,map_sub,map_one,hS,hZ] using hs

/-- The same precise Pell alternatives in the full half-integral basis.
In the imaginary branch, (−2uv,4uv)=2uv(2omega−1). -/
theorem unit_pair_half_basis_pell {nu : ℤ}
    (hd : 0 < discriminant 1 nu) (z r s : QuadInt 1 nu) (hz : z ≠ 0)
    (hr : r*r = z+1) (hs : s*s = 1-z) :
    (∃ u v : ℤ, v ≠ 0 ∧ u^2-(4*nu-1)*v^2 = 2 ∧
      (z = (((4*nu-1)*v^2+1 : ℤ) : QuadInt 1 nu) ∨
       z = -(((4*nu-1)*v^2+1 : ℤ) : QuadInt 1 nu))) ∨
    (∃ u v : ℤ, v ≠ 0 ∧ u^2-(4*nu-1)*v^2 = 1 ∧ z = ⟨-2*u*v,4*u*v⟩) := by
  obtain ⟨R,S,Z,hR,hS,hZ,hrZ,hsZ⟩ := unit_pair_half_root_lift hd z r s hr hs
  have hd' : 0 < 4*nu-1 := by simpa [discriminant] using hd
  have hZ0 : Z ≠ 0 := by intro h; apply hz; rw [← hZ,h,map_zero]
  rcases unit_pair_integer_basis_pell hd' Z R S hZ0 hrZ hsZ with hreal | himag
  · left
    obtain ⟨u,v,hv,hPell,hplus | hminus⟩ := hreal
    · exact ⟨u,v,hv,hPell,Or.inl (by rw [← hZ,hplus,map_intCast])⟩
    · exact ⟨u,v,hv,hPell,Or.inr (by rw [← hZ,hminus,map_neg,map_intCast])⟩
  · right
    obtain ⟨u,v,hv,hPell,hcoord⟩ := himag
    refine ⟨u,v,hv,hPell,?_⟩
    rw [← hZ,hcoord]
    apply QuadraticAlgebra.ext <;> dsimp [integerBasisToHalf] <;> ring

end QuadInt
end D1Bound5
end


