-- Prove2me | Definitions.Def_Section5Verified_Section5BooleanFrameMoments
-- name    : Section5Verified_Section5BooleanFrameMoments
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:01:18.008131+00:00
-- url     : https://prove2.me/theorems/9bea3b16-8cd0-4289-acda-f7292a61e70a
-- title:
--   Section5BooleanFrameMoments — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5BooleanFrameMoments; mechanically extracted with exact Lean declaration spans.

import Mathlib
section
set_option autoImplicit false

/-! Exact moments of the full Boolean sign frame. These are concrete finite
sums, with no independence or moment assumptions. They identify the covariance
that a coded, bounded-independence implementation must reproduce. -/

namespace Section5BooleanFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def sign (x : ι → Bool) (i : ι) : ℝ := if x i then -1 else 1

noncomputable def average (f : (ι → Bool) → ℝ) : ℝ :=
  (Fintype.card (ι → Bool) : ℝ)⁻¹ * ∑ x, f x

def flip (i : ι) : Equiv.Perm (ι → Bool) where
  toFun x := Function.update x i (!(x i))
  invFun x := Function.update x i (!(x i))
  left_inv x := by ext j; by_cases h : j=i <;> simp [h]
  right_inv x := by ext j; by_cases h : j=i <;> simp [h]

@[simp] theorem sign_sq (x : ι → Bool) (i : ι) : sign x i ^ 2 = 1 := by
  unfold sign
  split <;> norm_num

@[simp] theorem sign_mul_self (x : ι → Bool) (i : ι) : sign x i * sign x i = 1 := by
  simpa only [pow_two] using sign_sq x i

@[simp] theorem sign_flip_same (x : ι → Bool) (i : ι) : sign (flip i x) i = -sign x i := by
  simp only [sign,flip,Equiv.coe_fn_mk,Function.update_self]
  cases x i <;> norm_num

theorem sign_flip_other (x : ι → Bool) {i j : ι} (h : j ≠ i) :
    sign (flip i x) j=sign x j := by
  simp [sign,flip,h]



theorem average_smul (a : ℝ) (f : (ι → Bool) → ℝ) :
    average (fun x => a*f x)=a*average f := by
  simp only [average,← Finset.mul_sum]
  ring

theorem average_sum {κ : Type*} [Fintype κ] (f : κ → (ι → Bool) → ℝ) :
    average (fun x => ∑ i, f i x)=∑ i, average (f i) := by
  simp only [average,Finset.mul_sum]
  exact Finset.sum_comm

@[simp] theorem average_const (a : ℝ) : average (fun _ : ι → Bool => a)=a := by
  simp [average]

theorem average_flip (i : ι) (f : (ι → Bool) → ℝ) :
    average (fun x => f (flip i x))=average f := by
  simp only [average,Equiv.sum_comp]

theorem average_zero_of_flip (i : ι) (f : (ι → Bool) → ℝ)
    (h : ∀ x, f (flip i x)= -f x) : average f=0 := by
  have he := average_flip i f
  simp only [h,average,Finset.sum_neg_distrib,mul_neg] at he
  change -(average f)=average f at he
  linarith



theorem sign_second (i j : ι) :
    average (fun x : ι → Bool => sign x i*sign x j)=if i=j then 1 else 0 := by
  by_cases h : i=j
  · subst j
    simp
  · rw [if_neg h]
    apply average_zero_of_flip i
    intro x
    rw [sign_flip_same,sign_flip_other x (Ne.symm h)]
    ring



end Section5BooleanFrame

end


