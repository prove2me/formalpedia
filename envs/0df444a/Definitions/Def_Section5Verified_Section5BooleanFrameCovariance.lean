-- Prove2me | Definitions.Def_Section5Verified_Section5BooleanFrameCovariance
-- name    : Section5Verified_Section5BooleanFrameCovariance
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-26T19:02:25.824815+00:00
-- url     : https://prove2.me/theorems/9b94b29c-4226-56a2-877f-c38b6e78c094
-- title:
--   Section5BooleanFrameCovariance — verified interface
-- statement:
--   Finite register types, encodings, and structural interfaces used by the Section 5 supporting constructions. The included identities are required to make these definitions importable with their verified semantics.
-- source:
--   Supporting formalization for https://arxiv.org/html/2609.40331v3, Section 5; original source Solutions.Section5BooleanFrameCovariance; mechanically extracted with exact Lean declaration spans.

import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Mathlib
section
set_option autoImplicit false

/-! Exact normalization and diagonal-corrected covariance of the Boolean frame.
This does not yet assert a gate-efficient implementation or concentration. -/

namespace Section5BooleanFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def amplitude (w : ι → ℝ) (x : ι → Bool) : ℝ :=
  ∑ i, w i*sign x i

theorem amplitude_sq_expansion (w : ι → ℝ) (x : ι → Bool) :
    amplitude w x ^ 2=∑ i, ∑ j, (w i*w j)*(sign x i*sign x j) := by
  simp only [amplitude,pow_two,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem amplitude_second (w : ι → ℝ) :
    average (fun x => amplitude w x ^ 2)=∑ i, w i ^ 2 := by
  simp only [amplitude_sq_expansion,average_sum,average_smul,sign_second]
  simp [mul_ite,pow_two]



noncomputable def weight (w : ι → ℝ) (x : ι → Bool) : ℝ :=
  (Fintype.card (ι → Bool) : ℝ)⁻¹ * amplitude w x ^ 2

theorem weight_nonneg (w : ι → ℝ) (x : ι → Bool) : 0 ≤ weight w x := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (sq_nonneg _)

theorem weight_sum (w : ι → ℝ) : (∑ x, weight w x)=∑ i, w i ^ 2 := by
  simpa only [weight,← Finset.mul_sum,average] using amplitude_second w



end Section5BooleanFrame

end


