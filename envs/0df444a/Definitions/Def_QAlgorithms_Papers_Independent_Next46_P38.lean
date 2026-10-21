-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P38
-- name    : QAlgorithms_Papers_Independent_Next46_P38
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T14:40:38.708346+00:00
-- url     : https://prove2.me/theorems/2c946bad-485c-4eb0-99b8-c2dd4ec00855
-- title:
--   Definitions for Noncommutative maximal ergodic theorems
-- statement:
--   The objects the formalized statements of *Noncommutative maximal ergodic theorems* (arXiv:math/0505308) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `blockNormPadding`: The rectangular scalar matrix of compressed block norms in Lemma 3.2, PDF p.13, embedded as the upper-right block of a square matrix on `I ⊕ J`. All other blocks are zero. Its Euclidean operator norm equals that of the rectangular map from `ell2(J)` to `ell2(I)`.
-- source:
--   Noncommutative maximal ergodic theorems, arXiv:math/0505308v2, https://arxiv.org/abs/math/0505308v2

import Mathlib

/-!
Statements from Junge--Xu, Noncommutative maximal ergodic theorems,
arXiv:math/0505308v2. The source-page references below are PDF page numbers.
The assigned unit records every other planned node as an explicit deferral;
no abstract Lp structure is substituted for the actual operator spaces.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P38

universe u v w

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The rectangular scalar matrix of compressed block norms in Lemma 3.2,
PDF p.13, embedded as the upper-right block of a square matrix on `I ⊕ J`.
All other blocks are zero. Its Euclidean operator norm equals that of the
rectangular map from `ell2(J)` to `ell2(I)`. -/
def blockNormPadding {I : Type v} {J : Type w}
    (x : I → J → (H →L[ℂ] H))
    (e : I → (H →L[ℂ] H)) (f : J → (H →L[ℂ] H)) :
    Matrix (Sum I J) (Sum I J) ℂ :=
  fun a b => match a, b with
    | Sum.inl i, Sum.inr j => (‖e i * x i j * f j‖ : ℂ)
    | _, _ => 0

example {I : Type v} {J : Type w}
    (e : I → (H →L[ℂ] H)) (f : J → (H →L[ℂ] H)) :
    blockNormPadding (fun _ _ => (0 : H →L[ℂ] H)) e f = 0 := by
  ext a b
  cases a <;> cases b <;> simp [blockNormPadding]

end QAlgorithms.Papers.Independent.Next46.P38


