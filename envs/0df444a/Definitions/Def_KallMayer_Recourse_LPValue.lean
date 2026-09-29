-- Prove2me | Definitions.Def_KallMayer_Recourse_LPValue
-- name    : KallMayer_Recourse_LPValue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T03:53:21.369828+00:00
-- url     : https://prove2.me/theorems/62776177-d43d-4dbe-bc59-7fac6cdb7ffd
-- title:
--   KallMayer_Recourse_LPValue
-- statement:
--   Concrete book-local definitions from Definitions.Def_KallMayer_Recourse_LPValue. Chapter 1 §2.3 Proposition 2.11 PDF31 / printed20; LP pair PDF30; full row rank PDF24
-- source:
--   Chapter 1 §2.3 Proposition 2.11 PDF31 / printed20; LP pair PDF30; full row rank PDF24

import Mathlib

namespace KallMayer.Recourse

/-- The value of min {cᵀx | Ax = b, x ≥ 0}; Lemma 2.3, printed p. 206.
The EReal infimum gives +∞ for infeasibility and -∞ for unboundedness. -/
noncomputable def LPValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (b : Fin m → ℝ) : EReal :=
  sInf {r : EReal | ∃ x : Fin n → ℝ,
    (∀ j, 0 ≤ x j) ∧ Matrix.mulVec A x = b ∧
    r = ((dotProduct c x : ℝ) : EReal)}

/-- The primal LP has a finite attained minimum for every right-hand side.
This encodes “solvable ∀b” in Lemma 2.3 without assuming duality. -/
def SolvableEveryRHS {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) : Prop :=
  ∀ b : Fin m → ℝ, ∃ x : Fin n → ℝ,
    (∀ j, 0 ≤ x j) ∧ Matrix.mulVec A x = b ∧
    ∀ y : Fin n → ℝ, (∀ j, 0 ≤ y j) → Matrix.mulVec A y = b →
      dotProduct c x ≤ dotProduct c y

/-- The argmax of bᵀu over Aᵀu ≤ c, defined independently of primal values. -/
def DualOptimizers {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (b : Fin m → ℝ) : Set (Fin m → ℝ) :=
  {u | (∀ j, Matrix.mulVec A.transpose u j ≤ c j) ∧
    ∀ v : Fin m → ℝ, (∀ j, Matrix.mulVec A.transpose v j ≤ c j) →
      dotProduct b v ≤ dotProduct b u}

end KallMayer.Recourse


