-- Prove2me | Definitions.Def_KhachiyanRounding_BCD_Scalar
-- name    : KhachiyanRounding_BCD_Scalar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T14:43:11.820213+00:00
-- url     : https://prove2.me/theorems/c2c624ad-97fc-4d35-ad33-cd879962a83f
-- title:
--   Costed exact-real scalar loops and guarded elimination
-- statement:
--   An exact-real computation acts on ordinary finite scalar arrays and carries a natural-number counter. Every real addition, subtraction, multiplication and comparison costs one. A successful division costs two: one zero-denominator comparison and one division. Division by zero fails. Loading constants and integer size parameters, index arithmetic, array reads, writes and copies, and integer loop control are free.
--
--   Finite sums, dot products, matrix-vector products and diagonal-pivot Gauss–Jordan elimination are explicit scalar loops. Elimination operates on both halves of the augmented matrix; it contains no inverse oracle. Failure is represented by an absent result. On success the result contains the actual accumulated count.
--
--   This general execution layer provides the arithmetic model for the BCD implementation. It asserts no correctness, termination, positivity or complexity guarantee.
-- source:
--   Leonid G. Khachiyan (1996), Rounding of Polytopes in the Real Number Model of Computation, Mathematics of Operations Research 21(2), 307–320, https://doi.org/10.1287/moor.21.2.307, §1, (1.3), printed p.307 / PDF p.2; §2 rank-one implementation discussion, printed p.314 / PDF p.9. Scalarization and guarded Gauss–Jordan are explicit implementation choices in that model.

import Mathlib

namespace KhachiyanRounding.BCD

/-- Exact-real register computations. The state is the number of scalar operations
and comparisons executed. Array access, copying, index operations, integer loop
control, and loading 0, 1 and integer size parameters are free. No real-valued
operation outside the primitives below is permitted in the implementation.
A failed guarded division returns `none`; successful executions retain all costs.
Source: Khachiyan (1996), §§1–3, real arithmetic/comparison model. -/
abbrev Calc (α : Type) := StateT ℕ Option α

noncomputable def add (x y : ℝ) : Calc ℝ := fun c => some (x + y, c + 1)
noncomputable def sub (x y : ℝ) : Calc ℝ := fun c => some (x - y, c + 1)
noncomputable def mul (x y : ℝ) : Calc ℝ := fun c => some (x * y, c + 1)

/-- One real comparison, including equality at the boundary. -/
noncomputable def le (x y : ℝ) : Calc Bool := by
  classical
  exact fun c => some (decide (x ≤ y), c + 1)

/-- One equality comparison followed, if nonzero, by one division. -/
noncomputable def divide (x y : ℝ) : Calc ℝ := by
  classical
  exact fun c => if y = 0 then none else some (x / y, c + 2)

/-- Finite scalar register array, filled in increasing index order. -/
noncomputable def vector {n : ℕ} (f : Fin n → Calc ℝ) : Calc (Fin n → ℝ) :=
  (List.finRange n).foldlM (fun v i => do
    let x ← f i
    pure (Function.update v i x)) (fun _ => 0)

noncomputable def matrix {n : ℕ} (f : Fin n → Fin n → Calc ℝ) :
    Calc (Matrix (Fin n) (Fin n) ℝ) :=
  (List.finRange n).foldlM (fun A i => do
    let row ← vector (f i)
    pure (Function.update A i row)) (fun _ _ => 0)

/-- A scalar loop, with every summand and every addition charged. -/
noncomputable def sumList {ι : Type} (L : List ι) (f : ι → Calc ℝ) : Calc ℝ :=
  L.foldlM (fun s i => do
    let x ← f i
    add s x) 0

noncomputable def dot {n : ℕ} (x y : Fin n → ℝ) : Calc ℝ :=
  sumList (List.finRange n) (fun i => mul (x i) (y i))

noncomputable def matvec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : Calc (Fin n → ℝ) := vector (fun i => dot (A i) x)

/-- Gauss–Jordan elimination, pivoting on diagonal k at stage k. This definite
pivot rule succeeds for positive-definite inputs; that is a theorem obligation,
not a certificate or input field. Both halves of the augmented matrix are
normalized and eliminated by scalar loops. No matrix inverse is a primitive. -/
noncomputable def invert {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    Calc (Matrix (Fin n) (Fin n) ℝ) := do
  let (_, H) ← (List.finRange n).foldlM (fun (BH :
      Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin n) ℝ) k => do
    let (B, H) := BH
    let pivot := B k k
    let rowB ← vector (fun j => divide (B k j) pivot)
    let rowH ← vector (fun j => divide (H k j) pivot)
    let B' ← matrix (fun i j =>
      if i = k then pure (rowB j) else do
        let x ← mul (B i k) (rowB j)
        sub (B i j) x)
    let H' ← matrix (fun i j =>
      if i = k then pure (rowH j) else do
        let x ← mul (B i k) (rowH j)
        sub (H i j) x)
    pure (B', H')) (A, fun i j => if i = j then 1 else 0)
  pure H

end KhachiyanRounding.BCD


