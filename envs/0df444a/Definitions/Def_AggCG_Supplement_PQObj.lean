-- Prove2me | Definitions.Def_AggCG_Supplement_PQObj
-- name    : AggCG_Supplement_PQObj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:25:58.814202+00:00
-- url     : https://prove2.me/theorems/3ec57765-999b-4c82-b759-80e948ee3554
-- title:
--   Rational piecewise-quadratic objectives and gradient-descent runs
-- statement:
--   A piecewise-quadratic objective is given by rational affine boundaries and rational quadratic pieces, and may be discontinuous across the boundaries. Away from every boundary, its gradient is the gradient of the active quadratic piece. Gradient descent follows $x_{t+1}=x_t-\eta_t\nabla f(x_t)$, and a run is regular when all iterates through the horizon avoid every boundary.
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), §L and Theorem L.2, pp.64–65, PDF pp.65–66

import Mathlib
import Definitions.Def_AggCG_Supplement_stopCost

namespace AggCG.Supplement

/-- An affine function `x ↦ gᵀx + c` on `ℝ^D` with rational data, used as a piece boundary
(Sharma, *Computational Complexity of Data-Driven Configuration for Integer Programming, Clustering, and
Learning Algorithms*, STOC 2027 submission (manuscript sha256 f7ea0248…), §L, p.64, PDF p.65;
Theorem L.2, p.65, PDF p.66: "affine boundaries"). -/
structure AffineQ (D : ℕ) where
  /-- Linear part. -/
  g : Fin D → ℚ
  /-- Offset. -/
  c : ℚ

/-- Value of an affine function. -/
def AffineQ.eval {D : ℕ} (ℓ : AffineQ D) (x : Fin D → ℝ) : ℝ := ∑ i, (ℓ.g i : ℝ) * x i + ℓ.c

/-- A quadratic `x ↦ ½ xᵀQx + gᵀx + c` with rational data. -/
structure QuadQ (D : ℕ) where
  /-- Quadratic part. -/
  Q : Matrix (Fin D) (Fin D) ℚ
  /-- Linear part. -/
  g : Fin D → ℚ
  /-- Constant. -/
  c : ℚ

/-- Gradient `½(Q + Qᵀ)x + g` of the quadratic. -/
def QuadQ.grad {D : ℕ} (q : QuadQ D) (x : Fin D → ℝ) : Fin D → ℝ :=
  fun i => ∑ j, (((q.Q i j + q.Q j i) / 2 : ℚ) : ℝ) * x j + q.g i

/-- A piece of a piecewise-quadratic objective with `nb` boundaries: a sign condition on each boundary
(`none` unconstrained, `some true` strictly positive, `some false` strictly negative) and its quadratic. -/
structure PQPiece (D nb : ℕ) where
  /-- Sign condition on each boundary. -/
  sgn : Fin nb → Option Bool
  /-- The quadratic on this piece. -/
  quad : QuadQ D

/-- A **piecewise-quadratic, possibly discontinuous objective** on `ℝ^D` described with `nb` rational
affine boundaries and a list of pieces (Theorem L.2, p.65; §L, p.64: "piecewise-quadratic objectives",
"pieces separated by affine boundaries"). -/
structure PQObj (D : ℕ) where
  /-- Number of affine boundaries. -/
  nb : ℕ
  /-- The boundaries. -/
  bd : Fin nb → AffineQ D
  /-- The pieces, read in order. -/
  pieces : List (PQPiece D nb)

namespace PQObj

variable {D : ℕ}

/-- `x` lies on no piece boundary. -/
def OffBoundary (f : PQObj D) (x : Fin D → ℝ) : Prop := ∀ b, (f.bd b).eval x ≠ 0

/-- `x` satisfies the sign conditions of a piece. -/
def InPiece (f : PQObj D) (P : PQPiece D f.nb) (x : Fin D → ℝ) : Prop :=
  ∀ b, match P.sgn b with
    | none => True
    | some true => 0 < (f.bd b).eval x
    | some false => (f.bd b).eval x < 0

/-- The description is complete: every point off the boundaries lies in some piece. -/
def Covers (f : PQObj D) : Prop := ∀ x, f.OffBoundary x → ∃ P ∈ f.pieces, f.InPiece P x

open Classical in
/-- The gradient of the objective at a point off the boundaries: the gradient of the quadratic of the
first piece containing it (the objective is that quadratic on an open neighbourhood). -/
noncomputable def grad (f : PQObj D) (x : Fin D → ℝ) : Fin D → ℝ :=
  match f.pieces.find? (fun P => decide (f.InPiece P x)) with
  | some P => P.quad.grad x
  | none => 0

/-- The largest binary code length of a rational number in the description, measured as
`⌈log₂(|num| + 1)⌉ + ⌈log₂ den⌉`-type bit counts via `Nat.size`. -/
def maxBits (f : PQObj D) : ℕ :=
  let bits : ℚ → ℕ := fun q => Nat.size q.num.natAbs + Nat.size q.den
  max ((Finset.univ : Finset (Fin f.nb)).sup fun b =>
      max ((Finset.univ : Finset (Fin D)).sup fun i => bits ((f.bd b).g i)) (bits (f.bd b).c))
    ((f.pieces.map fun P =>
      max ((Finset.univ : Finset (Fin D × Fin D)).sup fun ij => bits (P.quad.Q ij.1 ij.2))
        (max ((Finset.univ : Finset (Fin D)).sup fun i => bits (P.quad.g i)) (bits P.quad.c))).foldr
      max 0)

end PQObj

/-- Gradient descent `x_{t+1} = x_t − η_t ∇f(x_t)` (§L, p.64), with `η t` the step size of the update
from `x_t` to `x_{t+1}`. -/
noncomputable def gdIter {D : ℕ} (f : PQObj D) (x0 : Fin D → ℝ) (η : ℕ → ℝ) : ℕ → (Fin D → ℝ)
  | 0 => x0
  | t + 1 => gdIter f x0 η t - η t • f.grad (gdIter f x0 η t)

/-- A run is **regular** (§L, p.64: "A regular parameter is one whose run avoids all piece boundaries
through the horizon") when the iterates `x_0, …, x_H` lie on no boundary. -/
def GDRegular {D : ℕ} (f : PQObj D) (x0 : Fin D → ℝ) (η : ℕ → ℝ) (H : ℕ) : Prop :=
  ∀ t ≤ H, f.OffBoundary (gdIter f x0 η t)

/-- The capped stopping cost of the run with threshold `ϑ` on the Euclidean gradient norm. -/
noncomputable def gdCost {D : ℕ} (f : PQObj D) (x0 : Fin D → ℝ) (η : ℕ → ℝ) (ϑ : ℝ) (H : ℕ) : ℕ :=
  stopCost (fun t => Real.sqrt (∑ i, (f.grad (gdIter f x0 η t) i) ^ 2)) ϑ H

end AggCG.Supplement


