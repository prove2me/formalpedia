-- Prove2me | Definitions.Def_KeystoneLadder
-- name    : KeystoneLadder
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:08.182025+00:00
-- url     : https://prove2.me/theorems/23cb74a0-05ea-47f0-bd0a-64596b38038e
-- title:
--   A total projective x-only ladder on a Weierstrass curve
-- statement:
--   The file defines a minimal projective line coordinate $[X:Z]$, equality by cross multiplication, the point at infinity, affine x-coordinates, and the projective x-image of an elliptic-curve point. It also defines raw and total differential addition, homogeneous doubling, Montgomery adjacent-pair states, the binary x-only ladder, affine readout, and the intended division-polynomial pair $[Φ_n(x):Ψ_n(x)^2]$. This is the executable x-coordinate ladder used by the Keystone certificate modules.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.overlappingInstances false

open Polynomial
open WeierstrassCurve
open WeierstrassCurve.Affine

noncomputable section

namespace KeystoneLadder

universe u

variable {k : Type u} [Field k] [DecidableEq k]

/-- Minimal projective x-coordinate over an arbitrary field. -/
public structure P1 (k : Type u) [Zero k] where
  X : k
  Z : k
  not_both_zero : X ≠ 0 ∨ Z ≠ 0

namespace P1

variable [Field k]

/-- Equality in `P¹`, by cross multiplication. -/
@[expose] public def Same (A B : P1 k) : Prop :=
  A.X * B.Z = B.X * A.Z

/-- Convert the bundled nonzero `P¹` representative to Mathlib's `Fin 2` convention. -/
@[expose] public def toVec (A : P1 k) : Fin 2 → k :=
  ![A.X, A.Z]

end P1

variable (E : WeierstrassCurve k)

/-- The point at infinity on the Kummer line. -/
@[expose] public def xInf : P1 k :=
  { X := 1, Z := 0, not_both_zero := Or.inl one_ne_zero }

/-- The affine x-coordinate `[x : 1]`. -/
@[expose] public def xAff (x : k) : P1 k :=
  { X := x, Z := 1, not_both_zero := Or.inr one_ne_zero }

/-- Projective x-coordinate. The group identity maps to `[1 : 0]`. -/
@[expose] public def xRep : E.toAffine.Point → P1 k
  | 0 => xInf
  | Point.some x _ _ => xAff x

/-- `δ = X₁Z₂ - X₂Z₁`. -/
@[expose] public def delta (A B : P1 k) : k :=
  A.X * B.Z - B.X * A.Z

/-- Homogeneous numerator for `x₊ + x₋`. -/
@[expose] public def sumNum (A B : P1 k) : k :=
    2 * A.X * B.X * (A.X * B.Z + B.X * A.Z)
  + E.b₂ * A.X * B.X * A.Z * B.Z
  + E.b₄ * A.Z * B.Z * (A.X * B.Z + B.X * A.Z)
  + E.b₆ * A.Z ^ 2 * B.Z ^ 2

/-- Projective equality on Mathlib's `Fin 2` representatives, oriented as `v = c • u`
for a nonzero scalar `c`. This stronger orientation excludes the zero vector on the right. -/
@[expose] public def SameP1Vec (u v : Fin 2 → k) : Prop :=
  ∃ c : k, c ≠ 0 ∧ v = c • u

namespace SameP1Vec

end SameP1Vec

namespace XOnly

@[expose, simp] public def X (v : Fin 2 → k) : k := v 0
@[expose, simp] public def Z (v : Fin 2 → k) : k := v 1

@[expose] public def xInfVec : Fin 2 → k :=
  ![1, 0]

@[expose] public def xAffVec (x : k) : Fin 2 → k :=
  ![x, 1]

/-- `δ = X₁Z₂ - X₂Z₁` on raw vector representatives. -/
@[expose] public def deltaVec (A B : Fin 2 → k) : k :=
  X A * Z B - X B * Z A

/-- Homogeneous numerator for `x₊ + x₋` on raw vector representatives. -/
@[expose] public def sumNumVec (A B : Fin 2 → k) : k :=
    2 * X A * X B * (X A * Z B + X B * Z A)
  + E.b₂ * X A * X B * Z A * Z B
  + E.b₄ * Z A * Z B * (X A * Z B + X B * Z A)
  + E.b₆ * Z A ^ 2 * Z B ^ 2

/-- Raw x-only differential addition: from `x(A)`, `x(B)`, and `x(A-B)`, produce `x(A+B)`.
It is deliberately unbundled because degeneracies may produce the zero vector. -/
@[expose] public def diffAddVec (A B D : Fin 2 → k) : Fin 2 → k :=
  let δ := deltaVec A B
  ![sumNumVec E A B * Z D - δ ^ 2 * X D, δ ^ 2 * Z D]

/-- Homogeneous numerator for the x-coordinate doubling map. -/
@[expose] public def dupNumH (X Z : k) : k :=
  X ^ 4 - E.b₄ * X ^ 2 * Z ^ 2 - 2 * E.b₆ * X * Z ^ 3 - E.b₈ * Z ^ 4

/-- Homogeneous denominator for the x-coordinate doubling map. -/
@[expose] public def dupDenH (X Z : k) : k :=
  4 * X ^ 3 * Z + E.b₂ * X ^ 2 * Z ^ 2 + 2 * E.b₄ * X * Z ^ 3 + E.b₆ * Z ^ 4

/-- Raw x-only doubling primitive. -/
@[expose] public def doubleVec (A : Fin 2 → k) : Fin 2 → k :=
  ![dupNumH E (X A) (Z A), dupDenH E (X A) (Z A)]

/-- Differential addition with the adjacent-pair degenerate branch made total.
For a genuine adjacent ladder pair, `δ = 0` means the desired sum is the point at infinity. -/
@[expose] public def diffAddOrInfVec (A B D : Fin 2 → k) : Fin 2 → k :=
  if deltaVec A B = 0 then xInfVec else diffAddVec E A B D

/-- Montgomery-pair ladder state: the first component represents `x(mP)` and the second
represents `x((m+1)P)`. -/
@[expose] public def xLadderPair (x : k) : ℕ → (Fin 2 → k) × (Fin 2 → k)
  | 0 => (xInfVec, xAffVec x)
  | 1 => (xAffVec x, doubleVec E (xAffVec x))
  | n + 2 =>
      let N := n + 2
      let S := xLadderPair x (N / 2)
      let A := S.1
      let B := S.2
      let C := diffAddOrInfVec E A B (xAffVec x)
      if Even N then (doubleVec E A, C) else (C, doubleVec E B)
termination_by n => n
decreasing_by
  omega

/-- The x-only ladder representative for `x(nP)`, extracted from the Montgomery pair state. -/
@[expose] public def xLadderRep (x : k) (n : ℕ) : Fin 2 → k :=
  (xLadderPair E x n).1

/-- Affine quotient readout of the x-only ladder. Meaningful when the denominator is nonzero. -/
@[expose] public def xLadder (x : k) (n : ℕ) : k :=
  X (xLadderRep E x n) / Z (xLadderRep E x n)

end XOnly

/-- The intended projective x-coordinate representative `[Φₙ(x), ΨSqₙ(x)]`. -/
@[expose] public def xPair (W : WeierstrassCurve k) (n : ℤ) (x : k) : Fin 2 → k :=
  ![(W.Φ n).eval x, (W.ΨSq n).eval x]

end KeystoneLadder


