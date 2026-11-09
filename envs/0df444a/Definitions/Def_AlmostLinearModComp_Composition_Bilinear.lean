-- Prove2me | Definitions.Def_AlmostLinearModComp_Composition_Bilinear
-- name    : AlmostLinearModComp_Composition_Bilinear
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:37.27085+00:00
-- url     : https://prove2.me/theorems/b187c9fc-d3af-4584-a76a-a34f627d13a9
-- title:
--   Bilinear multiplication architecture and arithmetic bound
-- statement:
--   A bilinear program applies a linear transformation to each of its two inputs, multiplies corresponding transformed coordinates, then applies a final linear transformation. All fixed scalars are integers interpreted canonically in the base ring. Validity checks the intermediate rank and all three linear-program interfaces. The cost counts all linear gates and every coordinatewise product.
--
--   For $s\ge1$, the explicit convention for the arithmetic soft bound is
--   $$B(C,k,s)=Cs(1+\log_2(s+2))^k.$$
--   The parameters $C>0$ and $k\in\mathbb N$ are quantified before all varying sizes and rings in Lemma A.1. The definition supplies no fast multiplication or correctness assumption.
-- source:
--   yang zhou, Mingsheng Wang, Almost-Linear Modular Composition over Arbitrary Commutative Rings, STOC 2027 submission #450 (October 2026), Lemma A.1 and its bilinearity paragraph, printed p.11 / PDF p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/450.pdf

import Definitions.Def_AlmostLinearModComp_Composition_Circuits

namespace AlmostLinearModComp.Composition

/-- Bilinear multiplication architecture: two linear transforms, componentwise
products, then a final linear transform. There are no polynomial-operation gates. -/
structure BilinearProgram where
  scalars : List ℤ
  rank : ℕ
  left : LinearProgram
  right : LinearProgram
  finish : LinearProgram

def BilinearProgram.valid (b : BilinearProgram) (inputs outputs : ℕ) : Prop :=
  b.left.valid b.scalars.length inputs b.rank ∧
  b.right.valid b.scalars.length inputs b.rank ∧
  b.finish.valid b.scalars.length b.rank outputs

def BilinearProgram.eval {R : Type*} [CommRing R] (b : BilinearProgram)
    (x y : List R) : List R :=
  let scalars := b.scalars.map (fun z : ℤ => (z : R))
  let u := b.left.eval scalars x
  let v := b.right.eval scalars y
  b.finish.eval scalars (u.zipWith (· * ·) v)

def BilinearProgram.cost (b : BilinearProgram) : ℕ :=
  b.left.cost + b.right.cost + b.rank + b.finish.cost

/-- Explicit logarithmic convention for the Appendix's soft-O bound. -/
noncomputable def arithmeticBound (C : ℝ) (k s : ℕ) : ℝ :=
  C * s * (1 + Real.logb 2 (s + 2)) ^ k

end AlmostLinearModComp.Composition


