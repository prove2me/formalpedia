-- Prove2me | Definitions.Def_FourBlockIP_FPT_ValueFunctions
-- name    : FourBlockIP_FPT_ValueFunctions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:04.543382+00:00
-- url     : https://prove2.me/theorems/6c0ae823-1a35-42fd-aa2e-639f9d0a850a
-- title:
--   Extended-real integer-program value functions and identity augmentation
-- statement:
--   For an integer matrix $A$, separable extended convex objective $f$, offset $r$ and natural dilation $M$, define
--
--   $$h(z)=\inf\{f(x):Ax=r+Mz,\ x\in\mathbb Z^n\}.$$
--
--   The infimum is taken in $\mathbb R\cup\{-\infty,+\infty\}$: an empty feasible image gives $+\infty$, and an image unbounded below gives $-\infty$. Identity augmentation appends the columns of the identity after the columns of $A$. Everywhere finiteness means that the undilated value function is a finite real number at every integer right-hand side.
--
--   This is the common value function of Lemma 4 and equations (5), (8); the latter finiteness predicate records the regime required in the paragraph preceding Lemma 7.
-- source:
--   Martin Koutecký, Alexandra Lassota, Koen Ligthart, 4-Block Integer Programming is in FPT, STOC 2027 submission #392 (October 2026), p. 6, value function and Lemma 4; p. 7, (5); p. 8, (8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/392.pdf

import Mathlib
import Definitions.Def_FourBlockIP_FPT_Convexity

namespace FourBlockIP.FPT

/-- The integer-program value function, p. 6. Infimum over lattice solutions:
empty feasible image gives +∞, unbounded below gives -∞. -/
noncomputable def valueFn {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (f : SepConvexExt n) (r : Fin m → ℤ) (M : ℕ) (z : Fin m → ℤ) : EReal :=
  sInf {v | ∃ x : Fin n → ℤ,
    (fun i => ∑ j, A i j * x j) = r + M • z ∧ v = f.eval (castVec x)}

/-- Horizontal concatenation [A,I], columns of A first. -/
def augment {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin m) (Fin (n + m)) ℤ := fun i j =>
  if h : j.val < n then A i ⟨j.val,h⟩ else if j.val - n = i.val then 1 else 0

/-- Finiteness of (8), on every integer right-hand side, before offset/dilation. -/
def EverywhereFinite {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (f : SepConvexExt n) : Prop :=
  ∀ b : Fin m → ℤ, ∃ v : ℝ, valueFn A f b 0 0 = (v : EReal)

end FourBlockIP.FPT


