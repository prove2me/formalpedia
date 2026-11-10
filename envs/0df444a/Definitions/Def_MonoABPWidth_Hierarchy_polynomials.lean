-- Prove2me | Definitions.Def_MonoABPWidth_Hierarchy_polynomials
-- name    : MonoABPWidth_Hierarchy_polynomials
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T08:14:55.650043+00:00
-- url     : https://prove2.me/theorems/aac19433-ea84-47e4-b476-8c36011443fd
-- title:
--   Monotone polynomials and nonnegative affine labels
-- statement:
--   Let $\sigma$ be the variable set and $\mathbb R[\sigma]$ its polynomial ring. A polynomial is monotone when all its real coefficients are nonnegative, and homogeneous when every monomial of its support has the same total degree. The zero polynomial is both monotone and homogeneous. An affine label consists of a nonnegative real constant $c$ and finitely supported nonnegative real coefficients $(a_x)_{x\in\sigma}$, representing
--   $$
--   \ell=c+\sum_{x\in\sigma}a_x x.
--   $$
--   The single-term predicate means that the polynomial is a nonnegative constant or a nonnegative multiple of one variable. It includes zero. This interface permits arbitrary affine sums in the original program; the single-term restriction is a separate predicate used only in simplified witnesses.
-- source:
--   Julian Dörfler, Alexander Rogovskyy, A Width Hierarchy of Monotone Algebraic Branching Programs, STOC 2027 submission #927 (October 2026), §2.1–2.2, pp.3–4, PDF4–5; Definition A.1(3), p.27, PDF28

import Mathlib

namespace MonoABPWidth.Hierarchy

/-- §2.1, p.3: nonnegative real coefficients, including the zero polynomial. -/
def MonotonePolynomial {σ : Type} (f : MvPolynomial σ ℝ) : Prop :=
  ∀ m : σ →₀ ℕ, 0 ≤ f.coeff m

/-- §2.1: all support monomials have one common total degree; zero is homogeneous. -/
def Homogeneous {σ : Type} (f : MvPolynomial σ ℝ) : Prop :=
  ∃ q : ℕ, f.IsHomogeneous q

/-- An arbitrary nonnegative affine form; the variable coefficients have finite support. -/
structure AffineLabel (σ : Type) where
  constant : NNReal
  linear : σ →₀ NNReal

/-- The actual polynomial carried by an affine edge label. -/
noncomputable def AffineLabel.poly {σ : Type} (l : AffineLabel σ) : MvPolynomial σ ℝ :=
  MvPolynomial.C (l.constant : ℝ) +
    l.linear.sum (fun x c => MvPolynomial.C (c : ℝ) * MvPolynomial.X x)

/-- Definition A.1(3): a constant or a scalar multiple of one variable, including zero. -/
def SingleTerm {σ : Type} (f : MvPolynomial σ ℝ) : Prop :=
  (∃ c : NNReal, f = MvPolynomial.C (c : ℝ)) ∨
    ∃ (c : NNReal) (x : σ), f = MvPolynomial.C (c : ℝ) * MvPolynomial.X x

end MonoABPWidth.Hierarchy


