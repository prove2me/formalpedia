-- Prove2me | Definitions.Def_SymmetricDomains
-- name    : SymmetricDomains
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:33:15.548757+00:00
-- url     : https://prove2.me/theorems/8c411348-d1a2-4915-b2c8-7e21d0fa8067
-- statement:
--   Affine(n) is complex n-space, realized as functions from Fin n to the complex numbers, and realCoordinates lists the real and imaginary parts of the n coordinates as 2n real numbers. A set V is affine algebraic if it equals the common zero set of some family of complex polynomials in n variables. A set is semialgebraic if it lies in the smallest class of subsets of Affine(n) that contains every set where a real polynomial in the 2n real coordinates vanishes, every set where such a polynomial is strictly positive, and is closed under complement and binary union. A map f from a subset S of Affine(n) to Affine(m) is holomorphic on S if each point of S has an open neighborhood W in Affine(n) and a function F on Affine(n), analytic on W, that agrees with f at all points of S inside W. A Biholomorph between subsets S and T is a homeomorphism S to T such that both the map and its inverse are holomorphic in this sense. A subset S is smooth if every point p of S has a subset W of S, relatively open in S and containing p, together with some m and an open set D in Affine(m), such that W and D are biholomorphic. Finally, IsBoundedSymmetricDomain(D) says that D is open, connected and bounded in Affine(n), and that for every point p of D there is a biholomorphic self-map of D that is an involution, fixes p, and has p as an isolated fixed point, meaning some neighborhood of p in D contains no other fixed point.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SymmetricDomains.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SymmetricDomains.lean; bytes 16..2050
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace Release061

abbrev Affine (n : ℕ) := Fin n → ℂ

def realCoordinates {n : ℕ} (z : Affine n) : Fin n ⊕ Fin n → ℝ :=
  Sum.elim (fun j => (z j).re) (fun j => (z j).im)

def IsAffineAlgebraic {n : ℕ} (V : Set (Affine n)) : Prop :=
  ∃ P : Set (MvPolynomial (Fin n) ℂ),
    V = {z | ∀ p ∈ P, MvPolynomial.eval z p = 0}

inductive IsSemialgebraic {n : ℕ} : Set (Affine n) → Prop
  | zero (p : MvPolynomial (Fin n ⊕ Fin n) ℝ) :
      IsSemialgebraic {z | MvPolynomial.eval (realCoordinates z) p = 0}
  | positive (p : MvPolynomial (Fin n ⊕ Fin n) ℝ) :
      IsSemialgebraic {z | 0 < MvPolynomial.eval (realCoordinates z) p}
  | compl {S : Set (Affine n)} : IsSemialgebraic S → IsSemialgebraic Sᶜ
  | union {S T : Set (Affine n)} :
      IsSemialgebraic S → IsSemialgebraic T → IsSemialgebraic (S ∪ T)

def HolomorphicOnSubset {n m : ℕ} (S : Set (Affine n)) (f : S → Affine m) : Prop :=
  ∀ p : S, ∃ W : Set (Affine n), IsOpen W ∧ (p : Affine n) ∈ W ∧
    ∃ F : Affine n → Affine m, AnalyticOnNhd ℂ F W ∧
      ∀ q : S, (q : Affine n) ∈ W → F q = f q

structure Biholomorph {n m : ℕ} (S : Set (Affine n)) (T : Set (Affine m)) where
  toHomeomorph : S ≃ₜ T
  holomorphic_toFun : HolomorphicOnSubset S (fun p => (toHomeomorph p : Affine m))
  holomorphic_invFun : HolomorphicOnSubset T (fun q => (toHomeomorph.symm q : Affine n))

def IsSmooth {n : ℕ} (S : Set (Affine n)) : Prop :=
  ∀ p : S, ∃ (m : ℕ) (W : Set (Affine n)), W ⊆ S ∧
    IsOpen ((Subtype.val : S → Affine n) ⁻¹' W) ∧ (p : Affine n) ∈ W ∧
    ∃ D : Set (Affine m), IsOpen D ∧ Nonempty (Biholomorph W D)

def IsBoundedSymmetricDomain {n : ℕ} (D : Set (Affine n)) : Prop :=
  IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧
    ∀ p : D, ∃ σ : Biholomorph D D,
      Function.Involutive σ.toHomeomorph ∧ σ.toHomeomorph p = p ∧
      ∃ W : Set D, IsOpen W ∧ p ∈ W ∧
        ∀ q ∈ W, σ.toHomeomorph q = q → q = p



end Release061
end OAI


