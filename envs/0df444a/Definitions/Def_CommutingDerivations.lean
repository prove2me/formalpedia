-- Prove2me | Definitions.Def_CommutingDerivations
-- name    : CommutingDerivations
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:04.477126+00:00
-- url     : https://prove2.me/theorems/c9ac026b-ac30-401d-8676-581e6677fddf
-- statement:
--   For any commutative ring, define S(h,u,v,w) = 2u³v + 3u⁴w + h(v² − 3u²w²) + h²w³ and P(x,y,s) = −2s²x + 3sy² − 3s³y. In the polynomial ring R = ℂ[h,u,v,w], with h,u,v,w the four independent coordinate variables, set x = u³ + hv, y = −u² + hw, s = S(h,u,v,w), p = P(x,y,s), and F = h − p − 1. For every integer n ≥ 4, extendedF is the same polynomial F in n variables, using the first four coordinates and leaving the remaining variables unused. Two indexing bijections combine the n−4 additional coordinates with either four distinguished coordinates to obtain n coordinates, or three distinguished coordinates to obtain n−1 coordinates; in each case the distinguished coordinates come first. For a commutative ring K and a commutative K-algebra A, a K-linear derivation D:A→A is defined to be locally nilpotent when, for every a∈A, some nonnegative integer iterate Dⁿ(a) is zero; the exponent may depend on a.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CommutingDerivations.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CommutingDerivations.lean; bytes 245..1553
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Adjoin.Basic

namespace OAI

noncomputable section

namespace AbhyankarSathaye

def S {B : Type*} [CommRing B] (h u v w : B) : B :=
  2*u^3*v + 3*u^4*w + h*(v^2 - 3*u^2*w^2) + h^2*w^3

def P {B : Type*} [CommRing B] (x y s : B) : B :=
  -2*s^2*x + 3*s*y^2 - 3*s^3*y

abbrev R := MvPolynomial (Fin 4) ℂ

def h : R := MvPolynomial.X 0
def u : R := MvPolynomial.X 1
def v : R := MvPolynomial.X 2
def w : R := MvPolynomial.X 3
def x : R := u^3 + h*v
def y : R := -u^2 + h*w
def s : R := S h u v w
def p : R := P x y s
def F : R := h - p - 1

def fourInclusion {n : ℕ} (hn : 4 ≤ n) (i : Fin 4) : Fin n :=
  ⟨i.val, lt_of_lt_of_le i.isLt hn⟩

def extendedF {n : ℕ} (hn : 4 ≤ n) : MvPolynomial (Fin n) ℂ :=
  MvPolynomial.rename (fourInclusion hn) F

def blocksToAmbient {n : ℕ} (hn : 4 ≤ n) : Fin (n-4) ⊕ Fin 4 ≃ Fin n :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))

def blocksToOutput {n : ℕ} (hn : 4 ≤ n) : Fin (n-4) ⊕ Fin 3 ≃ Fin (n-1) :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))

namespace CommutingDerivations

variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B]

def LocallyNilpotent (D : Derivation K A A) : Prop :=
  ∀ a : A, ∃ n : ℕ, (D : A → A)^[n] a = 0

open MvPolynomial



end CommutingDerivations
end AbhyankarSathaye
end
end OAI


