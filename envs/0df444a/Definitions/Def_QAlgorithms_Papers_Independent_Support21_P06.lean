-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support21_P06
-- name    : QAlgorithms_Papers_Independent_Support21_P06
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T03:37:05.932912+00:00
-- url     : https://prove2.me/theorems/034dcd8b-2d2d-46ff-b34f-c6df9e8a519e
-- title:
--   Definitions for Skew shape representations are irreducible
-- statement:
--   The objects the formalized statements of *Skew shape representations are irreducible* (arXiv:math/0401326) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `GenericParameter`: The standing parameter convention (math/0401326v2, PDF p.4).
--   - `simplePerm`: The paper's simple transposition s_(i+1), with Lean positions starting at zero.
--   - `permuteWeight`: Permutations act by (w t)_j = t_(w^(-1)(j)) (PDF p.8).
--   - `TorusWeight`: The torus consists of nonzero coordinates (PDF p.8).
--   - `AffineAction`: An affine Hecke representation by its generating linear operators (PDF pp.3–4). These are precisely the quadratic, braid, commuting, invertible-X and mixed relations; no spectral, intertwiner, or classification conclusion is assumed. The finite-dimensional hypothesis, when needed, is supplied to the theorem.
--   - `InWeightSpace`: Membership in the ordinary affine-Hecke weight space, including zero (PDF p.8). The accepted Renew46.P26.IsWeightVector instead requires a nonzero vector and a symmetric-group YJM representation, so it cannot encode this predicate.
--   - `IsGeneralizedWeightVector`: Membership in the joint generalized weight space (PDF p.8). The exponent may depend on the coordinate and the vector.
--   - `differenceInverse`: The finite geometric-series realization of (x_b-x_a)^(-1) on M_t^gen (PDF p.9). Write D=x_b-x_a, delta=t_b-t_a and N=D-delta I. Then D^(-1)=delta^(-1) sum_(k<2 dim V) (-delta^(-1) N)^k on that space. This is an explicit ambient endomorphism, not a Laurent-algebra inverse. Outside the stated generalized weight space it has no inverse specification.
--   - `tauGeneralized`: The local generalized-weight intertwiner, with the denominator orientation x_(i+1)-x_i from Proposition 3.2 (PDF pp.8–9).
--   - `wordPerm`: Product of simple permutations in written, left-to-right order (PDF p.4).
--   - `WordDefined`: Every local intertwiner must have unequal adjacent coordinates at the weight determined by its suffix (PDF pp.8–10).
--   - `tauGeneralizedWord`: A product of local operators, evaluated at suffix-permuted weights. The rightmost operator acts first (PDF pp.8–10).
--   - `tauWeight`: The ordinary-weight specialization of the local fraction (PDF p.10). It is defined by the scalar expression, and has its weight-space meaning only when t_i differs from t_(i+1). No finite-dimensionality is imposed here.
--   - `tauSquareScalar`: The scalar square in (3.7b) (PDF p.10).
--   - `FiniteHeckeFree`: Free finite Hecke generators; these are not the degenerate Hecke generators in the accepted Renew46.P26 module (PDF p.4).
--   - `freeT`: Generator in the free algebra (PDF p.4).
--   - `FiniteHeckeRelations`: The finite Hecke algebra's exact defining relations (PDF p.4).
--   - `FiniteHecke`: The presented finite (Iwahori) Hecke algebra, with no assumed basis theorem (PDF p.4).
--   - `heckeT`: Actual quotient generator (PDF p.4).
--   - `permLength`: Coxeter length as the actual number of inversions (PDF p.4).
--   - `IsReducedWord`: A reduced expression: its adjacent swaps multiply to w and its length is the inversion count (PDF p.4).
--   - `ReducedExpressions`: An arbitrary family of reduced expressions, an auxiliary choice of coordinates for T_w rather than any intertwiner-independence assumption. Every finite symmetric permutation has such an expression; Mathlib's Perm.mclosure_swap_castSucc_succ records the adjacent-generator fact.
--   - `heckeWord`: T-word product in the quotient (PDF p.4).
--   - `tauEvaluatedWord`: The evaluated intertwiner product, computed with suffix-permuted weights as in (3.3)–(3.5), PDF pp.9–10. No word-independence is built into it.
--   - `progressionWeight`: The geometric-progression weight of Proposition 3.6 (PDF p.10).
-- source:
--   Skew shape representations are irreducible, arXiv:math/0401326v2, https://arxiv.org/abs/math/0401326v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P06

open scoped BigOperators

open QAlgorithms.Papers.Independent.Renew46.P26 (Adjacent nextPosition)

attribute [local instance] Classical.propDecidable

/-- The standing parameter convention (math/0401326v2, PDF p.4). -/
def GenericParameter (q : ℂ) : Prop :=
  q ≠ 0 ∧ ∀ k : ℕ, 0 < k → q ^ k ≠ 1

/-- The paper's simple transposition s_(i+1), with Lean positions starting at zero. -/
def simplePerm {n : ℕ} (i : Adjacent n) : Equiv.Perm (Fin n) :=
  Equiv.swap i.val (nextPosition i)

/-- Permutations act by (w t)_j = t_(w^(-1)(j)) (PDF p.8). -/
def permuteWeight {n : ℕ} (w : Equiv.Perm (Fin n)) (t : Fin n → ℂ) : Fin n → ℂ :=
  fun j => t (w.symm j)

/-- The torus consists of nonzero coordinates (PDF p.8). -/
def TorusWeight {n : ℕ} (t : Fin n → ℂ) : Prop :=
  ∀ j, t j ≠ 0

/-- An affine Hecke representation by its generating linear operators (PDF pp.3–4).
These are precisely the quadratic, braid, commuting, invertible-X and mixed
relations; no spectral, intertwiner, or classification conclusion is assumed.
The finite-dimensional hypothesis, when needed, is supplied to the theorem. -/
structure AffineAction (n : ℕ) (q : ℂ) (V : Type*)
    [AddCommGroup V] [Module ℂ V] where
  x : Fin n → Module.End ℂ V
  xInv : Fin n → Module.End ℂ V
  t : Adjacent n → Module.End ℂ V
  inverse_left : ∀ j, xInv j * x j = 1
  inverse_right : ∀ j, x j * xInv j = 1
  x_commute : ∀ j k, x j * x k = x k * x j
  quadratic : ∀ i, t i * t i = (q - q⁻¹) • t i + 1
  distant : ∀ i j, (i.val.val + 1 < j.val.val ∨ j.val.val + 1 < i.val.val) →
    t i * t j = t j * t i
  braid : ∀ i j, j.val.val = i.val.val + 1 →
    t i * t j * t i = t j * t i * t j
  mixed : ∀ i j, j ≠ i.val → j ≠ nextPosition i → x j * t i = t i * x j
  conjugation : ∀ i, t i * x i.val * t i = x (nextPosition i)

/-- Membership in the ordinary affine-Hecke weight space, including zero (PDF p.8).
The accepted Renew46.P26.IsWeightVector instead requires a nonzero vector and
a symmetric-group YJM representation, so it cannot encode this predicate. -/
def InWeightSpace {n : ℕ} {q : ℂ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : AffineAction n q V) (t : Fin n → ℂ) (m : V) : Prop :=
  ∀ j, A.x j m = t j • m

/-- Membership in the joint generalized weight space (PDF p.8).
The exponent may depend on the coordinate and the vector. -/
def IsGeneralizedWeightVector {n : ℕ} {q : ℂ} {V : Type*}
    [AddCommGroup V] [Module ℂ V] (A : AffineAction n q V)
    (t : Fin n → ℂ) (m : V) : Prop :=
  ∀ j, ∃ k : ℕ, 0 < k ∧ ((A.x j - t j • (1 : Module.End ℂ V)) ^ k) m = 0

/-- The finite geometric-series realization of (x_b-x_a)^(-1) on M_t^gen
(PDF p.9). Write D=x_b-x_a, delta=t_b-t_a and N=D-delta I. Then
D^(-1)=delta^(-1) sum_(k<2 dim V) (-delta^(-1) N)^k on that space.
This is an explicit ambient endomorphism, not a Laurent-algebra inverse.
Outside the stated generalized weight space it has no inverse specification. -/
def differenceInverse {n : ℕ} {q : ℂ} {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : AffineAction n q V) (t : Fin n → ℂ) (a b : Fin n) : Module.End ℂ V :=
  let delta := t b - t a
  let nilpart := A.x b - A.x a - delta • (1 : Module.End ℂ V)
  delta⁻¹ • ∑ k ∈ Finset.range (2 * Module.finrank ℂ V), (-delta⁻¹ • nilpart) ^ k

/-- The local generalized-weight intertwiner, with the denominator orientation
x_(i+1)-x_i from Proposition 3.2 (PDF pp.8–9). -/
def tauGeneralized {n : ℕ} {q : ℂ} {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : AffineAction n q V) (t : Fin n → ℂ) (i : Adjacent n) : Module.End ℂ V :=
  A.t i - (q - q⁻¹) • (A.x (nextPosition i) * differenceInverse A t i.val (nextPosition i))

/-- Product of simple permutations in written, left-to-right order (PDF p.4). -/
def wordPerm {n : ℕ} (l : List (Adjacent n)) : Equiv.Perm (Fin n) :=
  (l.map simplePerm).prod

/-- Every local intertwiner must have unequal adjacent coordinates at the
weight determined by its suffix (PDF pp.8–10). -/
def WordDefined {n : ℕ} : List (Adjacent n) → (Fin n → ℂ) → Prop
  | [], _ => True
  | i :: l, t =>
      let s := permuteWeight (wordPerm l) t
      s i.val ≠ s (nextPosition i) ∧ WordDefined l t

/-- A product of local operators, evaluated at suffix-permuted weights.
The rightmost operator acts first (PDF pp.8–10). -/
def tauGeneralizedWord {n : ℕ} {q : ℂ} {V : Type*}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (A : AffineAction n q V) : List (Adjacent n) → (Fin n → ℂ) → Module.End ℂ V
  | [], _ => 1
  | i :: l, t =>
      tauGeneralized A (permuteWeight (wordPerm l) t) i * tauGeneralizedWord A l t

/-- The ordinary-weight specialization of the local fraction (PDF p.10).
It is defined by the scalar expression, and has its weight-space meaning only
when t_i differs from t_(i+1). No finite-dimensionality is imposed here. -/
def tauWeight {n : ℕ} {q : ℂ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : AffineAction n q V) (t : Fin n → ℂ) (i : Adjacent n) : Module.End ℂ V :=
  A.t i - ((q - q⁻¹) * t (nextPosition i) / (t (nextPosition i) - t i.val)) •
    (1 : Module.End ℂ V)

/-- The scalar square in (3.7b) (PDF p.10). -/
def tauSquareScalar {n : ℕ} (q : ℂ) (t : Fin n → ℂ) (i : Adjacent n) : ℂ :=
  ((q * t (nextPosition i) - q⁻¹ * t i.val) *
    (q * t i.val - q⁻¹ * t (nextPosition i))) /
    ((t (nextPosition i) - t i.val) * (t i.val - t (nextPosition i)))

/-- Free finite Hecke generators; these are not the degenerate Hecke generators
in the accepted Renew46.P26 module (PDF p.4). -/
abbrev FiniteHeckeFree (n : ℕ) := FreeAlgebra ℂ (Adjacent n)

/-- Generator in the free algebra (PDF p.4). -/
def freeT {n : ℕ} (i : Adjacent n) : FiniteHeckeFree n := FreeAlgebra.ι ℂ i

/-- The finite Hecke algebra's exact defining relations (PDF p.4). -/
def FiniteHeckeRelations (n : ℕ) (q : ℂ) (x y : FiniteHeckeFree n) : Prop :=
  (∃ i : Adjacent n,
    x = freeT i * freeT i ∧ y = (q - q⁻¹) • freeT i + 1) ∨
  (∃ i j : Adjacent n,
    (i.val.val + 1 < j.val.val ∨ j.val.val + 1 < i.val.val) ∧
    x = freeT i * freeT j ∧ y = freeT j * freeT i) ∨
  (∃ i j : Adjacent n, j.val.val = i.val.val + 1 ∧
    x = freeT i * freeT j * freeT i ∧ y = freeT j * freeT i * freeT j)

/-- The presented finite (Iwahori) Hecke algebra, with no assumed basis theorem
(PDF p.4). -/
abbrev FiniteHecke (n : ℕ) (q : ℂ) := RingQuot (FiniteHeckeRelations n q)

/-- Actual quotient generator (PDF p.4). -/
def heckeT {n : ℕ} (q : ℂ) (i : Adjacent n) : FiniteHecke n q :=
  RingQuot.mkAlgHom ℂ (FiniteHeckeRelations n q) (freeT i)

/-- Coxeter length as the actual number of inversions (PDF p.4). -/
def permLength {n : ℕ} (w : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun p => p.1 < p.2 ∧ w p.2 < w p.1)).card

/-- A reduced expression: its adjacent swaps multiply to w and its length
is the inversion count (PDF p.4). -/
def IsReducedWord {n : ℕ} (w : Equiv.Perm (Fin n)) (l : List (Adjacent n)) : Prop :=
  wordPerm l = w ∧ l.length = permLength w

/-- An arbitrary family of reduced expressions, an auxiliary choice of
coordinates for T_w rather than any intertwiner-independence assumption.
Every finite symmetric permutation has such an expression; Mathlib's
Perm.mclosure_swap_castSucc_succ records the adjacent-generator fact. -/
abbrev ReducedExpressions (n : ℕ) :=
  ∀ w : Equiv.Perm (Fin n), {l : List (Adjacent n) // IsReducedWord w l}

/-- T-word product in the quotient (PDF p.4). -/
def heckeWord {n : ℕ} (q : ℂ) (l : List (Adjacent n)) : FiniteHecke n q :=
  (l.map (heckeT q)).prod

/-- The evaluated intertwiner product, computed with suffix-permuted weights
as in (3.3)–(3.5), PDF pp.9–10. No word-independence is built into it. -/
def tauEvaluatedWord {n : ℕ} (q : ℂ) :
    List (Adjacent n) → (Fin n → ℂ) → FiniteHecke n q
  | [], _ => 1
  | i :: l, t =>
      let s := permuteWeight (wordPerm l) t
      (heckeT q i - algebraMap ℂ (FiniteHecke n q)
        ((q - q⁻¹) * s (nextPosition i) / (s (nextPosition i) - s i.val))) *
        tauEvaluatedWord q l t

/-- The geometric-progression weight of Proposition 3.6 (PDF p.10). -/
def progressionWeight {n : ℕ} (q a : ℂ) : Fin n → ℂ :=
  fun j => a * q ^ (2 * j.val)

/-- The empty word is the identity, independent of q and t. -/
example {n : ℕ} (q : ℂ) (t : Fin n → ℂ) :
    tauEvaluatedWord q ([] : List (Adjacent n)) t = 1 := by
  rfl

/-- All coordinate weights include zero as a vector; nonzero must be a separate
hypothesis in the final clause of (3.7). -/
example {n : ℕ} {q : ℂ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : AffineAction n q V) (t : Fin n → ℂ) : InWeightSpace A t 0 := by
  intro j
  simp

/-- On one letter, the unique reduced expression is empty, so the longest
intertwiner has the source normalization 1. -/
example : IsReducedWord (1 : Equiv.Perm (Fin 1)) [] := by
  constructor
  · rfl
  · change 0 = ((Finset.univ : Finset (Fin 1 × Fin 1)).filter
      (fun p => p.1 < p.2 ∧ p.2 < p.1)).card
    symm
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro p _ hp
    exact lt_asymm hp.1 hp.2

end QAlgorithms.Papers.Independent.Support21.P06


