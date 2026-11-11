-- Prove2me | Definitions.Def_SelectedSubset3SUM_Integer_Data
-- name    : SelectedSubset3SUM_Integer_Data
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:50:29.338225+00:00
-- url     : https://prove2.me/theorems/5666ff5a-87fa-4c93-a153-7f1c4e533254
-- title:
--   Ranked weighted subset inputs and integer sumset queries
-- statement:
--   For a natural universe size $d$, a ranked input contains two sparse lists of weighted subsets of $[d]$ and a list of query subsets. Validity requires distinct support keys, distinct queries, input rank $t$, query rank $2t$, $2t\le d$, and total support size at most the supplied upper bound $n$. The coefficient type can be $\mathbb R$ or $\mathbb Z$; missing keys have weight zero. The selected value is
--
--   $$ (f\star g)(X)=\sum_{U\subseteq X} f(U)g(X\setminus U). $$
--
--   Real zeta, covering-product and partial-zeta formulas are defined directly. The cumulative binomial counts, subset masks and explicit sparse input streams provide their combinatorial and input-size conventions.
--
--   An integer sumset input consists of three arbitrary-order lists $A,B,C$. Its validity requires that each list is duplicate-free and each number is in $[N^\kappa]$, where $N=|A|+|B|$ and $\kappa$ is fixed. The real number $\widehat n$ is exactly $\sqrt{|A||B|}$; membership means an equality of original natural-number sums, with no distinctness condition across the lists. The definitions also specify the real logarithms and dimension used by Theorem 2.3, affine modular hashing, bit positions and bad residue buckets. The latter formulas are mathematical objects, not unit-cost machine primitives.
--
--   These interfaces retain all input orders, arbitrary imbalance, zero real weights and empty families. They supply shared semantics for the three algorithmic targets.
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, STOC 2027 submission #1421 (October 2026), Problem 2.1 and Theorem 2.2, p.5; §2.2 and Theorem 2.3, pp.6–9, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1421.pdf

import Mathlib

namespace SelectedSubset3SUM.Integer

/-! Chan--Itakura--Ma--Yu, STOC 2027 submission #1421 (October 2026),
§2 pp.4--9. Lists are arbitrary-order presentations of finite sets, not sorted-input promises.
Real and integer coefficient spaces share the combinatorial input, not a precision restriction. -/

structure RankedData (R : Type) (d : ℕ) where
  left : List (Finset (Fin d) × R)
  right : List (Finset (Fin d) × R)
  queries : List (Finset (Fin d))

def RankedData.Valid {R : Type} {d : ℕ} (I : RankedData R d) (n t : ℕ) : Prop :=
  2 * t ≤ d ∧ I.left.length + I.right.length ≤ n ∧
  (I.left.map Prod.fst).Nodup ∧ (I.right.map Prod.fst).Nodup ∧ I.queries.Nodup ∧
  (∀ u ∈ I.left, u.1.card = t) ∧ (∀ u ∈ I.right, u.1.card = t) ∧
  (∀ X ∈ I.queries, X.card = 2 * t)

def sparseValue {R : Type} [Zero R] {d : ℕ}
    (rows : List (Finset (Fin d) × R)) (X : Finset (Fin d)) : R :=
  ((rows.find? (fun u => u.1 == X)).map Prod.snd).getD 0

def convolution {R : Type} [CommRing R] {d : ℕ}
    (I : RankedData R d) (X : Finset (Fin d)) : R :=
  ∑ A ∈ X.powerset, sparseValue I.left A * sparseValue I.right (X \ A)

def zeta {d : ℕ} (f : Finset (Fin d) → ℝ) (X : Finset (Fin d)) : ℝ :=
  ∑ S ∈ X.powerset, f S

def coveringProduct {d : ℕ} (f g : Finset (Fin d) → ℝ)
    (X : Finset (Fin d)) : ℝ :=
  ∑ A ∈ X.powerset, ∑ B ∈ X.powerset, if A ∪ B = X then f A * g B else 0

def partialZeta {d : ℕ} (f : Finset (Fin d) → ℝ) (i : ℕ)
    (X : Finset (Fin d)) : ℝ :=
  ∑ S ∈ X.powerset, if (S.filter fun j => j.val < i) =
    (X.filter fun j => j.val < i) then f S else 0

def lowerBinomial (d s : ℕ) : ℕ := ∑ j ∈ Finset.range (s + 1), d.choose j

def upperBinomial (r s : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (r + 1), if s ≤ j then r.choose j else 0

def mask {d : ℕ} (X : Finset (Fin d)) : ℕ := ∑ j ∈ X, 2 ^ j.val

def rankedKeys {R : Type} {d : ℕ} (n t s : ℕ) (I : RankedData R d) : List ℤ :=
  ([n, d, t, s, I.left.length, I.right.length, I.queries.length].map Int.ofNat) ++
    (I.left.map fun u => (mask u.1 : ℤ)) ++
    (I.right.map fun u => (mask u.1 : ℤ)) ++
    (I.queries.map fun X => (mask X : ℤ))

def rankedScalars {d : ℕ} (I : RankedData ℝ d) : List ℝ :=
  I.left.map Prod.snd ++ I.right.map Prod.snd

def rankedIntegers {d : ℕ} (n t s : ℕ) (I : RankedData ℤ d) : List ℤ :=
  rankedKeys n t s I ++ I.left.map Prod.snd ++ I.right.map Prod.snd

def IntegerWeights {d : ℕ} (I : RankedData ℤ d) (n κ : ℕ) : Prop :=
  ∀ u ∈ I.left ++ I.right, u.2.natAbs ≤ (max 2 n) ^ κ

def subsetCost (n d t s q : ℕ) : ℝ :=
  n + (lowerBinomial d s : ℝ) + q * (upperBinomial (2 * t) s : ℝ)

structure SumInput where
  A : List ℕ
  B : List ℕ
  C : List ℕ

def SumInput.N (I : SumInput) : ℕ := I.A.length + I.B.length

noncomputable def SumInput.nhat (I : SumInput) : ℝ :=
  Real.sqrt (I.A.length * I.B.length : ℕ)

def SumInput.Valid (I : SumInput) (κ : ℕ) : Prop :=
  I.A.Nodup ∧ I.B.Nodup ∧ I.C.Nodup ∧
  ∀ x ∈ I.A ++ I.B ++ I.C, x < I.N ^ κ

def SumInput.words (I : SumInput) : List ℤ :=
  ([I.A.length, I.B.length, I.C.length].map Int.ofNat) ++
    (I.A.map Int.ofNat) ++ (I.B.map Int.ofNat) ++ (I.C.map Int.ofNat)

def SumInput.answer (I : SumInput) (c : ℕ) : Prop :=
  ∃ a ∈ I.A, ∃ b ∈ I.B, a + b = c

def SumInput.EmptySide (I : SumInput) : Prop := I.A = [] ∨ I.B = []

noncomputable def lg (x : ℝ) : ℝ := Real.log x / Real.log 2

noncomputable def reductionDimension (I : SumInput) (t : ℕ) : ℕ :=
  ⌈(t : ℝ) + lg I.nhat + lg (lg I.N) + 1⌉₊

def affineHash (p ξ α x : ℕ) : ℕ := (x * ξ + α) % p

def bitPositions (d x : ℕ) : Finset (Fin d) :=
  Finset.univ.filter fun j => x.testBit j.val

def badBucket (A : List ℕ) (p a : ℕ) : Prop :=
  a ∈ A ∧ ∃ a' ∈ A, a' ≠ a ∧ a' % p = a % p

end SelectedSubset3SUM.Integer


