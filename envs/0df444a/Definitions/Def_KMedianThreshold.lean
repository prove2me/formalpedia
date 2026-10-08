-- Prove2me | Definitions.Def_KMedianThreshold
-- name    : KMedianThreshold
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:16.230303+00:00
-- url     : https://prove2.me/theorems/89472eea-11ce-4800-b828-99b1e0a73dc0
-- statement:
--   A metric k-median Instance consists of n points indexed by Fin n, a rational distance function that is nonnegative, vanishes exactly on equal points, is symmetric and satisfies the triangle inequality, a finite set of clients, a finite set of facilities, and a bound k with 1 ≤ k ≤ the number of facilities. encodeNat writes a natural number as a unary-length prefix (as many trues as its binary digit list is long), a false separator, then its binary digits; encodeRat writes a sign bit followed by the encodings of the absolute numerator and the denominator; encodeInstance concatenates the encodings of n and k, the membership bit masks of clients and facilities, and all pairwise distance encodings row by row. For a set S of points, nearest(j,S) is the real-valued minimum distance from client j to a member of S (zero if S is empty), cost(I,S) is the sum of nearest(j,S) over all clients, feasibleSets are the nonempty subsets of facilities of size at most k, and optimum is the minimum cost over feasible sets (zero if there are none). Correct(ε,I,output) says the output list of bits is the membership mask of some feasible facility set S with cost(I,S) ≤ (1 + 2/e + ε)·optimum(I). The complexity section defines FinitePolyTime for a function between encoded types as computability by a Mathlib TM2 Turing machine in polynomial time all of whose work alphabets are finite, and defines languages over bit strings, the class P as languages decided by such a machine, and NP as languages x for which some polynomial p and finitely-alphabeted polynomial-time verifier accept a witness w with length at most p(|x|), using encodePair to encode the pair of input and witness. PNeNP is the defined proposition P ≠ NP, not an established theorem. Finally, FactorCorrect(α,I,output) is like Correct with approximation factor α in place of 1+2/e+ε, and approximationFactors is the set of real α for which some deterministic finitely-alphabeted polynomial-time algorithm maps every instance, with arbitrary clients and facilities, to a feasible facility mask of cost at most α times optimum.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/KMedianThreshold.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/KMedianThreshold.lean; bytes 16..3631
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

section
section
namespace MetricKMedian

structure Instance where
  n : ℕ
  distance : Fin n → Fin n → ℚ
  clients : Finset (Fin n)
  facilities : Finset (Fin n)
  k : ℕ
  distance_nonneg : ∀ i j, 0 ≤ distance i j
  distance_eq_zero : ∀ i j, distance i j = 0 ↔ i = j
  distance_symm : ∀ i j, distance i j = distance j i
  distance_triangle : ∀ i j h, distance i h ≤ distance i j + distance j h
  k_pos : 1 ≤ k
  k_le : k ≤ facilities.card

def encodeNat (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def encodeRat (q : ℚ) : List Bool :=
  [decide (q.num < 0)] ++ encodeNat q.num.natAbs ++ encodeNat q.den

def encodeInstance (I : Instance) : List Bool :=
  encodeNat I.n ++ encodeNat I.k ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.clients)) ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.facilities)) ++
    (List.ofFn (fun i : Fin I.n =>
      (List.ofFn (fun j : Fin I.n => encodeRat (I.distance i j))).flatten)).flatten

noncomputable def nearest (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n)) : ℝ :=
  if h : S.Nonempty then
    (S.image (fun i => (I.distance j i : ℝ))).min' (h.image _)
  else 0

noncomputable def cost (I : Instance) (S : Finset (Fin I.n)) : ℝ :=
  ∑ j ∈ I.clients, nearest I j S

def feasibleSets (I : Instance) : Finset (Finset (Fin I.n)) :=
  I.facilities.powerset.filter (fun S => S.Nonempty ∧ S.card ≤ I.k)

noncomputable def optimum (I : Instance) : ℝ :=
  if h : (feasibleSets I).Nonempty then
    ((feasibleSets I).image (cost I)).min' (h.image _)
  else 0

def Correct (epsilon : ℝ) (I : Instance) (output : List Bool) : Prop :=
  ∃ S : Finset (Fin I.n), S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧
    output = List.ofFn (fun i : Fin I.n => decide (i ∈ S)) ∧
    cost I S ≤ (1 + 2 / Real.exp 1 + epsilon) * optimum I

end MetricKMedian
end
end

namespace MetricKMedian
namespace Complexity
/-- Polynomial-time computation with every physical work alphabet finite. -/
def FinitePolyTime {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) : Prop :=
  ∃ p : Turing.TM2ComputableInPolyTime ea eb f,
    ∀ k : p.tm.K, Finite (p.tm.Γ k)

abbrev Word := List Bool
abbrev Language := Set Word

def encodeBit (b : Bool) : Word := [b]

def encodePair (x : Word × Word) : Word :=
  encodeNat x.1.length ++ x.1 ++ x.2

def P : Set Language := {L | ∃ decideL : Word → Bool,
  FinitePolyTime id encodeBit decideL ∧ ∀ x, decideL x = true ↔ x ∈ L}

def NP : Set Language := {L | ∃ (verify : Word × Word → Bool) (p : Polynomial ℕ),
  FinitePolyTime encodePair encodeBit verify ∧
  ∀ x, x ∈ L ↔ ∃ w : Word, w.length ≤ p.eval x.length ∧ verify (x, w) = true}

/-- Separation of deterministic polynomial time from finite-verifier nondeterministic polynomial time. -/
def PNeNP : Prop := P ≠ NP

end Complexity
/-- An actual nonempty feasible facility set, encoded by its membership mask. -/
def FactorCorrect (α : ℝ) (I : Instance) (output : List Bool) : Prop :=
  ∃ S : Finset (Fin I.n), S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧
    output = List.ofFn (fun i : Fin I.n => decide (i ∈ S)) ∧
    cost I S ≤ α * optimum I

/-- Deterministic polynomial-time approximation factors for arbitrary specified clients and facilities. -/
def approximationFactors : Set ℝ := {α | ∃ algorithm : Instance → List Bool,
  Complexity.FinitePolyTime encodeInstance id algorithm ∧
  ∀ I, FactorCorrect α I (algorithm I)}

end MetricKMedian

namespace MetricKMedian


end MetricKMedian
end OAI


