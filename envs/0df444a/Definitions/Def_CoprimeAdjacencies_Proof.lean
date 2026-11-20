-- Prove2me | Definitions.Def_CoprimeAdjacencies_Proof
-- name    : CoprimeAdjacencies_Proof
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T19:27:14.751714+00:00
-- url     : https://prove2.me/theorems/9ef6b9f4-ba67-49e0-9ad6-3080a71d2cb2
-- title:
--   Proof
-- statement:
--   Definitions and structural lemmas for Proof, from G. Sidoine and contributors's pinned Minimum coprime adjacencies development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/gsidoine/coprime-adjacencies-lean/blob/4ccf4a1d94ccf83473bcacf87ddd9117274ec945/CoprimeAdjacencies/Proof.lean

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace P010
def largePrimes (n : ℕ) : Finset ℕ :=
  n.primesLE \ (n / 2).primesLE
def middlePrimes (n : ℕ) : Finset ℕ :=
  (n / 2).primesLE \ (n / 3).primesLE
def smallWitness : ℕ → List ℕ
  | 1 => [1]
  | 2 => [1, 2]
  | 3 => [1, 2, 3]
  | 4 => [1, 2, 4, 3]
  | 5 => [1, 2, 4, 3, 5]
  | 6 => [1, 2, 4, 6, 3, 5]
  | 7 => [1, 2, 4, 6, 3, 5, 7]
  | 8 => [1, 2, 4, 8, 6, 3, 5, 7]
  | 9 => [1, 2, 4, 8, 6, 3, 9, 5, 7]
  | 10 => [1, 3, 9, 6, 2, 4, 8, 10, 5, 7]
  | 11 => [1, 3, 9, 6, 2, 4, 8, 10, 5, 7, 11]
  | _ => []
def NonCoprimeChain (a : List ℕ) : Prop :=
  List.IsChain (fun x y : ℕ => ¬Nat.Coprime x y) a
def maximalNonCoprimeRuns (a : List ℕ) : List (List ℕ) :=
  a.splitBy (fun x y => decide (¬Nat.Coprime x y))
def isolatedVertices (n : ℕ) : Finset ℕ :=
  insert 1 (largePrimes n)
def primeClass (n p : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter (fun m => Nat.maxPrimeFac m = p)
noncomputable def orderedPrimeClass (n p u v : ℕ) : List ℕ := by
  classical
  exact u :: (((primeClass n p).erase u).erase v).toList ++ [v]
def intermediatePrimes (n : ℕ) : Finset ℕ :=
  (n / 3).primesLE \ (n / 4).primesLE
def evenUnitCount (n : ℕ) : ℕ :=
  pi (n / 4) + (intermediatePrimes n).card / 2
def EvenEnded (a : List ℕ) : Prop :=
  ∃ u v, a.head? = some u ∧ a.getLast? = some v ∧ 2 ∣ u ∧ 2 ∣ v
def packLeafClasses (core : List ℕ) : List ℕ → List (List ℕ)
  | [] => [core]
  | [p] => [[p, 2 * p] ++ core]
  | [p, q] => [[p, 2 * p] ++ core ++ [2 * q, q]]
  | p :: q :: r :: rs =>
      [p, 2 * p, 2 * q, q] :: packLeafClasses core (r :: rs)
def splitPrimePairs : List ℕ → List (ℕ × ℕ) × Option ℕ
  | [] => ([], none)
  | [p] => ([], some p)
  | p :: q :: rest =>
      let split := splitPrimePairs rest
      ((p, q) :: split.1, split.2)
noncomputable def smallEvenUnit (n p : ℕ) : List ℕ :=
  orderedPrimeClass n p (2 * p) (4 * p)
noncomputable def intermediateEvenUnit (n : ℕ) (pq : ℕ × ℕ) : List ℕ :=
  orderedPrimeClass n pq.1 (2 * pq.1) (3 * pq.1) ++
    orderedPrimeClass n pq.2 (3 * pq.2) (2 * pq.2)
noncomputable def threeEvenUnit (n : ℕ) : Option ℕ → List ℕ
  | none => orderedPrimeClass n 3 6 12
  | some p =>
      orderedPrimeClass n 3 6 9 ++
        orderedPrimeClass n p (3 * p) (2 * p)
noncomputable def coreUnits (n : ℕ) : List (List ℕ) := by
  classical
  let mids := splitPrimePairs (intermediatePrimes n).toList
  exact threeEvenUnit n mids.2 ::
      (((n / 4).primesLE.erase 3).toList.map (smallEvenUnit n) ++
        mids.1.map (intermediateEvenUnit n))
noncomputable def corePath (n : ℕ) : List ℕ :=
  (coreUnits n).flatten
noncomputable def classConcat (n : ℕ) (ps : List ℕ) : List ℕ :=
  ps.flatMap (fun p => (primeClass n p).toList)
noncomputable def coreIndices (n : ℕ) : List ℕ :=
  3 :: (((n / 4).primesLE.erase 3).toList ++
    (intermediatePrimes n).toList)
noncomputable def optimalCover (n : ℕ) : List (List ℕ) :=
  [[1]] ++
    (largePrimes n).toList.map (fun p => [p]) ++
    packLeafClasses (corePath n) (middlePrimes n).toList
end P010


