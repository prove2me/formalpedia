-- Prove2me | Definitions.Def_DepthFive
-- name    : DepthFive
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:07.428875+00:00
-- url     : https://prove2.me/theorems/4652af07-3a24-46f6-b49f-65e9e2d818d9
-- statement:
--   For a commutative semiring K and a natural number n, a depth-five arithmetic circuit uses scalar leaves from K and variable leaves xₜᵢⱼ indexed by triples in {0, …, n−1}³, with assigned leaf degrees zero and one, respectively. Its five gate layers, from the leaves upward, are weighted sums, products, weighted sums, products, and a single weighted output sum; weights lie in K, and input lists may repeat gates. The circuit structure assumes syntactic homogeneity: all leaves entering a bottom sum have its assigned degree; all products entering a middle sum have the same total assigned bottom degree; and all products entering the output have the same total assigned middle degree. Each empty sum is required to have assigned degree zero. These conditions concern every listed input, including inputs with zero coefficients. Evaluation takes place in the polynomial ring K[xₜᵢⱼ], interpreting scalar and variable leaves as the corresponding constants and indeterminates, sums as weighted polynomial sums, and products as polynomial products, with empty sums zero and empty products one. Circuit size counts all leaves and all gates, including the output gate, without separately counting input-list entries or weights. For each t, the matrix in layer t has (i,j)-entry xₜᵢⱼ; imm(K,n) is the (0,0)-entry of the ordered product of these n matrices when n>0, and is zero when n=0. Finally, ceilSqrt(n) is the least integer at least √n, ceilDiv(n,t) is defined by (n+t−1)/t using natural-number arithmetic, and upperGateBound(n) is 2n³+rn²+rn^(t+1)+n^(r−1)+1, where t=ceilSqrt(n) and r=ceilDiv(n,t). Here subtraction is truncated at zero and natural-number division by zero returns zero; the block defines this bound but does not assert that a circuit attains it.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DepthFive.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DepthFive.lean; bytes 16..4030
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators
universe u

namespace Problem335

inductive D5Leaf (K : Type u) (n : ℕ) where
  | scalar : K → D5Leaf K n
  | variable : (Fin n × Fin n × Fin n) → D5Leaf K n

def d5LeafDegree {K : Type u} {n : ℕ} : D5Leaf K n → ℕ
  | D5Leaf.scalar _ => 0
  | D5Leaf.variable _ => 1

structure Depth5Circuit (K : Type u) [CommSemiring K] (n : ℕ) where
  leafCount : ℕ
  leaves : Fin leafCount → D5Leaf K n
  bottomCount : ℕ
  bottomInputs : Fin bottomCount → List (K × Fin leafCount)
  bottomDegree : Fin bottomCount → ℕ
  bottomHomogeneous :
    ∀ i entry, entry ∈ bottomInputs i → d5LeafDegree (leaves entry.2) = bottomDegree i
  bottomEmpty :
    ∀ i, bottomInputs i = [] → bottomDegree i = 0
  lowerCount : ℕ
  lowerInputs : Fin lowerCount → List (Fin bottomCount)
  middleCount : ℕ
  middleInputs : Fin middleCount → List (K × Fin lowerCount)
  middleDegree : Fin middleCount → ℕ
  middleHomogeneous :
    ∀ i entry, entry ∈ middleInputs i →
      ((lowerInputs entry.2).map bottomDegree).sum = middleDegree i
  middleEmpty :
    ∀ i, middleInputs i = [] → middleDegree i = 0
  upperCount : ℕ
  upperInputs : Fin upperCount → List (Fin middleCount)
  outputInputs : List (K × Fin upperCount)
  outputDegree : ℕ
  outputHomogeneous :
    ∀ entry, entry ∈ outputInputs →
      ((upperInputs entry.2).map middleDegree).sum = outputDegree
  outputEmpty :
    outputInputs = [] → outputDegree = 0

def d5LeafValue {K : Type u} [CommSemiring K] {n : ℕ}
    (x : D5Leaf K n) : MvPolynomial (Fin n × Fin n × Fin n) K :=
  match x with
  | D5Leaf.scalar a => MvPolynomial.C a
  | D5Leaf.variable i => MvPolynomial.X i

def bottomValue {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.bottomCount) :
    MvPolynomial (Fin n × Fin n × Fin n) K := by
  classical
  exact ((c.bottomInputs i).map (fun entry =>
    MvPolynomial.C entry.1 * d5LeafValue (c.leaves entry.2))).sum

def lowerValue {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.lowerCount) :
    MvPolynomial (Fin n × Fin n × Fin n) K := by
  classical
  exact ((c.lowerInputs i).map (fun j => bottomValue c j)).prod

def middleValue {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.middleCount) :
    MvPolynomial (Fin n × Fin n × Fin n) K := by
  classical
  exact ((c.middleInputs i).map (fun entry =>
    MvPolynomial.C entry.1 * lowerValue c entry.2)).sum

def upperValue {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) (i : Fin c.upperCount) :
    MvPolynomial (Fin n × Fin n × Fin n) K := by
  classical
  exact ((c.upperInputs i).map (fun j => middleValue c j)).prod

def circuitValue {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) : MvPolynomial (Fin n × Fin n × Fin n) K := by
  classical
  exact (c.outputInputs.map (fun entry =>
    MvPolynomial.C entry.1 * upperValue c entry.2)).sum

def circuitSize {K : Type u} [CommSemiring K] {n : ℕ}
    (c : Depth5Circuit K n) : ℕ :=
  c.leafCount + c.bottomCount + c.lowerCount + c.middleCount + c.upperCount + 1

def immLayer (K : Type u) [CommSemiring K] (n : ℕ) (t : Fin n) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n × Fin n) K) :=
  fun i j => MvPolynomial.X (t, i, j)

def imm (K : Type u) [CommSemiring K] (n : ℕ) :
    MvPolynomial (Fin n × Fin n × Fin n) K := by
  classical
  by_cases h : 0 < n
  · let matrices :
        List (Matrix (Fin n) (Fin n)
          (MvPolynomial (Fin n × Fin n × Fin n) K)) :=
      List.ofFn (fun t : Fin n => immLayer K n t)
    exact matrices.prod ⟨0, h⟩ ⟨0, h⟩
  · exact 0

def ceilSqrt (n : ℕ) : ℕ :=
  Nat.sqrt n + if (Nat.sqrt n) ^ 2 = n then 0 else 1

def ceilDiv (n t : ℕ) : ℕ :=
  (n + t - 1) / t

def upperGateBound (n : ℕ) : ℕ :=
  let t := ceilSqrt n
  let r := ceilDiv n t
  2 * n ^ 3 + r * n ^ 2 + r * n ^ (t + 1) + n ^ (r - 1) + 1



end Problem335
end
end OAI


