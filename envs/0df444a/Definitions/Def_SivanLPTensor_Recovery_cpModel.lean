-- Prove2me | Definitions.Def_SivanLPTensor_Recovery_cpModel
-- name    : SivanLPTensor_Recovery_cpModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T05:29:45.354195+00:00
-- url     : https://prove2.me/theorems/debee339-bdec-4fbb-8d9d-8e88b01c4251
-- title:
--   Finite real CP decompositions, equivalence, and minimum rank
-- statement:
--   Let $m$ be the number of modes, $n_j$ their coordinate dimensions and $r$ the number of terms. A dense real tensor is an array indexed by one coordinate in each mode. A factor family consists of vectors $a_i^{(j)}\in\mathbb R^{n_j}$. Its synthesis is
--   $$T[\alpha]=\sum_{i=1}^r\prod_{j=1}^m a_i^{(j)}[\alpha_j].$$
--   Nonzero factors mean every vector is nonzero. Two decompositions are equivalent when one common bijection of the components and nonzero scalars $c_{ij}$ identify their factors, with $\prod_jc_{ij}=1$ for each component. Unique minimum rank means every decomposition has at least $r$ nonzero terms, and every $r$-term decomposition is equivalent. Competing decompositions have no LP promise.
--   These notions form the general CP interface, independently of the paper-specific condition. Coordinates use mixed-radix order with the first mode varying fastest.
-- source:
--   Shiri Sivan, STOC 2027 submission #1294 (October 2026), §1.1, printed p. 2 / PDF p. 4; §2, printed p. 3 / PDF p. 5

import Mathlib

noncomputable section

namespace SivanLPTensor.Recovery
open scoped BigOperators

/-- Finite dense coordinates, including modes of dimension one. -/
abbrev Tensor {m : ℕ} (n : Fin m → ℕ) := ((j : Fin m) → Fin (n j)) → ℝ
abbrev Factors {m : ℕ} (n : Fin m → ℕ) (r : ℕ) :=
  (j : Fin m) → Fin r → (Fin (n j) → ℝ)

def pureTensor {m : ℕ} {n : Fin m → ℕ}
    (a : (j : Fin m) → Fin (n j) → ℝ) : Tensor n :=
  fun α => ∏ j, a j (α j)

def synthesis {m r : ℕ} {n : Fin m → ℕ} (a : Factors n r) : Tensor n :=
  fun α => ∑ i, pureTensor (fun j => a j i) α

def NonzeroFactors {m r : ℕ} {n : Fin m → ℕ} (a : Factors n r) : Prop :=
  ∀ j i, a j i ≠ 0

/-- One shared permutation and compensating, nonzero component scalings. -/
def Equivalent {m r s : ℕ} {n : Fin m → ℕ}
    (a : Factors n r) (b : Factors n s) : Prop :=
  ∃ σ : Fin s ≃ Fin r, ∃ c : Fin s → Fin m → ℝ,
    (∀ i j, c i j ≠ 0) ∧ (∀ i, ∏ j, c i j = 1) ∧
    ∀ j i, b j i = c i j • a j (σ i)

/-- Minimum length and uniqueness against arbitrary nonzero decompositions. -/
def UniqueRank {m r : ℕ} {n : Fin m → ℕ} (a : Factors n r) : Prop :=
  (∀ (s : ℕ) (b : Factors n s), NonzeroFactors b →
    synthesis b = synthesis a → r ≤ s) ∧
  ∀ b : Factors n r, NonzeroFactors b → synthesis b = synthesis a → Equivalent a b

def inputSize {m : ℕ} (n : Fin m → ℕ) : ℕ := ∏ j, n j

/-- Deterministic mixed-radix order, first mode varying fastest. -/
def tensorCoordinates {m : ℕ} (n : Fin m → ℕ) : List ((j : Fin m) → Fin (n j)) :=
  if hn : ∀ j, 0 < n j then
    (List.range (inputSize n)).map (fun t j =>
      ⟨(t / (∏ k ∈ Finset.univ.filter (fun k : Fin m => k < j), n k)) % n j,
        Nat.mod_lt _ (hn j)⟩)
  else []

end SivanLPTensor.Recovery


