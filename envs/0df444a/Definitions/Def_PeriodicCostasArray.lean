-- Prove2me | Definitions.Def_PeriodicCostasArray
-- name    : PeriodicCostasArray
-- status  : Definition
-- author  : @shivm
-- created : 2026-10-04T14:10:24.760732+00:00
-- url     : https://prove2.me/theorems/5f294414-46d5-4ae5-9378-1569c8761695
-- title:
--   Periodic multidimensional Costas arrays (Rubio–Torres)
-- statement:
--   Multidimensional (periodic) Costas arrays in the sense of Rubio–Torres, Definitions 2–4. Write $[n]=\{1,\dots,n\}$, $X=[a_1]\times\cdots\times[a_k]$, $Y=[b_1]\times\cdots\times[b_l]$, $\Lambda=X\times Y$.
--
--   - `IsPermutationArray a b φ`: $k,l\ge1$, all sides $\ge2$, and $\varphi$ is a bijection $X\to Y$.
--   - `dots`: points $(x,y)\in\Lambda$ with $\varphi(x)=y$.
--   - `periodicDots`: points $p\in\mathbb Z^{k+l}$ whose coordinatewise reduction $((p_i-1)\bmod n_i)+1$ is a dot.
--   - `window a b t`: the translate $t+\Lambda$.
--   - `NoRepeatedDifferences D`: for distinct $\alpha,\omega\in D$, the vector $\omega-\alpha$ determines the pair.
--   - `IsCostas`: a permutation array whose dots have no repeated differences.
--   - `IsPeriodicCostas`: Costas, and for every $t$ the periodic dots in `window a b t` have no repeated differences.
--
--   A point is a pair $(x,y)$ of integer vectors; $\varphi$ is a total function whose values off $X$ are unused. Differences are not reduced modulo the sides.
-- source:
--   I. Rubio and J. Torres, Multidimensional Costas Arrays and Their Periodicity, IEEE Trans. Inf. Theory 69(8) (2023) 5032-5040, https://arxiv.org/abs/2208.02378, doi:10.1109/TIT.2023.3264951; Section 2 (pp. 3-4) and Definitions 2-4 (pp. 6, 8)

import Mathlib

namespace PeriodicCostas

/-- The hyper-rectangle `[n_1] × ⋯ × [n_r] ⊆ ℤ^r`, where `[n] = {1, …, n}`. -/
def box {r : ℕ} (n : Fin r → ℕ) : Set (Fin r → ℤ) :=
  {x | ∀ i, 1 ≤ x i ∧ x i ≤ (n i : ℤ)}

/-- `x ↦ x_Λ`: the unique point of `[n_1] × ⋯ × [n_r]` congruent to `x` modulo `n_i`
in every coordinate `i` (for `n_i ≥ 1`). -/
def reduce {r : ℕ} (n : Fin r → ℕ) (x : Fin r → ℤ) : Fin r → ℤ :=
  fun i => (x i - 1) % (n i : ℤ) + 1

/-- The `m`-dimensional permutation array (Definition 2), with `m = k + l`, of size
`a_1 × ⋯ × a_k × b_1 × ⋯ × b_l` defined by `φ : [a_1] × ⋯ × [a_k] → [b_1] × ⋯ × [b_l]`:
every side length is at least `2` and `φ` is a bijection between the two boxes. -/
def IsPermutationArray {k l : ℕ} (a : Fin k → ℕ) (b : Fin l → ℕ)
    (φ : (Fin k → ℤ) → (Fin l → ℤ)) : Prop :=
  1 ≤ k ∧ 1 ≤ l ∧ (∀ i, 2 ≤ a i) ∧ (∀ j, 2 ≤ b j) ∧ Set.BijOn φ (box a) (box b)

/-- The dots of the array: the points `(x, y)` of the index set `Λ = [a] × [b]`
with `φ x = y`. A point of `ℤ^m` is written as a pair `(x, y) ∈ ℤ^k × ℤ^l`. -/
def dots {k l : ℕ} (a : Fin k → ℕ) (b : Fin l → ℕ) (φ : (Fin k → ℤ) → (Fin l → ℤ)) :
    Set ((Fin k → ℤ) × (Fin l → ℤ)) :=
  {p | p.1 ∈ box a ∧ p.2 ∈ box b ∧ φ p.1 = p.2}

/-- The dots of the periodic extension `Ã(α) = A(α_Λ)` to `ℤ^m`. -/
def periodicDots {k l : ℕ} (a : Fin k → ℕ) (b : Fin l → ℕ)
    (φ : (Fin k → ℤ) → (Fin l → ℤ)) : Set ((Fin k → ℤ) × (Fin l → ℤ)) :=
  {p | (reduce a p.1, reduce b p.2) ∈ dots a b φ}

/-- The window `t + Λ` of size `a_1 × ⋯ × a_k × b_1 × ⋯ × b_l` with corner offset `t ∈ ℤ^m`. -/
def window {k l : ℕ} (a : Fin k → ℕ) (b : Fin l → ℕ) (t : (Fin k → ℤ) × (Fin l → ℤ)) :
    Set ((Fin k → ℤ) × (Fin l → ℤ)) :=
  {p | p.1 - t.1 ∈ box a ∧ p.2 - t.2 ∈ box b}

/-- A set of points has no repeated difference vectors: the difference vectors `ω - α`
over ordered pairs `(α, ω)` of distinct points are pairwise distinct. -/
def NoRepeatedDifferences {V : Type*} [AddGroup V] (D : Set V) : Prop :=
  ∀ α ∈ D, ∀ ω ∈ D, ∀ α' ∈ D, ∀ ω' ∈ D,
    α ≠ ω → α' ≠ ω' → ω - α = ω' - α' → α = α' ∧ ω = ω'

/-- Definition 3: an `m`-dimensional Costas array (a permutation array with no repeated
difference vectors). -/
def IsCostas {k l : ℕ} (a : Fin k → ℕ) (b : Fin l → ℕ)
    (φ : (Fin k → ℤ) → (Fin l → ℤ)) : Prop :=
  IsPermutationArray a b φ ∧ NoRepeatedDifferences (dots a b φ)

/-- Definition 4: a periodic Costas array — a Costas array such that every window
`t + Λ` (`t ∈ ℤ^m`) of its periodic extension has no repeated difference vectors. -/
def IsPeriodicCostas {k l : ℕ} (a : Fin k → ℕ) (b : Fin l → ℕ)
    (φ : (Fin k → ℤ) → (Fin l → ℤ)) : Prop :=
  IsCostas a b φ ∧
    ∀ t : (Fin k → ℤ) × (Fin l → ℤ), NoRepeatedDifferences (periodicDots a b φ ∩ window a b t)

end PeriodicCostas


