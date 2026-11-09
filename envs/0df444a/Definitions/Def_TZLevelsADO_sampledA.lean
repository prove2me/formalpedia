-- Prove2me | Definitions.Def_TZLevelsADO_sampledA
-- name    : TZLevelsADO_sampledA
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:50:25.609226+00:00
-- url     : https://prove2.me/theorems/4a79b492-db18-4d66-8f49-6752cdfc1771
-- title:
--   The randomly sampled Thorup–Zwick hierarchy and its law
-- statement:
--   Let $n \ge 1$, $k \ge 1$ and fix a vertex $v_0$. Draw one independent coin $\omega(i, v)$ for every level $i \in [k]$ and vertex $v$, equal to $1$ with probability $n^{-1/k}$. The **sampled hierarchy** is
--   $$A_0 = V, \qquad A_{i+1} = \{ v \in A_i : \omega(i+1, v) = 1 \} \cup \{v_0\} \quad (0 \le i < k-1), \qquad A_i = \emptyset \quad (i \ge k).$$
--   So each $A_{i+1}$ keeps each vertex of $A_i$ with probability $n^{-1/k}$, and the fixed vertex $v_0$ is added to $A_1, \dots, A_{k-1}$, so that $A_{k-1} \neq \emptyset$. For every outcome it is a Thorup–Zwick hierarchy.
--
--   This is the random hierarchy of §2 of the paper, used by the bunch-size bound (Lemma 4) and hence by the time and space bounds of Theorem 1.
--
--   **Formalization Note** The level-$0$ coins are never read. The probability $n^{-1/k} \in [0,1]$ is passed as a point of the unit interval.
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), §2 "The Thorup–Zwick hierarchy", p.7 (PDF p.8)

import Mathlib
import Definitions.Def_TZLevelsADO_Hierarchy

open MeasureTheory

namespace TZLevelsADO

/-!
# The randomly sampled Thorup–Zwick hierarchy

S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), §2 "The Thorup–Zwick hierarchy", p.7 (PDF p.8): "a vertex hierarchy
V = A₀ ⊇ A₁ ⊇ … ⊇ A_k = ∅, where, for every 0 ≤ i < k − 1, the set A_{i+1} contains each vertex of
A_i with probability n^{−1/k}. We also add one fixed vertex of A₀ to A₁, …, A_{k−1}, so that
A_{k−1} ≠ ∅."

**Formalization Note.**
* The coins are `ω : Fin k × Fin n → Bool`, one independent coin per (level, vertex), each `true` with
  probability `n^{−1/k}` (`coinLaw`). The coin `ω (i+1, v)` decides whether `v ∈ A_i` is kept in
  `A_{i+1}`, for `1 ≤ i + 1 ≤ k − 1`; the level-`0` coins are never read.
* `v₀` is the fixed vertex added to `A_1, …, A_{k−1}`; it lies in every `A_i` with `i < k`.
* `sampledA n k v₀ ω i = ∅` for `i ≥ k`.
* `sampledHierarchy` packages the sampled levels of a graph `G` as an admissible `Hierarchy G k`;
  the two lemmas before it are the structural facts this needs.
* For `n ≥ 1` the number `n^{−1/k}` lies in `[0, 1]`; `Set.projIcc` only fixes its type as a point of
  the unit interval and changes no value.
-/

/-- §2, p.7: the sampled levels `A_0 = V`, `A_{i+1} = {v ∈ A_i : ω(i+1, v)} ∪ {v₀}` for `i + 1 < k`,
and `A_i = ∅` for `i ≥ k`. -/
def sampledA (n k : ℕ) (v₀ : Fin n) (ω : Fin k × Fin n → Bool) : ℕ → Finset (Fin n)
  | 0 => Finset.univ
  | i + 1 =>
      if h : i + 1 < k then
        ((sampledA n k v₀ ω i).filter fun v => ω (⟨i + 1, h⟩, v) = true) ∪ {v₀}
      else ∅

/-- The sampling probability `n^{−1/k}`, as a point of the unit interval. -/
noncomputable def keepProb (n k : ℕ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one ((n : ℝ) ^ (-(1 : ℝ) / k))

/-- §2, p.7: the law of the coins: independent, each `true` with probability `n^{−1/k}`. -/
noncomputable def coinLaw (n k : ℕ) : Measure (Fin k × Fin n → Bool) :=
  Measure.pi fun _ : Fin k × Fin n => ProbabilityTheory.bernoulliMeasure true false (keepProb n k)

/-- The fixed vertex `v₀` lies in every sampled level `A_i` with `i < k`. -/
theorem v₀_mem_sampledA (n k : ℕ) (v₀ : Fin n) (ω : Fin k × Fin n → Bool) :
    ∀ i, i < k → v₀ ∈ sampledA n k v₀ ω i
  | 0, _ => by simp [sampledA]
  | i + 1, h => by simp [sampledA, h]

/-- The sampled levels are nested. -/
theorem sampledA_mono (n k : ℕ) (v₀ : Fin n) (ω : Fin k × Fin n → Bool) (i : ℕ) :
    sampledA n k v₀ ω (i + 1) ⊆ sampledA n k v₀ ω i := by
  by_cases h : i + 1 < k
  · simp only [sampledA, dif_pos h]
    refine Finset.union_subset (Finset.filter_subset _ _) ?_
    simpa using v₀_mem_sampledA n k v₀ ω i (by omega)
  · simp [sampledA, h]

/-- §2, p.7: the sampled hierarchy of the graph `G`, an admissible `Hierarchy G k`. -/
def sampledHierarchy (G : Graph) (k : ℕ) (hk : 0 < k) (v₀ : Fin G.n) (ω : Fin k × Fin G.n → Bool) :
    Hierarchy G k where
  A := sampledA G.n k v₀ ω
  pos := hk
  zero := rfl
  mono := sampledA_mono G.n k v₀ ω
  top_nonempty := ⟨v₀, v₀_mem_sampledA G.n k v₀ ω (k - 1) (by omega)⟩
  last := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp [sampledA]

end TZLevelsADO


