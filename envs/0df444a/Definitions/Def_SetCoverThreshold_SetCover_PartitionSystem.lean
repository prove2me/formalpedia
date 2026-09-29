-- Prove2me | Definitions.Def_SetCoverThreshold_SetCover_PartitionSystem
-- name    : SetCoverThreshold_SetCover_PartitionSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:53:36.24573+00:00
-- url     : https://prove2.me/theorems/d7d47462-8518-44d7-9d7d-af22120c9d93
-- title:
--   Partition systems $B(m,L,k,d)$ (Definition 3.1) and the Naor–Schulman–Srinivasan construction as a hypothesis
-- statement:
--   **Definition 3.1** (pp. 643–644). "A partition system B(m, L, k, d) has the following properties.
--   (1) There is a ground set B of m points.
--   (2) There is a collection of L distinct partitions p_1, . . . , p_L.
--   (3) For 1 ≤ i ≤ L, partition p_i is a collection of k disjoint subsets of B whose union is B.
--   (4) Any cover of the m points by subsets that appear in pairwise different partitions requires at least d subsets."
--
--   Here the ground set is $\{0,\dots,m-1\}$, and a partition system is a labelling $\mathrm{part}(b,j)\in\{0,\dots,k-1\}$: point $b$ lies in subset $\mathrm{part}(b,j)$ of partition $j$. Property (3) holds by construction. Property (2) says two different partitions never group the points into the same blocks. Property (4) says: if a family of pairs (partition $j$, subset $i$), no two with the same partition, covers every point, then it has at least $d$ members.
--
--   **The deterministic construction (hypothesis).** The paper states (p. 644): "The randomized construction can be replaced by a deterministic construction using techniques developed in Naor et al. [1995]. There, partition systems are called anti-universal sets. Theorem 9 in Naor et al. [1995] says that for any k one can in time linear in m construct a partition system for which m = (k/(k−1))^d d^{O(log d)} log L. (Here k is assumed to be an arbitrary constant, and m grows as a function of L and d.) Expressing the ratio d/k as a function of m one gets (1 − f(k)) ln m, where f(k) → 0 as k → ∞, provided that d is sufficiently large as a function of k, and L is bounded by a polynomial in d." The proposition `NaorPartitionSystems` records this as follows: for every $\eta>0$ there is $k_0$ such that for every $k\ge k_0$ and every exponent $a$ there are $m_0$ and a polynomial-time computable map which, given $m\ge m_0$ and $L\le\lfloor\log_2 m\rfloor^a$ in unary, outputs (as a table) a partition system $B(m',L,k,d)$ with $m'\ge m$ and
--
--   $$d\ \ge\ (1-\eta)\,k\,\ln m'.$$
--
--   Partition systems are the gadget of the reduction in Section 4.
--
--   **Formalization Note** "Time linear in m" is relaxed to polynomial time and "L bounded by a polynomial in d" is rendered as $L\le\lfloor\log_2 m\rfloor^a$; both relaxations make the assumed proposition weaker. The table of $B(m',L,k,d)$ lists, for each point, the subset index in every partition; it is written over the alphabet $\{0,\dots,k-1\}\cup\{\text{separator}\}$.
-- source:
--   Feige, A threshold of ln n for approximating set cover, J. ACM 45(4) (1998), pp. 643–644, Definition 3.1; p. 644, paragraph after the proof of Lemma 3.2 (Naor et al. 1995, Theorem 9)

import Mathlib
import Definitions.Def_CookPvsNP_defs

namespace SetCoverThreshold.SetCover

/-- A partition system `B(m, L, k, d)` (Feige 1998, Definition 3.1, pp. 643–644), on the ground
set `Fin m` with partitions indexed by `Fin L`. Point `b` lies in subset `part b j` of partition
`j`, so every partition is a collection of `k` disjoint subsets whose union is the ground set.
* `distinct`: the `L` partitions are distinct (two different indices never induce the same
  partition of the ground set into blocks);
* `cover_bound`: any cover of the `m` points by subsets (pairs `(j, i)` = subset `i` of
  partition `j`) that appear in pairwise different partitions has at least `d` members. -/
structure PartitionSystem (m L k d : ℕ) where
  part : Fin m → Fin L → Fin k
  distinct : ∀ j j' : Fin L, j ≠ j' →
    ¬ ∀ b b' : Fin m, (part b j = part b' j ↔ part b j' = part b' j')
  cover_bound : ∀ F : Finset (Fin L × Fin k),
    (∀ x ∈ F, ∀ y ∈ F, x.1 = y.1 → x = y) →
    (∀ b : Fin m, ∃ x ∈ F, part b x.1 = x.2) → d ≤ F.card

namespace PartitionSystem

variable {m L k d : ℕ}

/-- The table of a partition system: row `b` lists, for each partition `j`, the index of the
subset containing point `b`. -/
def table (P : PartitionSystem m L k d) : List (List (Fin k)) :=
  List.ofFn fun b : Fin m => List.ofFn fun j : Fin L => P.part b j

end PartitionSystem

/-- String encoding of a table over the alphabet `Option (Fin k)`: each row is written symbol by
symbol and terminated by the separator `none`. -/
def encodeTable {k : ℕ} (T : List (List (Fin k))) : List (Option (Fin k)) :=
  T.flatMap fun row => row.map some ++ [none]

/-- Unary encoding of a pair `(m, L)`: `1^m 0 1^L`. -/
def unaryPair (m L : ℕ) : List Bool :=
  List.replicate m true ++ false :: List.replicate L true

/-- The deterministic construction of partition systems of Naor, Schulman and Srinivasan (1995,
Theorem 9), in the form Feige 1998 uses it (p. 644), taken as a hypothesis: for every `η > 0`
there is `k₀` such that for every `k ≥ k₀` and every exponent `a` there are `m₀` and a
polynomial-time computable map which, on input `(m, L)` in unary with `m ≥ m₀` and
`L ≤ (⌊log₂ m⌋)^a`, outputs the table of a partition system `B(m', L, k, d)` with `m ≤ m'` and
`d ≥ (1 - η) k ln m'`. -/
def NaorPartitionSystems : Prop :=
  ∀ η : ℝ, 0 < η → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ a : ℕ, ∃ m₀ : ℕ,
    ∃ F : List Bool → List (Option (Fin k)), CookPvsNP.PolyTimeComputable F ∧
      ∀ m L : ℕ, m₀ ≤ m → L ≤ (Nat.log 2 m) ^ a →
        ∃ (m' d : ℕ) (P : PartitionSystem m' L k d),
          m ≤ m' ∧ F (unaryPair m L) = encodeTable P.table ∧
            (1 - η) * k * Real.log m' ≤ d

end SetCoverThreshold.SetCover


