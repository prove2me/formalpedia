-- Prove2me | Definitions.Def_CausalFailureRank_Supplement_safetyTable
-- name    : CausalFailureRank_Supplement_safetyTable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T02:51:15.0392+00:00
-- url     : https://prove2.me/theorems/893fd2f1-615c-475e-8d3d-b2d691a59faf
-- title:
--   Common augmented-tree safety-table interface
-- statement:
--   For a known-order tool-allocation game, the **augmented laminar tree** consists of the distinct nonempty compatibility sets, the full tool set $U$, and every singleton tool set. A normalized capacity vector $b$ on this tree represents
--
--   $$
--   \mathcal I(b)=\{D\subseteq U: |D\cap T|\le b_T\text{ for every tree node }T\}.
--   $$
--
--   Singleton capacities are $0$ or $1$, and each internal capacity is no larger than the sum of its children. The separate value `VOID` denotes the empty family and is not the all-zero vector, which represents $\{\emptyset\}$.
--
--   A safety table contains one representation for every suffix and error budget, exact rank and maximizing-tool query functions, and elementary operation and storage counters. Its correctness predicate requires membership to agree both with the causal `Handles` game and with $\rho(i,U\setminus D)>k$, recovers every rank, and returns an actual compatible tool attaining the best bad-child rank.
--
--   **Formalization Note** Stages and suffixes are 0-based. `Option.none` is `VOID`; `Option.some b` is $\mathcal I(b)$. Capacities are natural numbers, so their nonnegativity is built into the type. The underlying causal rank is the published base definition.
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), §3.2, pp.7–8 (PDF pp.8–9), definitions preceding Theorem 3.2

import Mathlib
import Definitions.Def_CausalFailureRank_rank

set_option autoImplicit false

namespace CausalFailureRank
namespace Supplement

/-- The compatibility sets form a laminar family: two nonempty stage sets are disjoint or nested.
Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027
submission, version of 2026-11-03, sha256 721c8b0d…), §3.2, pp.7–8. -/
def IsLaminar {N q : ℕ} (S : Fin N → Finset (Fin q)) : Prop :=
  ∀ i j, (S i).Nonempty → (S j).Nonempty →
    Disjoint (S i) (S j) ∨ S i ⊆ S j ∨ S j ⊆ S i

/-- The single augmented family `L`: the distinct nonempty compatibility sets, the root `U`, and
all singleton tool sets. Empty compatibility sets are deliberately absent. -/
def augmentedNodes {N q : ℕ} (S : Fin N → Finset (Fin q)) : Finset (Finset (Fin q)) :=
  insert Finset.univ
    ((Finset.univ.image fun r : Fin q ↦ {r}) ∪
      ((Finset.univ.image S).filter Finset.Nonempty))

/-- `C` is an immediate child of `T` in the inclusion tree carried by `L`. -/
def IsTreeChild {q : ℕ} (L : Finset (Finset (Fin q))) (C T : Finset (Fin q)) : Prop :=
  C ∈ L ∧ T ∈ L ∧ C ⊆ T ∧ C ≠ T ∧
    ∀ W ∈ L, C ⊆ W → W ⊆ T → W = C ∨ W = T

/-- The immediate children of a node in the inclusion tree. -/
noncomputable def treeChildren {q : ℕ} (L : Finset (Finset (Fin q))) (T : Finset (Fin q)) :
    Finset (Finset (Fin q)) := by
  classical
  exact L.filter fun C ↦ IsTreeChild L C T

/-- A capacity vector on `L` is normalized when singleton capacities are at most one and every
non-singleton capacity is at most the sum of the capacities of its children. Capacities are
natural numbers, so nonnegativity is built into their type. -/
def IsNormalizedCapacity {q : ℕ} (L : Finset (Finset (Fin q)))
    (b : Finset (Fin q) → ℕ) : Prop :=
  (∀ T ∈ L, (∃ r, T = {r}) → b T ≤ 1) ∧
    ∀ T ∈ L, (∀ r, T ≠ {r}) → b T ≤ ∑ C ∈ treeChildren L T, b C

/-- The capacity family `I(b) = {D : |D ∩ T| ≤ b_T for every T in L}`. -/
def capacityFamily {q : ℕ} (L : Finset (Finset (Fin q)))
    (b : Finset (Fin q) → ℕ) : Set (Finset (Fin q)) :=
  {D | ∀ T ∈ L, (D ∩ T).card ≤ b T}

/-- `none` is the paper's `VOID`; `some b` is `I(b)`. Thus `VOID` is definitionally distinct
from the all-zero vector, whose family contains the empty used-tool set. -/
def representedFamily {q : ℕ} (L : Finset (Finset (Fin q)))
    (rep : Option (Finset (Fin q) → ℕ)) : Set (Finset (Fin q)) :=
  match rep with
  | none => ∅
  | some b => capacityFamily L b

/-- The finite common-tree table promised by Theorem 3.2. Stages are 0-based, so `Fin (N+1)`
represents the paper's suffixes `1,…,N+1`; `Fin (q+2)` represents budgets `0,…,q+1`.

The operation counters are elementary integer/set-membership work units for the concrete table
construction and queries. The theorem bounds them uniformly; they are included in the output
interface rather than being inferred from the extensional functions. -/
structure SafetyTable {N q : ℕ} (S : Fin N → Finset (Fin q)) where
  tree : Finset (Finset (Fin q))
  entry : Fin (N + 1) → Fin (q + 2) → Option (Finset (Fin q) → ℕ)
  rankQuery : Fin (N + 1) → Finset (Fin q) → ℕ∞
  maximizingTool : Fin N → Finset (Fin q) → Option (Fin q)
  preprocessOps : ℕ
  storageBits : ℕ
  rankQueryOps : Fin (N + 1) → Finset (Fin q) → ℕ
  toolQueryOps : Fin N → Finset (Fin q) → ℕ
  treeConstructionOps : ℕ

/-- Extensional correctness of the common-tree table, including exact game meaning, rank recovery,
an actual maximizing compatible tool, normalized capacities, and the range `[0,q]`. -/
def SafetyTable.Correct {N q : ℕ} {S : Fin N → Finset (Fin q)}
    (T : SafetyTable S) : Prop :=
  T.tree = augmentedNodes S ∧
  (∀ i k b, T.entry i k = some b →
    IsNormalizedCapacity T.tree b ∧ ∀ A ∈ T.tree, b A ≤ q) ∧
  (∀ i k D,
    D ∈ representedFamily T.tree (T.entry i k) ↔ Handles S i.val (Finset.univ \ D) k.val) ∧
  (∀ i k D,
    D ∈ representedFamily T.tree (T.entry i k) ↔
      (k.val : ℕ∞) < gameRank S i.val (Finset.univ \ D)) ∧
  (∀ i R, T.rankQuery i R = gameRank S i.val R) ∧
  (∀ i R, (S i ∩ R).Nonempty →
    ∃ r, T.maximizingTool i R = some r ∧ r ∈ S i ∧ r ∈ R ∧
      gameRank S (i.val + 1) (R.erase r) = gameBadRank S i R) ∧
  T.preprocessOps = (N + 1) * (q + 2) * T.tree.card ∧
  T.storageBits = (N + 1) * (q + 2) * T.tree.card * (Nat.log2 (q + 1) + 1) ∧
  (∀ i R, T.rankQueryOps i R = (q + 2) * T.tree.card) ∧
  (∀ i R, T.toolQueryOps i R = (q + 2) * T.tree.card) ∧
  T.treeConstructionOps = (N + q + 1) ^ 2 * q

/-- Upload-module interface for the common-tree safety representation. -/
abbrev safetyTable {N q : ℕ} (S : Fin N → Finset (Fin q)) := SafetyTable S

end Supplement
end CausalFailureRank


