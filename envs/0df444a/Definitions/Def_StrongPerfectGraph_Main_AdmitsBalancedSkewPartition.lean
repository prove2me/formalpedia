-- Prove2me | Definitions.Def_StrongPerfectGraph_Main_AdmitsBalancedSkewPartition
-- name    : StrongPerfectGraph_Main_AdmitsBalancedSkewPartition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:22:14.308883+00:00
-- url     : https://prove2.me/theorems/0382adbf-1505-46ce-9217-393004ae195c
-- title:
--   Balanced skew partition
-- statement:
--   A **skew partition** of a graph $G$ is a partition $(A,B)$ of its vertices such that $G|A$ is disconnected and $\overline G|B$ is disconnected. It is **balanced** if (i) no odd induced path with nonadjacent ends in $B$ has all internal vertices in $A$, and (ii) no odd induced antipath with adjacent ends in $A$ has all internal vertices in $B$.
--
--   $$A\sqcup B=V(G),\quad G|A\text{ disconnected},\quad\overline G|B\text{ disconnected},\quad (A,B)\text{ balanced}.$$
--
--   A graph admits a balanced skew partition if such $A,B$ exist. The empty vertex set counts as connected, as the paper specifies. Lists orient paths and antipaths without changing their existence.
-- source:
--   Chudnovsky, Robertson, Seymour & Thomas, The strong perfect graph theorem, Ann. of Math. 164 (2006), p. 53–54, §1, definitions of path, balanced pair, connected set, and skew partition

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsInducedPath

namespace StrongPerfectGraph.Main

/-- Connectedness of an induced vertex set; the empty set is connected. -/
def IsConnectedSet {V : Type*} (G : SimpleGraph V) (X : Set V) : Prop :=
  ∀ u (hu : u ∈ X) v (hv : v ∈ X),
    (G.induce X).Reachable ⟨u, hu⟩ ⟨v, hv⟩

/-- The paper's balanced-pair condition, with both paths induced. -/
def IsBalanced {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  (∀ (p : List V) (u v : V),
      IsInducedPath G p → Odd (p.length - 1) →
      p.head? = some u → p.getLast? = some v →
      u ∈ B → v ∈ B → ¬ G.Adj u v →
      (∀ w ∈ p, w ≠ u → w ≠ v → w ∈ A) → False) ∧
  (∀ (p : List V) (u v : V),
      IsInducedPath Gᶜ p → Odd (p.length - 1) →
      p.head? = some u → p.getLast? = some v →
      u ∈ A → v ∈ A → G.Adj u v →
      (∀ w ∈ p, w ≠ u → w ≠ v → w ∈ B) → False)

/-- A skew partition has a disconnected first side and an anticonnected second side. -/
def IsSkewPartition {V : Type*} (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ A ∪ B = Set.univ ∧
    ¬ IsConnectedSet G A ∧ ¬ IsConnectedSet Gᶜ B

/-- Existence of a skew partition satisfying both parity restrictions. -/
def AdmitsBalancedSkewPartition {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ A B : Set V, IsSkewPartition G A B ∧ IsBalanced G A B

end StrongPerfectGraph.Main


