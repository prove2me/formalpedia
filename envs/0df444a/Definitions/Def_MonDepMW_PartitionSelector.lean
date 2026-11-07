-- Prove2me | Definitions.Def_MonDepMW_PartitionSelector
-- name    : MonDepMW_PartitionSelector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:49:29.585363+00:00
-- url     : https://prove2.me/theorems/7eb397be-c966-43ed-95d7-fc16b6821600
-- title:
--   Partition selectors: monotone, respectful, growth ratio (Definition 5.4)
-- statement:
--   A **partition selector** $\mathcal P(\cdot,\cdot)$ assigns to a graph $G$ and a set $A\subseteq V(G)$ a partition $\mathcal P(G,A)$ of $V(G)$. It is **monotone** if $\mathcal P(G,A)$ is a coarsening of $\mathcal P(G,B)$ whenever $A\subseteq B$, and **respectful** if $\mathcal P(G,A)$ is a refinement of $\mathcal T_1(G,A)$. Its **growth ratio** on $G$ is the least integer $\gamma$ with $|\mathcal P(G,A)|\leqslant\gamma|A|$ for every non-empty $A\subseteq V(G)$.
--
--   The selectors of interest are $\mathcal T_r$.
--
--   **Formalization Note** `GrowthLE` is "growth ratio at most $\gamma$", i.e. the inequality holds with $\gamma$.
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), §5.1, p.19, Definition 5.4

import Mathlib
import Definitions.Def_MonDepMW_rType

set_option autoImplicit false

namespace MonDepMW

/-- **Partition selectors.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), §5.1, p.19: "A partition selector is a function 𝒫(·, ·) that to a graph G and a set
of vertices A ⊆ V (G) assigns a partition 𝒫(G, A) of the vertex set of G." -/
abbrev PartitionSelector := ∀ n : ℕ, SimpleGraph (Fin n) → Finset (Fin n) → Setoid (Fin n)

/-- "We call a partition selector 𝒫 monotone if 𝒫(G, A) is a coarsening of 𝒫(G, B) whenever A ⊆ B." (p.19) -/
def PartitionSelector.Monotone (𝔓 : PartitionSelector) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)), A ⊆ B → 𝔓 n G B ≤ 𝔓 n G A

/-- "we call a partition selector 𝒫 respectful if for any graph G and A ⊆ V (G), 𝒫(G, A) is a refinement of 𝒯1(G, A)"
(p.19). -/
def PartitionSelector.Respectful (𝔓 : PartitionSelector) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), 𝔓 n G A ≤ oneType G A

/-- **Growth ratio at most `γ`.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), Definition 5.4, p.19: "The growth ratio of a partition selector 𝒫 on a graph G is
the least integer γ such that |𝒫(G, A)| ⩽ γ · |A| for every non-empty set A ⊆ V (G)." -/
def PartitionSelector.GrowthLE (𝔓 : PartitionSelector) {n : ℕ} (G : SimpleGraph (Fin n)) (γ : ℕ) : Prop :=
  ∀ A : Finset (Fin n), A.Nonempty → numParts (𝔓 n G A) ≤ γ * A.card

/-- The selector `𝒯_r` of `r`-types. -/
abbrev rTypeSelector (r : ℕ) : PartitionSelector := fun _ G A => rType G A r

end MonDepMW


